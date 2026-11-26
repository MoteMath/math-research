import Lib.General.LinearAlgebra.HaarUnique
import Lib.General.Algebra.ZerosCostDegree
import Lib.LocalGL.Green.CuspidalAtScalars
import New.Core.ModuleIndex
section FoldSeg0
open Fin Finset Set ENNReal Equiv Fintype LinearMap Matrix MeasureTheory Tuple
variable {k m : ℕ} {T : Type} [Add T] [One T] (v : T → Bool) (P : ℝ) (k' : ℕ)
@[simps!] def permStep (σ : T → Perm (Fin k)) : Module.End ℝ (Fin k × T → ℝ) := .pi fun x ↦
  ite (v x.2) (1 : ℝ) (-1) • (P • .proj (x.1, x.2 + 1) - .proj (σ x.2 x.1, x.2))
def slab (D : T → ℝ) := {β : Fin k' × T → ℝ | 0 ≤ β ∧ ∀ j, ∑ b, β (b, j) ∈ Icc (D j - 1) (D j)}
def pieriCone := {ν | ∀ j (b b' : Fin k), b.1 + 1 = b' → permStep v P 1 ν (ite (v j) b' b, j) ≤
  ν (b, j) - ν (b', j)}
lemma det_interlacing_indicator {x y : Fin k → ℝ} (hx : Antitone x) (hy : Antitone y) :
  det (of fun b c ↦ ite
  (y c < x b) (1 : ℝ) 0) = ite ((∀ b, y b < x b) ∧ ∀ b c, b.1 + 1 = c.1 → x c ≤ y b) 1 0 := by
  induction' k with k ih
  · simp
  obtain ⟨b, h⟩ | h := exists_or_forall_not fun b ↦ y 0 < x (succ b)
  · rw [det_zero_of_row_eq b.succ_ne_zero] <;> [grind [hy b.castSucc.zero_le]; ext c]
    grind [of_apply, hy c.zero_le, hx b.succ.zero_le]
  simp [det_succ_column_zero', sum_univ_succ, forall_fin_succ, h]
  erw [ih] <;> grind [Antitone]
omit [Add T] [One T] in
lemma isBounded_inter_slab [Fintype T] (D : T → ℝ) Y :
    Bornology.IsBounded (Y ∩ slab k D) := (Metric.isBounded_Icc ..).subset fun _ ⟨_, h, g⟩ ↦
    ⟨h, fun x ↦ (single_le_sum (fun b _ ↦ h (b, _)) (by simp)).trans (g _).2⟩
lemma volume_inter_slab_eq_signed_sum {v : Fin (m + 1) → _} (hP : 1 < P) D {Ω : Set _} (hΩ : ∀ ν,
  permStep v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P) : let Δ τ := |(1 - (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ τ).det|
  volume.real (Ω ∩ slab k D) =
          Δ id / k.factorial * (∑ τ : Perm (Fin k), τ.sign / Δ τ) * volume.real (slab k D) := by
  let S σ (τ : _ → Perm (Fin k)) (Y : Set _) := {ν | let β := permStep v P σ (ν ∘ prodCongrLeft τ)
    (∀ j, ∑ b, permStep v P 1 ν (b, j) ∈ Icc (D j - 1) (D j)) ∧ (∀ j b, 0 < β (b, j)) ∧ β ∈ Y}
  have z σ : (@permStep k _ _ _ v P σ).det ≠ 0 := (bot_lt_ker_of_det_eq_zero · |>.not_ge fun ν h ↦
    norm_le_zero_iff.1 (by nlinarith [(funext fun x ↦ by simpa [ite_eq_iff'] using (mul_eq_zero.1
    congr($h (_, _ - 1))) : P • ν = ν ∘ _) ▸ pi_norm_comp_le .., norm_smul P ν, P.le_norm_self]))
  have V σ τ Y : volume (S σ τ Y) = .ofReal |(permStep v P σ * (Perm.permMatrix ℝ
    (prodCongrLeft τ)).toLin').det⁻¹| * volume (Y ∩ slab k D) := by
    erw [← measure_inter_conull (ae_all_iff.2 (Measure.ae_eval_ne _ · 0)) (s := Y ∩ _), ←
      Measure.addHaar_preimage_linearMap _ (by simp [z])]
    congr with ν
    simp [S, slab, -Perm.coe_one, ← mul_sum, ← Perm.mul_apply, Pi.le_def, -Perm.coe_mul,
      fun e j ↦ Equiv.sum_comp e (ν ⟨·, j⟩), permMatrix_mulVec, ↓permStep_apply]
    grind
  let B : (_ → ℝ) →ₗ[ℝ] Fin k × Fin m.succ → ℝ := LinearMap.pi fun x ↦ P⁻¹ ^ x.2.1.succ • proj x.1
  have ⟨c, hc⟩ : ∃ c, ∀ σ, (@permStep k _ _ _ v P σ).det = c * (1 - (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ
      (List.ofFn σ).prod).det := ⟨_, fun σ ↦ by
    let G := (Perm.permMatrix ℝ (prodCongrLeft (partialProd σ ∘ castSucc))).toLin'
    let A := funLeft ℝ ℝ ((last _).partialProd σ ·, last m)
    rw [show _ • _ = A ∘ₗ B by ext; simp +zetaDelta [partialProd, List.take_of_length_le]]
    simpa [← det_toMatrix' (_ - _), toMatrix'_comp, det_one_sub_mul_comm B.toMatrix', field, G]
      using congr(($(show permStep v P σ * G = (permStep v 1 1 - permStep v 0 1) * G * (P • 1 -
      .pi fun x ↦ x.2.cases 0 (proj ⟨x.1, ·.castSucc⟩)) * (1 - B ∘ₗ A) by
      ext x ⟨b, j⟩
      cases j using lastCases <;>
      simp +zetaDelta [← succ_last, partialProd_succ, permMatrix_mulVec] <;> grind)).det)⟩
  have e ν : ∑ τ, (S 1 τ Ω).indicator (fun _ ↦ 1) ν =
      ∑ σ, (S σ 1 univ).indicator (fun _ ↦ ((List.ofFn σ).prod.sign : ℝ)) ν := ?_
  · simpa [↓integral_finsetSum, integrable_indicator_iff, fun σ ↦
      (by simp [S, hΩ, pieriCone, -permStep_apply]; use ?_ <;> fun_prop :
      MeasurableSet (S σ 1 univ) ∧ MeasurableSet (S 1 σ Ω)), ↓(V ..).trans_lt (mul_lt_top coe_lt_top
      (isBounded_inter_slab ..).measure_lt_top), -enorm_mul, Measure.real, hc, field, card_perm,
      ↓← ((prodCongrLeft fun g : Fin m → _ ↦ .mulRight (List.ofFn g).prod⁻¹).trans
        (consEquiv fun _ ↦ Perm
      (Fin k))).sum_comp, sum_prod_type_right, ← sum_mul, div_eq_inv_mul, abs_unit_intCast, V, by
      simpa [hc] using z 1, mul_right_comm _ _ (Int.cast _), Nat.cast_comm] using congr(∫ ν, $(e ν))
  let τ j := sort (-ν ⟨·, j⟩)
  have anti j := (monotone_sort (-ν ⟨·, j⟩)).neg
  simp_rw [indicator, S, hΩ, pieriCone, mem_ofPred, ite_and (∀ j, _ ∈ _), sum_ite_irrel,
    ← forall_and]
  rw [sum_eq_single τ fun σ ne ↦ ite_eq_right fun h ↦ ne (funext fun j ↦ eq_sort_iff'.2
    ((strictMono_iff_forall_covBy _).2 fun _ _ e ↦ .left _ _ (by
    simpa using (h ..).1.trans_le ((h ..).2 _ e.coe_fin.succ_eq)))), eq_comm]
  congr
  trans ∏ j, ((of fun b' b : Fin k ↦ ite (0 < permStep v P (fun _ ↦ .swap b b') ν (b, j)) 1
    0).reindex (τ j).symm (τ (j + 1)).symm).det
  · simp [↓det_reindex, ← Int.cast_prod, ← Units.coe_prod, det_apply', map_list_prod,
      prod_ofFn, -List.ofFn_succ, (AddGroup.addRight_bijective 1).prod_comp (Perm.sign <| τ ·),
      prod_univ_sum, Fintype.prod_ite_zero, -Units.val_mul]
  convert Fintype.prod_boole with j
  have a := (anti (j + 1)).const_mul (by bound : 0 ≤ P)
  by_cases v j <;> [convert (det_transpose _).trans (det_interlacing_indicator a (anti j)); convert
    det_interlacing_indicator (anti j) a using 2] <;> simp [← ext_iff, τ, *, forall_and, sub_add]
  infer_instance
lemma prod_mul_volume_inter_slab {N} [NeZero N] {v P} (hP : 1 < P) (D : ZMod N → ℝ) {Ω} (hΩ : ∀ ν,
  permStep v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P) : (∏ l : Fin k, ((P ^ N) ^ (l.1 + 1) - 1) /
  (P ^ N - 1)) * volume.real (Ω ∩ slab k D) = volume.real (slab k D) := by
  have q := one_lt_pow₀ hP (NeZero.ne N)
  cases N; bound
  erw [volume_inter_slab_eq_signed_sum P hP D hΩ]
  set P := P ^ _
  let d i := (P ^ (i + 1) - 1) / (P - 1)
  let p c : (Fin k × Fin 1 → ℝ) →ₗ[ℝ] ℝ := if h : c < k then .proj (⟨c, h⟩, 0) else 0
  let F : Module.End ℝ _ := LinearMap.pi fun x ↦ d x.1 • (p x.1 - P • p (x.1 + 1))
  have det : F.det = ∏ b : Fin k, d b := by
    rw [← det_toMatrix', ← det_reindex_self (prodUnique ..), det_of_isUpperTriangular]
      <;> simp [Fin.ext_iff, F, p, DFunLike.dite_apply, BlockTriangular]; lia
  have deg β : ∑ b, F β (b, 0) = ∑ b, β (b, 0) := sub_eq_zero.1 (by convert (sum_range_sub' (fun c ↦
    (d c - 1) * p c β) k) <;> simp [sum_range, F, p, ↓← sum_sub_distrib, -smul_dite] <;> grind)
  have D0 : 0 < F.det := by simp [prod_pos, d, one_lt_pow₀, *]
  have := @volume_inter_slab_eq_signed_sum k 0 P ⊤ q 1 (pieriCone ⊤ P) (by simp [pieriCone, field])
  erw [@Set.ext _ (_ ∩ _) (F ⁻¹' slab k 1), Measure.real, volume.addHaar_preimage_linearMap D0.ne',
    toReal_mul, mul_left_inj' (toReal_pos (mt (measure_mono_null (s := .Icc 0 (↑k)⁻¹) fun β ⟨h, g⟩ ↦
    ⟨h, by simp; grw [← h _, g _]; simp [mul_inv_le_one]⟩) (by simp [Real.volume_Icc_pi]))
    (Set.univ_inter _ ▸ isBounded_inter_slab ..).measure_lt_top.ne).ne', pow_one] at this
  simp [↓← this, ← det, abs_of_nonneg, D0.le, field, d]; rfl
  simp [slab, deg, ← and_assoc, pieriCone, Pi.le_def]
  simpa [F, p, DFunLike.dite_apply, d, one_lt_pow₀, *] using fun β _ _ ↦ ⟨by bound, fun h ↦
    ⟨by grind, WellFoundedGT.fix fun b I ↦ (h b).trans' (by grind [mul_nonneg])⟩⟩
end FoldSeg0
noncomputable section
open Fintype Finset MvPolynomial Matrix IsLocalRing Ideal
variable (k N) (W R R' : Type) [CommRing W] [IsLocalRing W] [CommRing R] [CommRing R']
  (φ : R →+* R')
attribute [local simp ←] prod_pow_eq_pow_sum add_assoc coeff_map Quotient.eq_zero_iff_dvd
attribute [local simp] polyOfCoeffs exponentOf Finsupp.weight_eq_sum prod_prod_type_right
  Fintype.prod_ite_zero prod_univ_sum sum_prod_type_right diagonal_apply linSubst_mul map_bind₁
  AlgHom.ext_iff smul_eq_C_mul
def twoBlock r (b : Fin k) := ite (b.1 < r) 0 1
structure TwistingData where
  (p o₀ : ℕ) ι : ZMod N → W →+* R
  isEven : ZMod N → _
  w : R
  prime : p.Prime
  five_le_P : 5 ≤ p ^ o₀
  w_sq : w ^ 2 = p
  frobenius_congr s x : ↑p ∣ ι (s + 1) x - ι s x ^ p ^ o₀
  isEven_succ s : isEven (s + 1) = !isEven s
  card_residueField : .card (ResidueField W) = (p ^ o₀) ^ N
namespace TwistingData
variable {k N W R R'} [NeZero N] (T : TwistingData N W R) (n r : ℕ) (i) (a a' :
  Fin k) {τ} (g : GL (Fin k) W) (s : ZMod N) (x : Fin k × _)
abbrev P := T.p ^ T.o₀
abbrev q := T.P ^ N
def map := {T with
  ι := φ.comp ∘ T.ι, w := φ T.w, w_sq := by simp [← map_pow, w_sq]
  frobenius_congr := by simpa using (map_dvd φ <| T.frobenius_congr · ·)}
@[simps -isSimp] def letterMatrix := MonoidHom.mk ⟨fun g : GL (Fin k) W ↦
  (ite (T.isEven s) ↑g g⁻¹.1ᵀ).map (T.ι s), by simp⟩ (by bound)
def polyAction := MonoidHom.mk ⟨fun g ↦ linSubst (blockDiagonal (T.letterMatrix (k := k) · g)),
  by simp [← Pi.one_def]⟩ (by simp)
@[simps -isSimp] def letterRep := MonoidHom.mk ⟨fun g ↦
  kroneckerPi (symPowMatrix n <| T.letterMatrix (k := k) · g), by simp⟩ (by simp [kroneckerPi_mul])
def deepIndicator := if T.isEven x.2 ↔ r ≤ x.1 then 1 else 0
def depth k n r β := (exponentOf (a := n) β).weight (T.deepIndicator (k := k) r)
@[simps] def rootVar := (ite (T.isEven s) a' a, s)
def excessWeight := (ite (x = T.rootVar a a' x.2) (T.P ^ (1 + (x.2 - 1 - i).val)) 0 -
  ite (x = T.rootVar a' a x.2) (T.P ^ (x.2 - i).val) 0 : ℝ) / T.q
def translatesIn τ (I : Ideal R) (B : Set _) := (⟨⟨⟨{F | ∀ g ∈ @levi k W _ τ, ∀ β ∈ B,
  (T.letterRep n g *ᵥ F) β ∈ I}, by aesop⟩, by simp⟩, by simp_all [mul_mem_left]⟩ : Submodule R _)
abbrev excessCond I h :=
  T.translatesIn n (twoBlock k a') I {β | ∃ i, h < (exponentOf β).weight (T.excessWeight i a a')}
abbrev deepForms k n r d := T.translatesIn n 0 ⊥ {β | T.depth k n r β < d}
attribute [local simp] symPowMatrix linSubst polyAction kroneckerPi letterRep pow_mul' excessWeight
  depth blockDiagonal mulVec_eq_sum
attribute [local grind!] TwistingData le_self_pow NeZero
omit [NeZero N] in
lemma one_lt_P : (1 : ℝ) < T.P := mod_cast by lia
lemma one_lt_q : (1 : ℝ) < T.q := mod_cast by grind
omit [NeZero N] in
lemma frobenius_pow_congr x : ↑T.p ∣ T.ι (s + n) x - T.ι s x ^ T.P ^ n := have := T.frobenius_congr
             by induction n <;> simp_all [pow_succ']
variable {n r i a a' g x}
omit [NeZero N] in
lemma w_ne_zero [CharZero R] : T.w ≠ 0 := by grind [Nat.cast_inj, T.prime.pos]
omit [NeZero N] in
include T in lemma finite_residueField : Finite (ResidueField W) := by grind [Nat.card_pos_iff]
lemma p_dvd_letterMatrix_of_mem_parahoric (hg : g ∈ parahoric W τ) i j (h : ite (T.isEven s)
  (τ i < τ j) (τ j < τ i)) : ↑T.p ∣ T.letterMatrix s g i j := ((isUnit_one_sub_self_of_mem_nonunits
  _ (pow_mem_of_mem _ ((residue_eq_zero_iff (ite (T.isEven s) _ g⁻¹.1ᵀ i j)).1 (by
  split_ifs at * <;> apply_rules [inv_mem hg])) (T.q - 1) (by grind))).map (T.ι s)).dvd_mul_right.1
  (by simpa [letterMatrix, mul_sub, mul_pow_sub_one, T.prime.ne_zero] using
  T.frobenius_pow_congr N ..)
lemma polyAction_X : T.polyAction g (X x) = ∑ b,
  C (T.letterMatrix x.2 g b x.1) * X (b, x.2) := by simp
lemma diagonal_pow_depth (x : R) : diagonal (x ^ T.depth k n r ·) = kroneckerPi fun s ↦
  symPowMatrix n (diagonal (n := Fin k) (x ^ T.deepIndicator r ⟨·, s⟩)) := by ext; simp [apply_ite,
  -aeval_eq_bind₁, aeval_monomial, C_mul_X_eq_monomial, monomial_pow, ← monomial_sum_prod]; grind
lemma polyAction_polyOfCoeffs F : T.polyAction g (polyOfCoeffs F) =
  polyOfCoeffs (T.letterRep n g *ᵥ F) := by
  simpa [monomial_eq, coeff_map, -univ_eq_attach] using congr(∑ α, F α • ∏ s, rename (·, s)
    $(sum_monomials_eq_of_isHomogeneous ((α s).isHomogeneous_linSubst (T.letterMatrix s g)))).symm
lemma letterRep_map : (T.map φ).letterRep n g = (T.letterRep n g).map φ := by aesop
@[simp] lemma one_add_val_sub_one_sub : 1 + (s - 1 - i).val = ite (s = i) N (s - i).val := by
  zify; simp [sub_right_comm, ZMod.cast_sub_one]
lemma five_mul_P_pow_le_q : 5 * T.P ^ s.val ≤
  T.q := by grw [T.five_le_P, ← pow_succ', q]; gcongr <;> grind
lemma excessWeight_mem_Icc : T.excessWeight i a a' x ∈ Set.Icc (-5⁻¹) 1 :=
  (unitInterval.div_mem (by simp) (by simp)
  (Nat.mono_cast (T.five_mul_P_pow_le_q (x.2 - i)))).elim (by simp [sub_div, ite_div]; grind)
end TwistingData
end
section FoldSeg2
open Finset Finsupp Fintype Ideal MatMul Matrix MvPolynomial
variable {N k W K} [NeZero N] [CommRing W] [IsLocalRing W] [Field K] (T : TwistingData N W K)
lemma TwistingData.sum_deepIndicator r (b : Fin k) : ∑ s, T.deepIndicator r (b, s) = N / 2 :=
  Nat.eq_div_of_mul_eq_right
  nofun (by nth_rw 1 [two_mul, ← sum_translate (-1), ← sum_add_distrib, sum_const_nat,
  mul_one] <;> simp; grind [deepIndicator, isEven_succ])
lemma TwistingData.exists_le_weight_of_mem_deepForms [CharP K T.p] {n r τ F} (hk : 2 * r ≤
  k) (hN : 2 * r < N) (hF : F ∈ T.deepForms k n r τ) (F0 : F ≠ 0) : ∃ β, F β ≠ 0 ∧ τ ≤
  (exponentOf β).weight fun x ↦ (T.deepIndicator r x / T.P ^ ite (2 * r ≤ x.1) (2 * r) 1 : ℝ) := by
  choose J hJ using fun i b ↦ show ∃ j : ℕ, j / 2 = b ∧ T.isEven (i - j) by by_contra! h; grind
    [T.isEven_succ (i - 2 * b - 1), sub_add_cancel, sub_sub, h (2 * b), h (2 * b + 1)]
  obtain ⟨p, _, _, m, e⟩ := T.prime.pos, @ofFinite _ T.finite_residueField, Fact.mk T.prime, hk.dest
  let R := MvPolynomial (Fin k × ZMod N) K
  let x := algebraMap R (FractionRing R)
  let κ v := T.P ^ (T.deepIndicator (k := k) r v * ite (2 * r ≤ v.1) (2 * r) 1)
  let I := Fin r ×ₗ Fin (m + 1)
  let ρ (t : I) : Fin k := ⟨t.1, by lia⟩
  let σ (t : I) : Fin k := ⟨ite (t.2 = 0) (t.1 + r) (k - t.2), by lia⟩
  let c v t : R := ite (T.rootVar (ρ t) (σ t) v.2 =
    v) (X (T.rootVar (σ t) (ρ t) v.2)) 0 * ite (T.isEven v.2) 1 (-1)
  let a i (y : I → IsLocalRing.ResidueField W) t := x (C (T.ι i (y t).out))
  let z y v := a v.2 y ⬝ᵥ x ∘ c v
  have hz v (j : ℕ) y : x ∘ c v ^ T.P ^ j ⬝ᵥ a (v.2 + j) y = z y v ^ T.P ^ j := by
    erw [dotProduct_comm, ← pow_mul, sum_pow_char_pow]; simp [a, dotProduct, pow_mul, mul_pow,
      by simpa [CharP.cast_eq_zero] using T.frobenius_pow_congr j v.2]
  have entry i u : ∃ g, (∀ α ∈ g.support, weight (κ · : _ → ℝ)⁻¹ α < 1) ∧
      ∀ y, eval (z y) g = u ⬝ᵥ a i y := by
    let j (t : I) := ite (t.2 = 0) 0 (J i t.1)
    let v t := T.rootVar (ρ t) (σ t) (i - j t)
    obtain ⟨w, rfl⟩ := (x.mapMatrix (of fun t ↦ c (v t) ^ T.P ^ j t)).vecMul_surjective_iff_isUnit.2
      (by clear * - p hJ hN
          simp [↓isUnit_iff_isUnit_det, ↓← x.map_det, x, R]
          apply ne_of_apply_ne (eval fun v ↦ 0 ^ ((i - v.2).val / 2 - v.1))
          rw [RingHom.map_det, det_of_isUpperTriangular fun _ _ ↦ ?_ ∘ Prod.lex_def.1] <;> simp [c,
            v, rootVar, univ.prod_eq_zero_iff, apply_ite (eval _),
            @Nat.mod_eq_of_lt (j _) N (by grind)] <;> grind [pow_eq_zero_iff']) u
    use ∑ t, w t • X (v t) ^ T.P ^ j t, fun α h ↦ ?_, fun y ↦ by
      simpa [← hz, v, Matrix.map] using! dotProduct_mulVec ..
    obtain ⟨t, rfl, -⟩ := by simpa [coeff_X_pow] using support_sum h
    simp [weight_single, field, κ, -mul_ite]; clear * - hJ; gcongr <;> grind [rootVar,
      deepIndicator, one_lt_P]
  let ι := eval₂Hom (C.comp (x.comp C)) fun v ↦ ite (T.deepIndicator r v = 0) (C (x (X v))) (X v)
  have ⟨α, h, H⟩ := exists_le_cost_of_vanishing κ (by bound) z (fun y y' h ↦ funext fun t ↦
    (entry 0 (Pi.single t 1)).elim fun _ hf ↦ (y t).out_eq ▸ (y' t).out_eq ▸ Ideal.Quotient.eq.2
    (mt (·.map (T.ι 0)) (by simpa [← h, hf, a, x, R] using hf.2 y'))) ?_ (fun _ ↦ by simp only [κ,
    ← hz, entry]) τ (ι (polyOfCoeffs F)) (fun h ↦
    F0 (by ext β; simpa [polyOfCoeffs, coeff_sum] using congrArg (·.coeff (exponentOf β)) (by
           simpa [h, x] using congr(($(show x = .comp (eval (x ∘ X)) ι by
           ext <;> simp [ι, apply_ite])) (polyOfCoeffs F)) : polyOfCoeffs F = 0))) fun y ↦ ?_
  simp [polyOfCoeffs, coeff_sum, ι, prod_fintype, prod_ite, ← map_pow, ← map_prod,
    coeff_prod_X_pow] at h
  obtain ⟨β, rfl, h, -⟩ := by simpa [x] using exists_ne_zero_of_sum_ne_zero h
  use β, h, H.trans (by simp [weight_eq_sum, κ, deepIndicator]; bound)
  subst e
  grw [card_fun, card_eq_nat_card, T.card_residueField, ← pow_mul, ← N.div_mul_le_self 2,
    prod_pow_eq_pow_sum, pow_le_pow_right₀] <;> simp [I, ↓sum_prod_type, ← univ.sum_mul,
    sum_deepIndicator, Fin.sum_univ_add, ← Nat.not_lt, -not_lt] <;> lia
  let A := ∑ t, Matrix.single (ρ t) (σ t) (y t).out
  let g : GL _ W := by use 1 + A, 1 + -A <;> simp (disch := lia) [A, univ.sum_mul_sum]
  rw [show F = T.letterRep n g⁻¹ *ᵥ T.letterRep n g *ᵥ F by simp [← map_mul],
    ← polyAction_polyOfCoeffs]
  simp [polyOfCoeffs, monomial_eq]
  refine sum_mem fun β _ ↦ (le_or_gt ..).elim
    (pow_le_pow_right · (mul_mem_left _ _ ?_)) (hF g nofun β · ▸ by simp)
  simp [depth, weight_eq_sum, ← prod_pow_eq_pow_sum, pow_mul']
  refine prod_mem_prod fun v _ ↦ pow_mem_pow ?_ _
  by_cases T.isEven v.2 <;> by_cases r ≤ v.1 <;> simp [polyAction_X, letterMatrix_apply, g, A, c,
    rootVar, ι, z, a, add_mul, univ.sum_mul, Matrix.sum_apply, Matrix.single, ite_and,
    @Finset.sum_comm I, deepIndicator, *, dotProduct,
    apply_ite (DFunLike.coe _), -coe_eval₂Hom, show ∀ t, ¬r ≤ ρ t ∧ r ≤ σ t by lia, Prod.ext_iff]
end FoldSeg2
section FoldSeg3
open IsLocalRing Module Nat Finset Finsupp LinearMap Matrix MvPolynomial Submodule
attribute [-simp] coe_units_inv mulVec_single
attribute [local simp] Finset.mul_sum Fintype.sum_prod_type LinearMap.ext_iff restrict_apply mulVec
  Matrix.mul_apply Matrix.trace coeff_sum eval_monomial map_eval RingHom.map_det _root_.funext_iff
variable {k D : ℕ} {W O σ : Type} [CommRing W] [IsLocalRing W] [CommRing O] (τ : Fin k → ℕ)
  (ι : W →+* O) [Fintype σ]
noncomputable def ClassMean.conjSubst (a : GL (Fin k) W) :=
  linSubst (a⁻¹.1ᵀ.kroneckerMap (ι · * ι ·) a.1)
lemma ClassMean.map_C_mul_mul_C {ν} (A B : Matrix σ σ O) (X : Matrix σ σ (MvPolynomial ν O))
    (l : Dual O _) : (A.map C * X * B.map C).map l = A * X.map l * B := ext
    (by simp [mul_comm (∑ _, _), C_mul', mul_left_comm])
attribute [local simp ←] ClassMean.map_C_mul_mul_C Matrix.map_map Matrix.map_mul monomial_sum_prod
  cast_prod cast_sum kroneckerPi_map kroneckerPi_mul mul_assoc
lemma ClassMean.eq_top_of_eval_monomial n {e d} (hd : d.IsHomogeneous e) (hW : n + e ≤ .card
    (ResidueField W)) {b} (hb : IsUnit (eval b d)) {p : Submodule O (Monomials σ n → O)}
    (hp : ∀ b, IsUnit (eval b d) → (ι <| eval b <| monomial ·.1 1) ∈ p) : p = ⊤ := by
  let q := p.comap (σ₁₂ := ι) ⟨⟨(ι ∘ ·), by simp⟩, by simp⟩
  simpa [q, Pi.single, Function.comp_update, eq_top_iff_forall_basis_mem (Pi.basisFun ..)] using
    subsingleton_tensorProduct.1
    ((subsingleton_dual_iff _).1 ((liftBaseChangeEquiv _).subsingleton_congr.1
    (subsingleton_of_forall_eq 0 fun e ↦ (by ext γ; simpa using congrArg (·.coeff γ) ·)
    ((mul_eq_zero_iff_right (by simpa [·] using hb.map (residue W))).1 (((IsHomogeneous.sum univ _ _
    fun γ _ ↦ isHomogeneous_monomial (e (q.mkQ (Pi.single γ 1))) γ.degree_eq).mul (hd.map
    (residue W))).eq_zero_of_forall_eval_eq_zero_of_le_card (by
    simpa [residue_surjective.comp_left.forall, mul_comm (e _),
      Algebra.smul_def _ (e _), or_iff_not_imp_right, ← residue_ne_zero_iff_isUnit] using
      fun b h ↦ congr(e $(q.ker_mkQ.ge ((pi_eq_sum_univ' _).subst (hp b h)))))
    ((Cardinal.natCast_toNat_le _).trans' (mod_cast hW)))))))
variable (σ) [IsDomain O] [CharZero O] [ValuationRing O]
lemma ClassMean.exists_invariant_diagonal_form (pp : k.Prime) (hp : ¬IsUnit (k : O)) f : ∃ q :
    _ → O, (∀ γ : σ →₀ ℕ, γ.degree < k ^ f → k ^ (Fintype.card σ * f) = γ.multinomial * q γ) ∧ ∀ A α
    β, (linSubst A (monomial β 1)).coeff α * q α = q β * (linSubst Aᵀ (monomial α 1)).coeff β := by
  have M s α (h : s.sum α < k ^ f) : (@multinomial σ s α : O) ∣ k ^ (#s * f) := by
    induction s using cons_induction <;> simp_all [multinomial_insert, pow_mul', _root_.pow_succ']
    gcongr
    grw [← (Nat.choose ..).ordProj_mul_ordCompl_eq_self, cast_mul, cast_pow, (notMem_maximalIdeal.1
      (Ideal.IsPrime.notMem_of_isCoprime_of_mem (coprime_ordCompl pp (choose_ne_zero
      le_self_add)).cast hp)).mul_right_dvd, factorization_choose_le_log, h, log_pow pp.one_lt]; lia
  choose q hq using fun γ ↦ iteInduction (M univ γ) fun _ ↦ dvd_zero _
  use (q ·), by grind [multinomial_eq_of_support_subset, degree_eq_sum], fun A α β ↦
    nsmul_right_injective α.degree.factorial_ne_zero
    (by grind [degree_eq_sum, by simpa [fockPairing, jet_eq_sum, prod_fintype, -coe_monomial] using
    (fockPairing_linSubst A (monomial α 1) (monomial β 1)), !congr(($(multinomial_spec ..) : O)),
    (Monomials.isHomogeneous_linSubst _ ⟨α, by aesop⟩).coeff_eq_zero])
lemma ClassMean.exists_mean {p : ℕ} (pp : p.Prime) (hp : ¬IsUnit (p : O)) f (hD : D < p ^ f)
    (hW : D + k < .card (ResidueField W)) (x : _ → ℝ) (P : ℝ → _) : ∃ κ : Dual O _,
  (∀ a ∈ levi W τ, ∀ g, κ (conjSubst ι a g) = κ g) ∧ (∀ α, weight (x ·.1) α ≠ weight (x ·.2) α
  → κ (monomial α 1) = 0) ∧ (∀ α, P (weight (x ·.1) α) → κ (monomial α 1) = if degree α ≤ D then p ^
  (k ^ 2 * f) • eval (vec 1) (monomial α 1) else 0) ∧ κ ∈ span O {l ∘ₗ (conjSubst ι u).toLinearMap |
  (u ∈ levi W τ) (l : Dual O _) (_ : ∀ α, ¬P (weight (x ·.1) α) → l (monomial α 1) = 0)} := by
  simp_rw [le_iff_lt_add_one]
  refine Fin.val_last (D + 1) ▸ (Fin.last _).induction ⟨0, by simp⟩ fun d ⟨κ, _, _, u, w⟩ ↦ ?_
  let Y := of fun i j ↦ C (@ite W (τ i = τ j) _ 1 0) * X (j, i)
  let g := kroneckerPi fun _ : Fin d ↦ Y.map (·.map ι)
  have H m t α w : (g m t).coeff α ≠ 0 → α.weight w = ∑ l, (w (t l, m l) : ℝ) := by simp +contextual
    [g, Y, kroneckerPi, ↓C_mul_X_eq_monomial, weight, eq_comm]
  let S := (Pi.basisFun O (Monomials _ d)).constr O fun γ ↦ g.map (·.coeff γ.1)
  have E (l : Dual ..) : S (l <| monomial · 1) = g.map l := ext fun m t ↦ by simp [Matrix.sum_apply,
    S, mul_comm,
    ← congr(l $(sum_monomials_eq_of_isHomogeneous (by simpa [weight_eq_sum] using H m t · 1)))]
  have hv b : _ = kroneckerPi fun _ ↦ (Y.map (eval b)).map ι :=
    (E (aeval (ι ∘ b)).toLinearMap).trans (ext (by simp [g, kroneckerPi]))
  have L (a : levi W τ) : Y.map (eval (vec a.1)) = a.1 :=
    ext (by simp_all [Y, apply_ite, ite_apply, a.2 _])
  choose ev he using (mem_range.2 ⟨_, L · ▸ hv _⟩)
  have sp p (hp' : ∀ {c} a, S c = S (ev a) → c ∈ p) := eq_top_of_eval_monomial ι d (Y.det_apply' ▸
    IsHomogeneous.sum _ _ _ fun _ _ ↦ .C_mul
      (.prod _ _ 1 (by solve_by_elim [isHomogeneous_C_mul_X]))
    _) (by simp; lia) (by simpa using L 1 ▸ isUnits_det_units 1) (by simpa using! fun b h ↦ (hp' _
    ((hv b).trans (he ⟨.mk'' _ h, by clear * -; simp_all [Y, levi]⟩).symm)))
  let N := ⨆ t, (toLin'.1.flip (Pi.single t (ite (P (∑ l, x (t l))) 1 0)) ∘ₗ S).range
  obtain ⟨m, _, q, _, hq'⟩ := iSup_le_iff.1 (le_refl N), @free_of_flat_of_isLocalRing O N _ _ _ _ _
    (Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (isTorsionFree_iff_torsion_eq_bot.1 inferInstance)),
    exists_invariant_diagonal_form (Fin k × Fin k) pp hp f
  let K := pi fun γ : Monomials _ d ↦ (lcoeff O γ.1).smulRight (q γ.1)
  have hK α : S (K (monomial α 1)) = _ := congr(S $(by simp [K]; lia)).trans (E (q α • lcoeff O α))
  have adj := by simpa using fun a ↦ (linearMap_ext fun α ↦ ext_ring (by
    erw [congrArg S (funext (hq' _ · α)), E ((q α • lcoeff O α) ∘ₗ (linSubst _).toLinearMap)]
    simp [*, g, -LinearMap.coe_smul]; congr!
    simp [← ext_iff, -prod_mul_distrib, univ.sum_mul, Y, linSubst, ← C_mul', kroneckerPi, -ite_mul]
    congr! 3; grind [a.2 _, inv_mem a.2 _]) :
    S ∘ₗ K ∘ₗ conjSubst ι a.1 = mulLeftRight O (S (ev a), S (ev a⁻¹)) ∘ₗ S ∘ₗ K)
  let ρ : _ →ₗ[O] End O N := ⟨⟨(S · |>.toLin'.restrict (id ((sp ((N.compatibleMaps N).comap
    (toLin'.1 ∘ₗ S)) fun a _ ↦ iSup_le fun v ↦ range_le_iff_comap.2 (sp _ fun b _ ↦
    m v ⟨ev (a * b), by simp [*]⟩)).ge ⟨⟩))), by simp⟩, by simp⟩
  let b := finBasis O N
  use κ + trace O N ∘ₗ ρ ∘ₗ K, fun a h f ↦ by simp [*]; convert ((ρ (ev ⟨a, h⟩)).trace_mul_cycle O
    (ρ (K f)) (ρ (ev ⟨a, h⟩⁻¹))) <;> simp [*, ρ], fun α h ↦ by simpa [*, ρ] using
    (LinearMap.isNilpotent_trace_of_isNilpotent (End.isNilpotent.restrict _ (.map ⟨2, (sq _).trans
    (ext fun _ _ ↦ sum_eq_zero (by simp; grind))⟩ toLinAlgEquiv'))).eq_zero, fun α h ↦
    congr($(u α h) + $((trace_comp_comm' _ (codRestrict N _ ((range_toLin' _).trans_le (span_le.2
    (Set.range_subset_iff.2 (m · ⟨K (monomial α 1), by simp [*]; grind⟩))) ⟨·, rfl⟩))).trans
      (.trans (by simp [*, g, Y, kroneckerPi, sum_pow']; congr!) congr(_ *
    $(coeff_linearCombination_X_pow_of_fintype
    (vec 1) α d))))).trans (by simp [sum] at *; grind [degree_apply])
  convert add_mem w (sum_mem (t := univ) fun j ↦ by
    simpa using (iSup_le fun v ↦ range_le_iff_comap.2 (sp _ fun {c} a _ ↦ by
      exists ⟨_, m v ⟨c, rfl⟩⟩, subset_span ⟨_, a⁻¹.2, (b.coord j ∘ₗ ρ c) ∘ₗ codRestrict N _
      (m v ⟨·, rfl⟩) ∘ₗ K, fun α h ↦ ker_le_ker_comp _ _ (by simp [*]; grind), by simp [ρ, *]⟩) :
      N ≤ (comap ((ρ ∘ₗ K).flip.compr₂ (b.coord j)) _).map N.subtype) (b j).2)
  simp [trace_eq_matrix_trace O b, toMatrix_apply]
end FoldSeg3
section FoldSeg4
attribute [-instance] IsAddTorsionFree.of_isDomain_charZero instCharZeroOfIsSemireal
variable {σ R A N k W} [CommRing R] [CommRing A] [Algebra R A] (F : ℝ → AddSubgroup R) (c : σ → ℝ)
  (w : R) (t : ℝ) (χ : MvPolynomial σ R →ₐ[R] A) [NeZero N] [CommRing W] [IsLocalRing W]
  (T : TwistingData N W R)
open Polynomial IsLocalRing Function in
lemma stepanov_count (ι : W →+* R) {Φ} E (h0 : Φ ≠ 0) (h : ∀ x, X ^ E ∣ taylor (ι x) Φ) :
    E * .card (ResidueField W) ≤ Φ.natDegree := by
  cases fintypeOrInfinite (ResidueField W) <;> simp [Nat.card]
  simpa [Nontrivial.of_polynomial_ne h0, Monic.natDegree_pow, monic_prod_X_sub_C, Finset.prod_pow,
    Monic.pow] using (Monic.not_dvd_of_natDegree_lt · h0 · (Fintype.prod_dvd_of_coprime
    (fun x y h ↦ .pow (isCoprime_X_sub_C_of_isUnit_sub (map_sub ι .. ▸ .map ι (by simpa
    [← residue_ne_zero_iff_isUnit, surjInv_eq]))))
    (X_sub_C_pow_dvd_iff.2 <| h <| surjInv residue_surjective ·)))
class IsRealFiltration extends SetLike.GradedMonoid F where antitone : Antitone F
open MvPolynomial Matrix Finsupp SetLike Nat Ideal.Quotient IsRealFiltration AddSubgroup
@[simp] def adicFiltration := mk ⟨⟨{x | w ^ ⌈t⌉₊ ∣ x}, .add⟩, by simp⟩ .neg_right
instance : IsRealFiltration (adicFiltration w) where
  one_mem := by simp
  mul_mem _ _ _ _ a b := by simp_all; grw [ceil_add_le, pow_add, a, b]
  antitone _ _ _ _ := .trans (by gcongr)
def gaussFiltration := mk ⟨⟨{f : MvPolynomial σ R | ∀ α, f.coeff α ∈ F (t - weight c α)},
  by aesop⟩, by simp⟩ (by simp)
variable {c t F w} {a a' : Fin k}
lemma mem_adicFiltration_of_nonpos {x} (h : x ≠ 0 → t ≤ 0) : x ∈ adicFiltration w t := by
  by_cases x = 0 <;> simp_all [ceil_eq_zero.2]
lemma monomial_mem_gaussFiltration {α x} : x ∈ F (t - weight c α) →
  monomial α x ∈ gaussFiltration F c t := fun _ _ ↦ by aesop
instance [IsRealFiltration F] : IsRealFiltration (gaussFiltration F c) where
  one_mem := monomial_mem_gaussFiltration (by simp [one_mem_graded])
  mul_mem _ _ f _ h h' _ := f.coeff_mul .. ▸ sum_mem fun (a, b) ↦ by
    simp; grind [mul_mem_graded (h a) (h' b)]
  antitone _ _ _ _ := (antitone (by grind) <| · ·)
lemma aeval_sub_mem_of_gaussFiltration G [IsRealFiltration G] {f} (h :
  f ∈ gaussFiltration F c t) (u : ∀ i, χ (X i) ∈ G (c i)) (ψ := χ) (v :
  ∀ i, ψ (X i) - χ (X i) ∈ G (c i + 20⁻¹) := by simp) (y : ∀ {t x}, x ∈ F t → algebraMap R A x ∈ G
  t := by intros; (repeat apply monomial_mem_gaussFiltration); simpa) : ψ f ∈ G t ∧
  ψ f - χ f ∈ G (t + 20⁻¹) := by
  induction' f using induction_on'' with _ α x f e _ _ _ p i I generalizing t
  simpa using y (h 0)
  simp_all [add_sub_add_comm, add_mem_cancel_left,
    monomial_mem_gaussFiltration (by simpa [f.notMem_support_iff.1 e] using h α)]
  have ⟨a, b⟩ := @I (t - c i) (by grind [weight_single, coeff_mul_X, h <| · + single i 1])
  grind [mul_mem_graded a (add_mem (u i) (antitone (by simp) (v i))),
    add_mem (mul_mem_graded b (u i)) (antitone (by grind) (mul_mem_graded a (v i)))]
lemma TwistingData.root_lemma i (ha : a ≠ a') τ c {f α} (l : ℕ) (h : ∀ g ∈ levi W τ,
  T.polyAction g⁻¹ f ∈ gaussFiltration (adicFiltration T.w)
  c (l + weight c α)) (h0 : ¬T.w ^ (l + 1) ∣ f.coeff α) (hτ : τ a = τ a') (hc : ∀ s, c (T.rootVar a
  a' s) - c (T.rootVar a' a s) ∈ Set.Icc 0.4 1.6) : weight (T.excessWeight i a a') α ≤ 0 := by
  set y := T.rootVar a _; set x := T.rootVar _ a; let π z := ite (z = y i) (x i) z
  have hm β : mapDomain π β + single (y i) (β (y i) : ℕ) = β + single (x i) (β (y i)) := by
    induction β using induction_linear <;> simp [mapDomain_add] <;> grind
  let g r := .swap W a a' * transvectionGL ha (ite (T.isEven i) (-r) r)
  let σ z := Equiv.swap (x z.2) (y z.2) z
  obtain ⟨_, f1, _, hs, ω, _⟩ := T.one_lt_q, h 1, hc i, T.five_mul_P_pow_le_q,
    mul_left_surjective₀ (one_pos.trans T.one_lt_q).ne' (c (y i) - c (x i))
  simp at *; have : 0 < ω := by nlinarith
  have _ s t : y s ≠ x t ∧ x s ≠ y t := by grind [rootVar]
  let ε z := ite (z = y z.2) (ite (T.isEven z.2 = T.isEven i) (-1) 1) 0
  have cs z : ∃ s, (s = i ∨ s ≠ i ∧ y s ≠ y i ∧ 5 ≤ T.P ^ (s - i).val) ∧ (z = y s ∨ z = x s ∨
    ∀ t, z ≠ y t ∧ z ≠ x t) := by grind [TwistingData, le_pow, ZMod.val_pos, rootVar]
  rify at cs hs
  let m z := ite (z = x z.2) (T.P ^ (z.2 - i).val) 0 * T.q
  let e z := ite (z = y z.2) (T.P ^ (1 + (z.2 - 1 - i).val)) 0
  let χ z := monomial (single (π z) 1) (monomial (single () (m z)) (1 : R))
  let η z := monomial (single (σ z) 1)
    (monomial (single () (e (σ z))) (ite (z.2 = i) 0 (ε z + ε (σ z)) : R))
  let d u (v : _ → ℕ) z := c z - v z * u
  let G u v := gaussFiltration (gaussFiltration (adicFiltration T.w) fun () ↦ u) (d u v)
  have ag r z : T.polyAction (g r) (X z) = X (σ z) + C (ε z * T.ι z.2 r) * X z := by
    simp +zetaDelta [polyAction_X, letterMatrix_apply, transvectionGL, swap,
      GeneralLinearGroup.swap, Equiv.swap_apply_eq_iff]
    split <;> simp [transvection, Matrix.single, add_mul, ite_and,
      apply_ite (DFunLike.coe _)] <;> grind [rootVar]
  have ⟨A, D⟩ :=
    aeval_sub_mem_of_gaussFiltration (aeval χ) (G (-ω) m) f1 ?_ (aeval (χ - η)) ?_ <;> intros
  have l2 z r (m : ℕ) : monomial (single z 1) (C (T.ι (i + m) r) + X () ^ T.P ^ m - (X () + C (T.ι i
      r)) ^ T.P ^ m) ∈ G ω e (d ω e z + 2) := monomial_mem_gaussFiltration
    (.trans (pow_dvd_pow _ (by simp [↓weight_single, weight_eq_sum, *])) <|
    (C_dvd_iff_dvd_coeff (_ ^ 2) _).1 (by simpa [w_sq, prime, ← pow_mul, add_pow_prime_pow_eq',
    ← sub_sub, dvd_sub_left] using (map_dvd C (T.frobenius_pow_congr ..))) ·)
  let u := uniqueAlgEquiv R Unit
  have S {r} := aeval_sub_mem_of_gaussFiltration ((mapAlgHom ((u.arrowCongr u).symm
    (Polynomial.taylorAlgHom (T.ι i r)))).comp (.comp (aeval (χ - η)) (T.polyAction (g r)))) _
    (h (g r) (by apply mul_mem <;> simp [levi, swap, transvection] <;> grind)) fun z ↦
    Eq.subst ?_ (sub_mem (?_ : (χ - η) (σ z) ∈ _) (sub_mem (antitone ?_ (l2 (σ z) (|ε z| * r)
    (N + (z.2 - i).val))) (zsmul_mem (antitone ?_ (l2 z r (z.2 - i).val)) (ε z))))
  any_goals simp [*]
  any_goals apply_rules only [sub_mem, monomial_mem_gaussFiltration, mem_adicFiltration_of_nonpos]
  any_goals obtain ⟨s, _ | _, rfl | rfl | _⟩ := cs ‹_› <;> simp +zetaDelta [*, ↓weight_single,
    monomial_eq, Equiv.swap_apply_def] <;> (try split <;> simp) <;> intros <;>
    first | ring1 | nlinarith [hc s, hs (s - i)]
  have V {t v s g} (j : ℕ) (h : g ∈ G t v s) (K : ∀ z, d t v (π z) = d t v z := by simp +zetaDelta
    [↓apply_ite (d _ _), *]) (hj : l < s - (weight c α - weight v α * t) - j * t := by
    rify at *; nlinarith) := ((u _).coeff_map _ j).trans ((eq_zero_iff_dvd ..).2 (trans
    ((pow_dvd_pow _ (by simpa [lt_ceil, weight_apply, ↓sum_mapDomain_index, add_smul, ↓K, d,
    mul_sub, sum_mul, mul_assoc] using hj : l < _)).trans (h (mapDomain π α) _))
    (coeff_uniqueAlgEquiv ..).symm))
  have : _ ≤ weight m α := (stepanov_count (.comp ..) (weight e α) (fun H ↦ h0 ?_) fun r ↦
    Polynomial.X_pow_dvd_iff.2 fun _ _ ↦ by simpa [← AlgHom.mul_apply, ← map_mul, -map_aeval,
    coeff_map] using (V _ S.1)).trans (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun _ _ ↦ V _ A)
  simpa +zetaDelta [weight_eq_sum, excessWeight, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul,
    mul_sub, field, T.card_residueField, ← @cast_le ℝ, -ite_mul]
  convert by simpa [H, eq_zero_iff_dvd] using V (weight m α) D
  exact f.induction_on' (fun β r ↦ by
    simp [χ, aeval_monomial, monomial_pow, u, Finsupp.prod, ← monomial_sum_prod, ← single_finsetSum,
      ↓coeff_uniqueAlgEquiv, apply_ite AddMonoidAlgebra.coeff,
      DFunLike.ite_apply, ← ite_and, -single_mul]; congr!
    use by bound, fun _ : mapDomain .. = _ ∧ weight m β = _ ↦ by
      simpa +zetaDelta [*, by
        simpa +zetaDelta [*, add_comm, weight_single, T.prime.ne_zero,
        -ite_mul] using congr(($(hm α) + $((hm β).symm)).weight m)] using (hm β).symm) (by simp_all)
end FoldSeg4
noncomputable section
namespace TwistingData
open MvPolynomial Matrix Finsupp SetLike IsRealFiltration Ideal.Quotient Fintype Function List Nat
variable {N k W O R} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O] [CommRing R]
  (T : TwistingData N W O) (h : GL (Fin k) W) (s : ZMod N) (r ℓ n d : ℕ) (a a' : Fin k)
  (ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R)
abbrev frobGenericMatrix := of fun b c : Fin k ↦ @X O _ _ (s - d, b, c) ^ T.P ^ d
def frobOperator := kroneckerPi fun s ↦ symPowMatrix n (of fun b c ↦ ite (T.isEven s) id
  (·.adjugateᵀ) ((range (ℓ + T.deepIndicator r (b, s))).map (ψ s)).reverse.prod b c)
def letterConj := MonoidHom.mk ⟨(h.1.map (T.ι s) * · * h⁻¹.1.map (T.ι s)), by simp⟩
  (by simp [mul_assoc, ← (h.1⁻¹.map _).mul_assoc])
def indexWeight b := (ite (b = a') 1 0 - ite (b = a) 1 0) / (T.P ^ ℓ : ℝ)
variable {r ℓ n d s a a' h ψ β γ ν}
attribute [local simp] weight_eq_sum sum_prod_type_right indexWeight letterConj mul_sub map
  Matrix.mul_apply letterMatrix deepIndicator
lemma frobOperator_map (χ : R →+* O) (hh : h ∈ levi W (twoBlock k r)) :
  (T.frobOperator r ℓ n ψ).map χ = T.letterRep n h⁻¹ * T.frobOperator r ℓ n (fun s d ↦
  T.letterConj h s ((ψ s d).map χ)) * T.letterRep n h := by
  simp_rw [letterRep_apply, frobOperator, ← kroneckerPi_mul, ← map_mul, ← kroneckerPi_map,
    ← symPowMatrix_map]
  congr!
  have e {M s} : .map (ite (T.isEven s) id (·.adjugateᵀ) M) χ = T.letterMatrix s h⁻¹ * ite (T.isEven
    s) id (·.adjugateᵀ) (T.letterConj h s (χ.mapMatrix M)) * T.letterMatrix s h := by
    split <;> simp [*, ← transpose_mul, adjugate_mul_distrib, mul_assoc, adjugate_mul, mul_adjugate,
      smul_smul, transpose_map, ← det_mul, ← (h.1⁻¹.map _).mul_assoc]; exact χ.map_adjugate _
  ext; erw [congrFun₂ e]
  simp [-coe_units_inv, map_list_prod, comp_def]; congr! 3
  grind [transpose_apply, twoBlock, hh _, inv_mem hh _]
lemma frobOperator_mem G [IsRealFiltration G] (α : _ → _ → Fin k → ℝ) x u (e :
  (∀ s b, |α s 0 b| ≤ u) ∧ ∀ s d, ∑ b, α s d b = 0) (hx : ∀ b s, x (b, s) =
  ite (T.isEven s) 1 (-1) * α s (ℓ + T.deepIndicator r (b, s)) b) (H : ∀ s, ∀ d ≤
  ℓ, ∀ b c, ψ s d b c ∈ G (α s (d + 1) b - α s d c - u)) (o : 0 ≤ u := by positivity) :
  T.frobOperator r ℓ n ψ β γ ∈ G (weight x (exponentOf β) - N * (n * (k * ((ℓ + 2) * u)))) :=
  antitone (by simp [← Finset.sum_mul, ← cast_sum, Monomials.degree_eq, ← degree_eq_sum,
  exponentOf]) (prod_mem_graded _ _ _ fun s _ ↦ (show _ ∈ gaussFiltration G (k * ((ℓ + 2) * u) - x
  ⟨·, s⟩) 0 by simpa [linSubst, bind₁_monomial, X, smul_monomial] using
  prod_pow_mem_graded _ 0 _ _ fun c _ ↦ sum_mem fun b _ ↦ monomial_mem_gaussFiltration (by
  simp [↓weight_single, *]
  generalize l : ℓ + _ = m
  replace l : m ≤ ℓ + 1 := by lia
  have h {b c} : ((range m).map (ψ s)).reverse.prod b c ∈ G (α s m b - (m + 1) * u) := by
    induction' m with m I generalizing b <;> simp [range_succ]
    grind [zero_mem, antitone _ (one_mem_graded G)]
    exact sum_mem fun x ↦ by grind [mul_mem_graded (H s m _ b x) (@I _ x)]
  split <;> simp [adjugate, cramer_apply, det_apply]
  exact antitone (by grw [← b.pos.nat_succ_le, l]; grind) h
  exact sum_mem fun π _ ↦ zsmul_mem
    (antitone (by simp [Finset.sum_update_of_mem]; grw [l, card_finset_fin_le]; grind)
    (prod_mem_graded G (update (α s m · - (m + 1) * u) b 0) _
    (by grind [zero_mem, updateCol_apply, transpose_apply, one_mem_graded G]))) _)) _)
lemma X_mem_gaussFiltration {σ w ω v} : @X O σ _ v ∈ gaussFiltration (adicFiltration w) ω (ω v) :=
  monomial_mem_gaussFiltration (by simp [weight_single])
omit [NeZero N] in
lemma p_dvd_cj_frobenius_sub {Y b c} : ↑T.p ∣ T.letterConj h s ((T.letterConj h⁻¹ (s - d) Y).map
  (· ^ T.P ^ d)) b c - Y b c ^ T.P ^ d := let π := Ideal.Quotient.mk (.span {(_ : O)})
  let f := RingHom.mk' (π.1.comp (powMonoidHom _)) (by
    simp [← pow_mul, add_pow_prime_pow_eq T.prime, π, -map_natCast])
  (eq_zero_iff_dvd ..).1 (sub_eq_zero.2 (congrFun₂ ((by simp [← RingHom.coe_comp, ← mul_assoc,
    mul_assoc (Y.map _), show π ∘ (· ^ _) = f by rfl, show π.comp _ = f.comp
    _ by ext; simpa [← eq_zero_iff_dvd] using! T.frobenius_pow_congr d (s - d) _]) : .map _ π =
    Y.map f) ..))
lemma pow_dvd_coeff_conj_frobOperator (ha : a + 1 = a'.1) i (hn : N * n * k * (ℓ + 2) ≤
  T.P ^ ℓ) (hl : ℓ ≤ N) h {ψ} (hψ : ψ = fun s (d : ℕ) ↦ (map C T).letterConj h s
  (((map C T).letterConj h⁻¹ (s - d) (of fun b c ↦ X (s - d, b, c))).map (· ^ T.P ^ d))) {c : ℕ}
  (e : ∀ j ≠ i, weight (T.indexWeight ℓ a a' ·.1) (ν.curry j) = weight (T.indexWeight ℓ a a' ·.2)
  (ν.curry j)) (g : 2 * c + 1 < |weight (T.excessWeight (i + ℓ) a a') (exponentOf β) - weight
  (T.indexWeight ℓ a a' ·.1) (ν.curry i)|) : T.w ^ c ∣ (T.frobOperator a' ℓ n ψ β γ).coeff ν := by
  obtain ⟨rfl, _, _, ε, hε, g⟩ := hψ, T.prime.ne_zero, T.one_lt_P.le,
    (RCLike.exists_norm_eq_mul_self _).imp fun _ ↦ And.imp_right g.trans_eq
  let A m b := T.indexWeight ℓ a a' b * (ε / 2 * T.P ^ m / T.q)
  let ω | (j, b, c) => ite (j = i) (A N b) (A (j - i).val b - A (j - i).val c)
  have hA {m} (e : m ≤ N) b : ‖A m b‖ ≤ 2⁻¹ / T.P ^ ℓ := by
    simp [A, *, field]; split_ifs <;> simp <;> gcongr <;> lia
  refine .trans (pow_dvd_pow _ (lt_ceil.2 ?_).le) (T.frobOperator_mem (gaussFiltration
    (adicFiltration _) ω) (fun s d ↦ A (d + (s - d - i).val)) (T.excessWeight (i + ℓ) a a' · *
    (ε / 2)) _ ⟨fun _ ↦ hA (by grind), by simp [A, sub_mul, div_eq_mul_inv]⟩ (fun _ _ ↦ by
    dsimp; split_ifs <;> simp [excessWeight, rootVar, field, -one_add_val_sub_one_sub] <;> ring_nf
      <;> grind only) (fun s d hd b c ↦ have hω {v} := abs_le.1 (show |ω v| ≤ 1 / T.P ^ d by
    grw [hd]; clear_value A; grind [Real.norm_eq_abs]); have := abs_le.1 (hA (hd.trans hl) c)
      antitone (by simp [ω, ← sub_sub, add_assoc]; split <;> simp_all [A, pow_add, ← mul_div] <;>
        linarith) fun μ ↦ if q :
        _ then .trans (.pow (dvd_zero _) q) ((show _ ∈ gaussFiltration (adicFiltration _) ω _ by
    simp [← monomial_zero']
    solve_by_elim (transparency := .instances) (maxDepth := 50) [mul_mem_graded, pow_mem_graded,
      antitone hω.1 X_mem_gaussFiltration, monomial_mem_gaussFiltration,
      mem_adicFiltration_of_nonpos, (sub_self _).le, sum_mem]) μ) else
    (dvd_sub_left (pow_mem_graded _ X_mem_gaussFiltration μ)).1 (.trans (pow_dvd_pow _ (by
    clear_value ω; simp [field] at *; grind)) (T.w_sq ▸ (C_dvd_iff_dvd_coeff ..).1
    (T.map C).p_dvd_cj_frobenius_sub μ))) ..)
  grw [show (N : ℝ) * _ ≤ 2⁻¹ by field; norm_cast]
  simp_all [↓sum_prod_type, ω, A, ← mul_assoc, ← Finset.sum_mul]; bound
lemma degree_le_of_coeff_frobOperator (e : (T.frobOperator (k := k) r ℓ n
  T.frobGenericMatrix β γ).coeff ν ≠ 0) j : degree (ν.curry j) ≤ N *
    (n * (k * ((ℓ + 2) * T.P ^ ℓ))) := by
  rify; simpa [degree_eq_sum] using (mt zero_pow (ne_zero_of_dvd_ne_zero e (T.frobOperator_mem
    (gaussFiltration _ (if ·.1 = j then -1 else 0)) 0 0 _ (by simp) (by simp) (fun s d h _ _ ↦
    antitone (by grw [← h] <;> bound [T.prime.pos]) (pow_mem_graded _ X_mem_gaussFiltration)) ..)))
end TwistingData
end
section FoldSeg6
open Module Nat Subgroup Filter Finset Finsupp Fintype Matrix MeasureTheory MvPolynomial Real
  MeasureTheory.Measure
variable {N k W K} [NeZero N] [CommRing W] [IsLocalRing W] [Field K] (T :
  TwistingData N W K) {a a' : Fin k}
instance [Finite (IsLocalRing.ResidueField W)] (τ) :
    (@parahoric k W _ _ τ).FiniteIndex := finiteIndex_of_le (ker_le_comap ..)
lemma index_borel_le [Finite K] : (parabolic (R := K) (OrderDual.toDual ∘ @Fin.val k)).index ≤ ∏ l :
    Fin k, ((Nat.card K : ℝ) ^ (l.1 + 1) - 1) / (Nat.card K - 1) := by
  set A := @parabolic ..
  simpa [card_GL_eq_prod, Nat.card_pi, Nat.card_units, prod_range, Finite.one_lt_card,
    prod_pow_eq_pow_sum,
    field] using mono_cast (α := ℝ) (A.index_mul_card.le.trans' (mul_le_mul_left _
    (card_le_card_of_injective (fun x : ∀ i, Kˣ × (Set.Iio i → K) ↦ ⟨.mkOfDetNeZero (of fun i j ↦
    ite _ 0 (dite _ ((x i).2 ⟨j, ·⟩) fun _ ↦ (x i).1)) (by simp +contextual [BlockTriangular,
    det_of_isLowerTriangular, univ.prod_eq_zero_iff]), fun _ _ ↦ (ite_eq_left ·)⟩) fun x y h ↦ by
    ext i j <;> [simpa using congr($h.1 i i); simpa [lt_asymm, j.2.out] using congr($h.1 i j)])))
variable (a) in
def TwistingData.excessCone (h : ℝ) :=
  {β | ∀ i (b b' : Fin k), b.1 + 1 = b' → T.excessWeight i b b' ⬝ᵥ β ≤ ite (b' = a) h 0}
lemma TwistingData.finrank_excessCond_le_volume [CharP K T.p] (ha : a.1 + 1 = a') n h :
    finrank K (T.excessCond n a a' ⊥ h) ≤ (parahoric W (↑)).relIndex (levi W (twoBlock k a')) *
  volume.real (T.excessCone a' (h + N * (k + 1)) ∩ slab k fun _ ↦ n + k + 1) := by
  refine ge_of_tendsto_of_frequently (.const_mul _ (tendsto_card_div_pow_atTop_volume _ ?B (by
    unfold excessCone slab dotProduct; measurability) (Convex.addHaar_frontier _
    (by exact fun _ ⟨X, _, A⟩
    _ ⟨Y, _, B⟩ _ _ s t e ↦ ⟨fun _ _ _ _ ↦ by simp; grw [X .., Y ..] <;> simp [↓← add_mul, *],
    by positivity, fun j ↦ by simpa [univ.mul_sum] using convex_Icc _ _ (A j) (B j) s t e⟩))))
    (frequently_atTop'.2 fun t ↦ let m := T.q ^ t; ⟨m, t.lt_pow_self (mod_cast T.one_lt_q), ?_⟩)
  apply isBounded_inter_slab
  obtain ⟨_, _, p0, R, hR, h1⟩ := T.finite_residueField, Fact.mk T.prime, CharP.cast_eq_zero K _,
    ((parahoric W (↑)).subgroupOf (levi W (twoBlock k a'))).exists_isComplement_right 1
  set Λ := @Inter.inter ..
  obtain ⟨m1, _, _⟩ := NeZero.pos m, hR.finite_right.fintype, ((ZSpan.setFinite_inter _ ?B).subset
    (inf_le_inf_left _ (ZSpan.smul _ (NeZero.ne _)).le) : Λ.Finite).fintype
  field_simp
  norm_cast
  let γ (u : _ × ZMod N → Fin m) := equivFunOnFinite.symm fun x ↦
    u x + m * ite (x.1 = a) (k - (∑ b, (u (b, x.2)).1) / m) 0
  let p := ∑ u, .mulRight K (monomial (γ u) 1) ∘ₗ (expand m).toLinearMap ∘ₗ polyOfCoeffs ∘ₗ
    (T.excessCond n a a' ⊥ h).subtype ∘ₗ .proj u
  convert (LinearMap.pi fun x : R × Λ ↦ lcoeff K (equivFunOnFinite.symm (⌊x.2.1 · * m⌋₊)) ∘ₗ
    (T.polyAction x.1).toLinearMap ∘ₗ p).finrank_le_finrank_of_injective (.of_ker _ fun F f0 ↦ ?_)
  iterate 2 simp [relIndex, ← hR.card_right, mul_comm]
  ext u β; by_contra
  let w (x : Fin k × _) : ℝ := ite (T.isEven x.2) x.1 (-x.1)
  have ⟨⟨x, α⟩, hα, H⟩ := (univ.sigma fun x : R ↦ (T.polyAction x (p F)).support).exists_min_image
    (weight w ·.2) ⟨⟨⟨1, h1⟩, m • exponentOf β + γ u⟩, by
    simp [p, polyOfCoeffs, coeff_sum]
    rw [Fintype.sum_eq_single u fun v n ↦ Finset.sum_eq_zero fun _ _ ↦ ite_eq_right fun e ↦ n (by
    ext x; simpa [γ, mod_eq_of_lt, -mul_ite] using congr($e x % m))]; simpa [m1.ne']⟩
  refine absurd (congrFun f0 ⟨x, (α · / m), ?_, BoxIntegral.unitPartition.mem_smul_span_iff.2
    (⟨α ·, by simp [field]⟩)⟩) (by simpa using hα); clear f0
  obtain ⟨u, δ, ⟨ε, ⟨⟩⟩, hu, hv⟩ := by
    simp [p, ← AlgHom.mul_apply, (algHom_ext
      (by simp [m, ↓← pow_mul, polyAction_X, sum_pow_char_pow, mul_pow, ← C_pow, letterMatrix,
      ← (by simpa [← pow_mul, p0] using T.frobenius_pow_congr (N * t))]) : Commute (T.polyAction _)
      (expand m)), (expand m).mul_apply, polyAction_polyOfCoeffs, monomial_eq, polyAction_X] at hα
    simp [coeff_sum, polyOfCoeffs, univ.sum_mul, ← sum_prod_type'] at hα
    simpa [coeff_monomial_mul', le_iff_exists_add] using exists_ne_zero_of_sum_ne_zero hα
  have he s : ∑ b, ε (b, s) ∈ Set.Icc (m * k) (m * k + m) := by
    apply IsWeightedHomogeneous.prod _ _ _ fun j _ ↦ .pow (.sum _ _ (ite (j.2 = s) 1 0) fun b _ ↦
      (isWeightedHomogeneous_X K (if ·.2 = s then 1 else 0) (b, _)).C_mul (T.letterMatrix _ x b _))
      _ at hv
    simp [γ, weight_eq_sum, sum_prod_type, Nat.mul_sub] at hv
    grind [(by grw [Fin.is_le']; simp : ∑ b, (u (b, s)).1 ≤ k * m), mul_div_self_eq_mod_sub_self,
      mod_lt (∑ b, (u (b, s)).1) m1]
  refine ⟨fun i b b' e ↦ ?_, fun _ ↦ by positivity, fun s ↦ by simp [← univ.mul_sum, exponentOf,
    field, ← cast_sum, ← degree_eq_sum, Monomials.degree_eq, ← sum_div]; norm_cast; grind [he s]⟩
  simp_rw [dotProduct, mul_div, ← sum_div, ← nsmul_eq_mul', ← weight_eq_sum, field, mul_ite_zero]
  split
  grw [map_add, map_nsmul, (by omega : b = a), ‹b' = _›, not_lt.1 (hu <| (F u).2 _ x.1.2 δ ⟨i, ·⟩),
    weight_eq_sum, T.excessWeight_mem_Icc.2, ← univ.sum_smul, sum_prod_type_right,
    (he _).2]; simp [field]
  apply T.root_lemma i _ _ w 0 (fun g hg ↦ (hR.2 (⟨g, hg⟩⁻¹ * x)).elim fun b hb ↦
    Set.mem_of_eq_of_mem (by simpa using congr(T.polyAction ($hb.symm).1 (p F)))
    (aeval_sub_mem_of_gaussFiltration _ _ (mem_adicFiltration_of_nonpos <| by
    simpa using H ⟨_, ·⟩) fun y ↦ by simpa [polyAction_X, C_mul_X_eq_monomial] using
    (sum_mem fun i _ ↦ monomial_mem_gaussFiltration (mem_adicFiltration_of_nonpos (by
    unfold w; split <;> simpa [weight_single, *] using (T.p_dvd_letterMatrix_of_mem_parahoric y.2
      b.1.2 i _).mt)))).1) <;> grind [w_sq, dvd_def, twoBlock, rootVar, congr(($e : ℝ))]
lemma TwistingData.excessWeight_dotProduct_permStep i ν :
  T.excessWeight i a a' ⬝ᵥ permStep T.isEven T.P 1 ν = (1 - 1 / T.q) *
  (permStep T.isEven T.P 1 ν (T.rootVar a a' i) - (ν (a, i) - ν (a', i))) := by
  let F s := T.P ^ (1 + (s - i).val) * (ν (a, s + 1) - ν (a', s + 1)) / T.q
  rw [dotProduct, sum_prod_type_right, ← add_sub_cancel_right (∑ _, _), ← sum_add_distrib,
    ← (Equiv.subRight 1).sum_comp F, ← sum_sub_distrib, Fintype.sum_eq_single i] <;> intros <;>
    by_cases T.isEven ‹_› <;> simp [F, excessWeight, ↓one_add_val_sub_one_sub, rootVar,
    division_def, sub_mul, *] <;> field [T.prime.ne_zero]
lemma TwistingData.exists_mem_excessCone_mem_Icc (ha : a.1 + 1 = a') :
    ∃ σ ∈ T.excessCone a' (-1), σ ∈ Set.Icc 0 fun _ ↦ (T.P ^ (3 * a'.1) : ℝ) := by
  obtain ⟨h5, hq, e⟩ := T.five_le_P, le_self_pow (NeZero.ne N) T.P,
    @T.excessWeight_dotProduct_permStep _ k
  rify at h5 hq e ⊢
  generalize (_ ^ T.o₀ : ℝ) = P at *
  let u b := ite (b ≤ a) (P ^ (2 * (a.1 - b)) * 2) 0
  have s b : (P ^ 2 - 1) * u b ∈ Set.Icc 0 (P ^ (3 * a'.1)) := by
    simp [u]; split <;> constructor <;> try bound
    grw [sub_le_self, (by bound : 2 ≤ P), ← pow_succ, ← pow_add, pow_le_pow_right₀] <;> grind
  refine ⟨permStep T.isEven P 1 fun x ↦ ite (T.isEven x.2) 1 P * u x.1, fun i b b' _ ↦ ?_,
    forall_and.1 fun (b', i) ↦ ?_⟩ <;> by_cases T.isEven i <;> simp [T.isEven_succ, *, field]
  iterate 2 rw [show u b = P ^ 2 * u b' + ite (b' = a') 2 0 by by_cases b = a <;> simp [u, *, ←
    mul_assoc, ← pow_add] <;> grind]; split <;> nlinarith [(s b').1, (by bound : P ≤ P * P ^ N)]
  all_goals grind [s b']
lemma volume_sum_mem_Icc_le {n} {d D : ℝ} (hd : d ≤ D) : volume
    {y : Fin n.succ → ℝ | (∀ b, 0 ≤ y b) ∧ univ.sum y ∈ Set.Icc (d - 1) d} ≤ ‖D ^ n / n !‖ₑ := by
  cases n
  grw [measure_mono, volume_pi_pi ![Set.Icc (d - 1) d]] <;> simp [Set.pi]
  grw [← (volume_preserving_piFinSuccAbove _ 0).symm.measure_preimage_equiv, volume_eq_prod,
    prod_apply_le (by measurability), ← setLIntegral_eq_of_support_subset (s := .uIcc D 0) fun x
    h ↦ (nonempty_of_measure_ne_zero h).elim _, ← setLIntegral_congr uIoc_ae_eq_interval,
    lintegral_mono ((measure_mono _).trans <| volume_sum_mem_Icc_le <| sub_le_sub_right hd ·),
    ← ofReal_integral_norm_eq_lintegral_enorm (Continuous.integrableOn_uIoc (by fun_prop))] <;> simp
    [← ofReal_norm, integral_div, abs_sub_comm D, integral_pow_abs_sub_uIoc,
    @Fin.forall_fin_succ (succ _), factorial] <;> grind [Finset.sum_nonneg, Set.mem_uIcc]
def HeckeSizes (P d N k n r ℓ : ℕ) (κ y z : ℝ) := 0 < r ∧ 2 * r ≤ k ∧ κ ≤ 1 ∧ 1 ≤ y ∧ ℓ + ℓ = N ∧
  N * (n * (k * (ℓ + 2))) + n + k < P ^ ℓ ∧ 6 * (2 * ((k + k ^ 2) * (d * N) * N) + 2 :) + 2 ≤
  y ∧ 2 * (N + 2) * k / y ≤ κ ∧ (y + N * (k + 1)) * k * P ^ (3 * r) + k + 2 ≤ y⁻¹ * n ∧ N * n *
  (1 / P ^ (2 * r) + r ^ 2 / (k * P)) ≤ z
lemma TwistingData.index_mul_finrank_excessCond_le [CharP K T.p] (ha : a.1 + 1 = a') {n ℓ h κ z}
  (big : HeckeSizes T.P T.o₀ N k n a' ℓ κ h z) : (parahoric W (twoBlock k a')).index * finrank K
  (T.excessCond n a a' ⊥ h) ≤ (1 + κ) * Fintype.card (Monomials (Fin k) n) ^ N := by
  obtain ⟨_ | k, ⟨σ, σ1, _, σ2⟩, _, -, -, _, _, _⟩ := k, T.exists_mem_excessCone_mem_Icc ha,
    T.finite_residueField, big
  lia
  let τ := (h + N * (k + 2)) • σ
  grw [T.finrank_excessCond_le_volume ha, Measure.real, (measure_mono _).trans_eq
    (measure_preimage_add _ τ _), ← Measure.real, relIndex_le_of_le_right, mul_left_comm,
    ← mul_assoc, ← cast_mul, relIndex_mul_index, parahoric, index_comap, relIndex_le_of_le_right,
    relIndex_top_right, index_borel_le, T.card_residueField, cast_pow, @prod_mul_volume_inter_slab _
    _ _ T.isEven _ T.one_lt_P (n + k + 2 + ∑ b, τ ⟨b, ·⟩) (T.excessCone a' 0) (by simp [excessCone,
    pieriCone, excessWeight_dotProduct_permStep, ← le_div_iff₀', inv_lt_one_iff₀,
    ↓one_lt_q, -cast_pow, -cast_npow]), Measure.real, (measure_mono (by exact fun β g j _ ↦
    ⟨(g.1 ⟨·, j⟩), g.2 j⟩)).trans
    (((measurePreserving_flip.comp measurePreserving_curry).measure_preimage_le _).trans
    ((volume_pi_pi _).trans_le (prod_le_pow_card _ _ _ fun j _ ↦ volume_sum_mem_Icc_le (show _ + _
    ≤ h⁻¹.exp * n by simp [τ]; grw [σ2 _, ← add_one_le_exp]; simp; grind))))] <;> try simp [
    relIndex, card_finsuppAntidiag_nat_eq_choose, mul_pow, mul_div_assoc, -enorm_mul, ← exp_nat_mul,
    (isBounded_inter_slab (T := ZMod N) ..).measure_lt_top.ne]
  grw [← choose_symm_add, ← pow_le_choose, ← le_add_right, exp_bound' (n := 1)] <;> (try gcongr) <;>
    simp [field] at * <;> nlinarith
  iterate 2 intro; simp [parahoric, parabolic, levi, BlockTriangular]; grind [twoBlock,
    not_isUnit_zero]
  exact ⟨fun β g _ _ _ _ ↦ by simp [τ]; grw [g.1 .., σ1 ..] <;> bound, fun β ⟨_, _, g⟩ ↦
    ⟨by positivity, (by simp; grind [g ·])⟩⟩
lemma TwistingData.sum_finrank_deepForms_le [CharP K T.p] {n r ℓ κ h z} (big :
  HeckeSizes T.P T.o₀ N k n r ℓ κ h z) M : (∑ d ∈ range M, finrank K (T.deepForms k n r d) : ℝ) ≤
  (1 + z) * Fintype.card (Monomials (Fin k) n) ^ N := by
  obtain ⟨_ | k, _, _, hk, -, hy, _, _, -, -, h2, h3⟩ :=
    k, (pow_right_mono₀ T.one_lt_P.le).map_sup ℓ (3 * r), big; lia
  grw [← hy, inv_one] at h2
  grw [((LinearMap.funLeft K K Subtype.val).domRestrict _).finrank_le_finrank_of_injective
    (.of_ker _ fun F e ↦ F.ext (Not.imp_symm (T.exists_le_weight_of_mem_deepForms hk
    (by norm_cast at *; lia) F.2) fun ⟨β, h, H⟩ ↦ h congr($e ⟨β, lt_succ_of_le (le_floor H)⟩)))]
  simp [Fintype.card_subtype, ← sum_boole, (range M).sum_comm, ↓← mem_range, weight_eq_sum]
  grw [min_le_right, floor_le (by positivity), sum_add_distrib, ← h3, le_expect univ_nonempty
    fun b ↦ imp_intro ((Equiv.Perm.subtypePerm (equivCongrLeft (.subLeft b)).symm (by
    simp [↓mem_finsuppAntidiag'])).bijective.comp_left.sum_comp _).ge]
  simp [↓expect_sum_comm, Finset.expect_eq_sum_div_card, ← univ.sum_mul, *, ← univ.mul_sum,
    exponentOf, field, ↓sum_prod_type, ← cast_sum, sum_deepIndicator, apply_ite, sum_ite,
    Fin.card_filter_val_lt,
    ← degree_eq_sum, Monomials.degree_eq, ← translate_apply, sum_translate, div_eq_mul_inv]
  grw [card_finset_fin_le, cast_succ, cast_div_le]
  ring
  bound
end FoldSeg6
namespace TwistingData
open MvPolynomial Matrix IsLocalRing Function Module PiTensorProduct Finset Fintype Kronecker Equiv
  ClassMean Ideal Pointwise MatMul
attribute [local simp] dotProduct prod_prod_type prod_eq_zero_iff mul_sum sum_mul vecMul
  sum_prod_type mulVec polyOfCoeffs Matrix.map IsConcreteLE.le_iff Submodule.mem_sup_left
attribute [local simp ←] map_mul kroneckerPi_mul Matrix.mul_apply
attribute [-simp] Matrix.one_apply _root_.map_inv
attribute [local grind] dvd_trans deepIndicator twoBlock pow_mul pow_dvd_pow dvd_mul_of_dvd_right
  dvd_def
variable {N k n W O X E H} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O] [IsDomain O]
  [ValuationRing O] (T : TwistingData N W O) (c : ℕ) {a r : Fin k} [Fintype X]
  [Fintype E] (Q M : Matrix (X × (ZMod N → Monomials (Fin k) n)) E O) (R β : type_of% Qᵀ)
omit [Fintype E] in
lemma card_le_finrank_translatesIn {s G B} (h : ∀ j ∈ s, ∀ i, (R * Q) i j = ite (i = j) 1 0)
    (hs : ∀ j ∈ s, ∀ x, Q.col j ∘ (x, ·) ∈ T.translatesIn n G (maximalIdeal O) B) :
    #s ≤ finrank (ResidueField O) (X → (map (residue O) T).translatesIn n G ⊥ B) :=
  card_coe s ▸ LinearIndependent.fintype_card_le_finrank (b := fun j x ↦ ⟨residue O ∘ Q.col j ∘ (x,
  ·), by simp_all [translatesIn, letterRep_map, ← map_sum]⟩)
  (linearIndependent_iff.2 fun g hg i ↦ by simpa [mul_sum _, sum_comm, mul_left_comm, h,
  ← mul_sum, ← map_sum] using congr(∑ y, residue O (R i y) * ($hg y.1).1 y.2))
lemma of_pairing a z {w G B} (hR : R * Q = 1) (hw : ¬IsUnit w) (h : ∀ i j, a * w ∣
    (β * M - a • 1 :) i j) (hn : ∀ u v F, Q *ᵥ u - M *ᵥ v = (a * w) • F → ∀ x, F ∘ (x, ·) ∈
    T.translatesIn n G (maximalIdeal O) B) : ∃ l, card E + l ≤
  finrank (ResidueField O) (X → (map (residue O) T).translatesIn n G ⊥ B) ∧
  IndexDvd ⊤ (.map (β * Q).mulVecLin ⊤ ⊔ z • ⊤) (a ^ card E * z ^ l) := by
  obtain ⟨⟨U, V⟩, _, G, _, t, e⟩ := isValuationPair_top.smith_normal_form ((Q * R * M - M) * R)
  rw [← G.mul_inv_eq_iff_eq_mul] at e
  choose s _ using (ValuationRing.cond (a * w) <| t ·)
  choose W _ using h
  let A := β * U * (diagonal (a • w • s) - diagonal t)
  refine ⟨_, (T.card_le_finrank_translatesIn (Q.fromCols U) (R.fromRows (V - V * Q * R))
    (by simp_all [V.mul_apply, Q.mul_apply, one_apply, by
    simpa [← ext_iff, ← Matrix.mul_assoc, hR, or_iff_not_imp_right] using
      congr(R * $e)]) ?_).trans_eq' (card_disjSum _ {i | t i ∣ a * w ∧ t i ≠ 0}), .trans
    (.of_det_dvd (A := A * G.1 * Q + β * Q * R * M) ?_ ?_) (.map (.of_det_dvd (by rw [det_diagonal,
    ← prod_const, prod_filter]) le_rfl) A.mulVecLin le_rfl (le_sup_of_le_right ?_))⟩
  simpa using ⟨fun j ↦ hn (Pi.single j _) 0 _ (by aesop), fun _ _ ⟨c, h⟩ _ ↦ hn _ _ _ (by
    simpa [-mulVec_smul, h, ↓ ← mulVec_mulVec, ↓diagonal_mulVec_single,
      ↓op_smul_eq_smul] using! congr($e *ᵥ Pi.single (_, _) c))⟩
  convert ((1 + w • (of W + β * U * diagonal s * G.1 * Q)).det_smul a).dvd.trans _
  ext; simp_all [A, ← e]
  grind
  simp_all [↓det_one_add_smul w, map_mul, ← residue_ne_zero_iff_isUnit, -residue_eq_zero_iff]
  simp [Submodule.add_mem_sup, -mulVec_mulVec]
  simpa using (⟨A *ᵥ ·, by simp [-sub_mulVec, A, funext_iff, -Matrix.mul_assoc]; grind⟩)
variable [CharZero O]
lemma exists_depth_factorization (ha : a < r) {x} (hm : ∀ β, T.depth k n r β ≤ x) (s : E → X) (g : E
  → _) (hs : Surjective fun e ↦ ((s e, ⟦(g e)⁻¹⟧) : X × _ ⧸ parahoric W (twoBlock k r))) : ∃ (Q d :
  Matrix _ _ O) (R : type_of% Qᵀ), (Q * d = of fun (e, α) (x, β) ↦ ite (s e = x) ((diagonal (T.w ^
  T.depth k n r ·) * T.letterRep n (g e) :) α β) 0) ∧ d.det ∣ T.w ^ ∑ τ ∈ range x,
  finrank (ResidueField O) (X → (map (residue O) T).deepForms k n r τ) ∧ R * Q = 1 ∧
  ∀ j e {h : ℝ}, 2 * c ≤ h → (Q *ᵥ j) ∘ (e, ·) ∈ T.excessCond n a r (span {T.w ^ c}) h := by
  set J := of _
  have hJ φ e : (J *ᵥ φ) ∘ (e, ·) = _ *ᵥ φ ∘ _ := funext (by simp [J, -diagonal_mul]; tauto)
  have hf {z φ} (h : ∀ y, z ∣ (J *ᵥ φ) y) x γ β :
      z ∣ T.w ^ T.depth k n r β * (T.letterRep n γ *ᵥ φ ∘ (x, ·)) β := by
    obtain ⟨e, rfl, he⟩ := by simpa [QuotientGroup.eq] using hs (x, ↑γ⁻¹)
    choose A hA using show ∀ s i j,
      T.w ^ T.deepIndicator r (j, s) ∣ T.w ^ T.deepIndicator r (i, s) * T.letterMatrix s
      (g e * γ⁻¹)⁻¹ i j by grind [p_dvd_letterMatrix_of_mem_parahoric, inv_mem, w_sq]
    rw [← mulVec_diagonal (_ ^ T.depth k n r ·), ← inv_mul_cancel_right γ, map_mul, mulVec_mulVec, ←
      mul_assoc, (?_ : diagonal _ * _ = kroneckerPi (symPowMatrix n ∘ of ∘ A) * _), mul_assoc,
      ← mulVec_mulVec, ← hJ]
    exact dvd_sum (by grind)
    simp [letterRep, diagonal_pow_depth]; congr! 3
    ext; simpa [mul_comm] using hA ..
  have ⟨U, _, D, _, e, _⟩ := isValuationPair_top.hermite
    (.ofSurjective _ ((Prod.fst_surjective.comp hs).prodMap surjective_id)) J
  obtain ⟨K, -, P, -, t, rfl⟩ := isValuationPair_top.smith_normal_form D
  have h0 i := @hf (t i) (P.2ᵀ i) (by simp [e, ← Matrix.mul_assoc])
  choose t' ht using fun i ↦ by simpa using show t i ∣ (P.1 * T.w ^ x • P.2) i i from (dvd_sum
    fun ⟨y, β⟩ _ ↦ by grw [h0 i y 1 β, hm]; simp [-mulVec])
  refine ⟨_, _, U.2.submatrix _ id, e.symm, ?_, by
    simpa [← submatrix_mul] using submatrix_one_embedding _, fun j _ _ _ l hl β ⟨i, h⟩ ↦ ?_⟩
  simp [-finrank_pi_fintype, -prod_prod_type]
  grw [prod_dvd_prod_of_dvd _ (T.w ^ #{τ ∈ range x | ¬t · ∣ T.w ^ τ}) fun i _ ↦ by
    set m := #_
    grind [@card_le_card _ (range (m + 1))]]
  erw [prod_pow_eq_pow_sum, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  gcongr; exact T.card_le_finrank_translatesIn P.2 P.1 (by simp [one_apply]) fun i hi y γ _ β hβ e ↦
    (mem_filter.1 hi).2 ((e.dvd_mul_right.1 (h0 ..)).trans (pow_dvd_pow _ hβ.le))
  have hφ := congr($e *ᵥ P.2 *ᵥ diagonal t' *ᵥ K.2 *ᵥ j)
  simp [← mul_assoc (diagonal t), ← ht, ← smul_one_eq_diagonal] at hφ
  rw [mem_span_singleton, ← mul_dvd_mul_iff_left (pow_ne_zero x T.w_ne_zero), ← pow_add, ←
    smul_eq_mul, ← Pi.smul_apply, ← mulVec_smul, ← Pi.smul_comp, ← hφ, ← mulVec_mulVec, hJ,
    mulVec_mulVec, Commute.left_comm, ← map_mul, ← mulVec_mulVec, mulVec_diagonal]
  set F := _ ∘ _
  let ω y := T.deepIndicator r y - T.excessWeight i a r y / 2
  choose l L g G using fun γ ↦ @Nat.exists_not_and_succ_of_not_zero_of_exists (fun l ↦ ∃ g, ¬T.w ^
    l ∣ (T.letterRep n g *ᵥ F) γ ∨ ⌈x - (exponentOf γ).weight ω⌉₊ < l) (by simp) ⟨_, 1, .inr .refl⟩
  let ⟨γ, H⟩ := (@Finite.exists_min _ _ _ ⟨β⟩ _ fun γ ↦
    l γ + (exponentOf γ).weight ω).imp fun _ M g δ ↦
    (pow_dvd_pow _ (Nat.ceil_le.2 (sub_le_iff_le_add.2 (M δ)))).trans (by_contra (L δ ⟨g, .inl ·⟩))
  have := (G γ).imp_left fun hg ↦ And.intro (fun d : _ ≤ x ↦ hg (by
    grw [← mul_dvd_mul_iff_left (pow_ne_zero _ T.w_ne_zero), ← @hf (_ ^ x), ← pow_add, ← d]
    simp [hφ, -mulVec])) (T.root_lemma i ha.ne 0 ω _ (f := polyOfCoeffs (T.letterRep n (g γ) *ᵥ F))
    (fun g _ ↦ by simpa [↓polyAction_polyOfCoeffs, -mulVec] using
    (_root_.sum_mem fun _ _ ↦ monomial_mem_gaussFiltration (H ..)))
    (by simpa [coeff_sum]) rfl (by simp [ω, deepIndicator]; grind [excessWeight_mem_Icc]))
  grw [← H, ← pow_add, pow_dvd_pow]
  simp [← add_assoc, ω, depth, Finsupp.weight_eq_sum, mul_sub, mul_div, ← sum_div] at this h ⊢
  rify at *; grind [Nat.le_ceil]
  simp [commute_iff_eq, letterRep, diagonal_pow_depth]; congr! 3
  ext; simp [letterMatrix, -coe_units_inv]; clear * - hl; grind [hl _, inv_mem hl _,
    transpose_apply]
lemma _root_.exists_tensor_dual ι σ R [Fintype ι] [CommRing R] : ∃ S :
    MultilinearMap R (fun _ : ι ↦ Dual R (MvPolynomial σ R)) (Dual R (MvPolynomial _ R)), ∀ l
    (f : _ → _), S l (∏ j, rename (j, ·) (f j)) = ∏ j, l j (f j) := ⟨((aeval fun (i, v) ↦
    singleAlgHom i (X v)).toLinearMap.dualMap ∘ₗ dualDistrib).compMultilinearMap (tprod R), by
  simp [aeval_rename, comp_def, ← comp_aeval, -singleAlgHom_apply]; simp [← tprod_prod]⟩
lemma exists_projector (hp : ¬IsUnit (T.p : O)) (ha : a + 1 = r.1) {ℓ} θ (e : ℓ + ℓ = N)
    (h : N * (n * (k * (ℓ + 2))) + n + k < T.P ^ ℓ) : ∃ b Z, (∀ F, Z *ᵥ F ∈ T.excessCond n a r
    (span {T.w ^ c}) θ) ∧ (∀ y ∈ T.excessCond n a r (span {T.w ^ c}) (θ - (4 * c + 2)), ∀ F,
    T.w ^ c ∣ y ⬝ᵥ (b * Z *ᵥ F) - T.p ^ ((k + k ^ 2) * (T.o₀ * N) * N) * y ⬝ᵥ F) ∧
    ∀ γ α β, b β * T.letterRep n (transposeGL γ) β α = b α * T.letterRep n γ α β := by
  obtain ⟨⟨S, hS⟩, q, b₀, hb, hx⟩ := exists_tensor_dual (ZMod N) (Fin k × Fin k) O, e ▸ Nat.pow_add
    .. ▸ Nat.mul_le_mul_right _ h, exists_invariant_diagonal_form (Fin k) T.prime hp (T.o₀ * N)
  let b (β : ZMod N → Monomials _ n) := ∏ s, b₀ (β s).1
  choose b' hb' using fun β ↦ (prod_dvd_prod_of_dvd _ _ fun s _ ↦
    Dvd.intro_left _ (hb _ (by grind [Monomials.degree_eq])).symm : b β ∣ _)
  have hν l f : S l f = ∑ ν ∈ f.support, f.coeff ν * ∏ j, l j (monomial (ν.curry j) 1) :=
    (congrArg _ f.as_sum).trans (by simp [← hS, monomial_eq, C_mul'])
  let Z := ((LinearMap.mapMatrixLinear O).flip
    (T.frobOperator r ℓ n T.frobGenericMatrix)).compMultilinearMap S
  have key i {m} (l : type_of% m) {g y F} (hg : g ∈ _) (e : ∀ j f, m j f = l j (conjSubst (T.ι j) g
    f)) (H : ∀ β _ ν, univ.prod _ = (0 : O) ∨ _) : y ⬝ᵥ Z m *ᵥ F ∈ span {T.w ^ c} := (by
    rw [(congr(.map _ $(show _ = _ ∘ₗ (aeval _).toLinearMap by
      ext; simp [single_eq_monomial, hν m, e]
      simp [← hS, monomial_eq])) : Z _ = .map (.map ((T.map C).frobOperator _ _ _ _) (eval₂Hom C
      fun (j, v) ↦ rename (j, ·) (conjSubst (T.ι j) g (X v)))) (S l)), frobOperator_map _ _ hg]
    simp_rw [letterRep_map, map_C_mul_mul_C, ← mulVec_mulVec, dotProduct_mulVec y, funext (hν l)]
    exact sum_mem fun β _ ↦ dite _ (mul_mem_right _ _) fun q ↦ mem_span_singleton.2 (.mul_left
      (dvd_sum fun _ _ ↦ .mul_right (dvd_sum fun ν _ ↦ (H β q ν).elim (· ▸ by simp) (And.elim
      (T.pow_dvd_coeff_conj_frobOperator ha i (by lia) (by lia) g (by simp [letterConj, conjSubst,
      linSubst, ← C_mul', map, map_mul,
      mul_apply, mul_assoc, mul_comm (X _)])) · |>.mul_right _)) _) _))
  choose κ h0 h2 h1 h3 using fun P j ↦ exists_mean (twoBlock k r) (T.ι j) T.prime hp (T.o₀ * N)
    (by grind) (D := N * (n * (k * ((ℓ + 2) * T.P ^ ℓ)))) (by grind [card_residueField])
    (T.indexWeight ℓ a r) (P ∨ θ - (2 * c + 1) < ·)
  use b, Z (-κ False + κ True) * diagonal b', fun F g hg β ⟨i, hi⟩ ↦ mulVec_mulVec F (Z _) _ ▸
    key (i - ℓ) (-κ False + κ True) hg (by simp [h0 _ _ g hg]) (by
    simp [one_apply]
    clear * - h1 h2 hi; grind [zero_mem]), fun y hy F ↦ ?_, ?ρ
  have := ?ρ
  let Y := (dotProductBilin O O (b * y) ∘ₗ toLin'.1.flip (b' * F)).compMultilinearMap Z
  have hz : Z (κ True) = (_ :
    O) • (T.frobOperator r ℓ n T.frobGenericMatrix).map
      (eval (vec (1 : Matrix (Fin k) (Fin k) O) ·.2)) :=
    ext fun _ _ ↦ by
    simp [Z, hν, eval_eq']; congr! 1
    simp [h1, T.degree_le_of_coeff_frobOperator (mem_support_iff.1 ‹_›), eval_monomial]
    rw [mul_left_comm]
  simp [↓T.frobOperator_map _ (one_mem _), frobOperator, one_apply,
    T.prime.ne_zero, ite_apply, ← diagonal.eq_1, @eq_comm (Fin k)] at hz hb'
  convert (mem_span_singleton.1 (sum_mem (Finset.induction (by simp) fun s t _ _ _ ↦ ?_))).trans
    (sub_eq_of_eq_add' ((Y.map_add_univ (-κ False) (κ True)).trans
    (sum_eq_add_sum_compl ∅ _))).symm.dvd
  simp [Y]; ac_rfl; simp [Y, hz, add_mul]; grind
  rw [piecewise_insert]
  refine neg_mem (Submodule.mem_span.1 (h3 _ s) (.comap (Y.toLinearMap _ s) (span _)) fun
    | _, ⟨u, h, γ, e, rfl⟩ => And.elim (key s (update (t.piecewise (-κ False) (κ True)) s γ) h) ?_)
  have z β := (mul_mem_left _ (b β) <|
    hy (transposeGL u⁻¹) (swap (inv_mem h · · ·.symm)) β ⟨s + ℓ, ·⟩)
  simp [update, piecewise, DFunLike.ite_apply] at z ⊢; clear * - z e h0 h2 h this; grind
  simp [letterRep, kroneckerPi, b, ← prod_mul_distrib]
  congr! 1; erw [mul_comm, letterMatrix]; bound
lemma hasType_twisted_hecke (hp : ¬IsUnit (T.p : O)) {r ℓ κ y z} (big : HeckeSizes T.P T.o₀ N k n r
  ℓ κ y z) {I M : Type} [Fintype H] [Fintype (_ ⧸ parahoric W (twoBlock k r))] [Fintype I]
  [AddCommGroup M] [Module O M] (f : (X → I → O) →ₗ[O] M) {Y : End O M} (src :
  X × _ ⧸ parahoric W (twoBlock k r) → X) (g : _ → GL (Fin k) W) (u : _ → GL H O) (J : I ≃ _ × H)
  (hs : Injective fun e ↦ ((src e, ↑(transposeGL (g e))⁻¹) : X × _ ⧸ parahoric W (twoBlock k r)))
  (hY : ∀ F, Y (f F) = f fun c i ↦ ∑ b, ∑ j, u (c, b) (J i).2 (J j).2 * (T.letterRep n (g (c, b)) *
  diagonal ((T.p : O) ^ T.depth k n r ·) * T.letterRep n b.out⁻¹ :) (J j).1 (J i).1 * F (src (c, b))
  j) m : HasType ↑T.p f.range m Y ((z + κ * m + y) * (Nat.card X * Nat.card I)) := by
  have ⟨_, _, _, _, e, h1, _⟩ := big
  set c := 2 * _ + 2
  let S := T.map (residue O)
  have ha : @Fin.val k ⟨r - 1, by lia⟩ + 1 = @Fin.val k ⟨r, by lia⟩ := by lia
  obtain ⟨hu, _, x, hm⟩ := (T.w_sq ▸ hp) ∘ .pow 2, CharP.of_eq_zero S.prime
    ((residue_eq_zero_iff _).2 hp), Finite.exists_le (T.depth k n r)
  obtain ⟨U, U', ⟨b, Z, hZ, hZ', hρ⟩, ⟨Q, d, R, hj, h₀, hR, hQ⟩, Q', d', R', j', h₁, hR', hQ'⟩ :=
    S.index_mul_finrank_excessCond_le ha big, S.sum_finrank_deepForms_le big x, T.exists_projector c
    hp ha y e h1, T.exists_depth_factorization c ha.le hm _ _ ((prodAssoc H ..).symm.surjective.comp
    (surjective_id.prodMap hs.bijective_of_finite.2)), T.exists_depth_factorization c ha.le hm (.map
    id (·.1)) (·.2.2.out⁻¹) (⟨prodAssoc H X _ ·, by simp⟩)
  obtain ⟨l, L, key⟩ := T.of_pairing Q (blockDiagonal (u · |>.2) ⊗ₖ Z * R'ᵀ) R
    (Q'ᵀ * blockDiagonal (u · |>.1) ⊗ₖ diagonal b) (T.w ^ _) (T.p ^ m) hR hu (fun i j ↦ by
    grw [← pow_succ, one_le_two]
    convert univ.dvd_sum fun y _ ↦ hZ' _ (hQ' (Pi.single i 1) y (by bound)) (R' j ⟨y, ·⟩)
    simp [← transpose_eq_one.2 hR', ← (_ ⊗ₖ _).mul_assoc, ← mul_kronecker_mul, w_sq,
      ← blockDiagonal_mul, mul_apply, diagonal, blockDiagonal_apply, one_apply, mul_assoc, pow_mul])
      fun v _ _ h x γ hγ β hβ e ↦ by simpa [← pow_succ, pow_dvd_pow_iff T.w_ne_zero hu, c, e,
      mem_span_singleton, Pi.smul_comp, -mulVec] using (Set.mem_of_eq_of_mem (congr($h
      ∘ (x, ·)).symm.trans (by
      rw [← mulVec_mulVec, ← (vec_bijective.2 (R'ᵀ *ᵥ _)).choose_spec, kronecker_mulVec_vec]; ext
      simp; rfl)) (sub_mem (hQ v x (by bound)) (hZ _)) γ hγ β hβ)
  let ε := .funCongrLeft O O ((((prodComm ..).trans (J.prodCongr (.refl X))).trans
    (prodAssoc ..)).trans (prodComm ..)) ≪≫ₗ .curry ..
  have := (IndexDvd.of_det_dvd (d'.det_transpose ▸ h₁) le_sup_left).comp le_top
    (key.comp le_top (.of_det_dvd h₀ le_sup_left))
  simp_rw [mul_left_comm, ← mul_pow, ← sq, pow_mul, w_sq, ← pow_mul, ← pow_add] at this
  refine ⟨by simp [hY], _, ?_, this.map (f ∘ₗ ε) (by simp) ?_⟩
  grw [← (by bound : c / 2 ≤ y)]
  simp [Subgroup.index, card_congr J, c, ← mul_sum] at L U U' ⊢; rify at L
  linear_combination (norm := linarith!) ↑m * L + card X * card H * (↑m * U + U')
  simp [← LinearMap.range_comp, -IsConcreteLE.le_iff]
  refine le_sup_of_le_left fun | _, ⟨F, rfl⟩ => ⟨ε ((b ·.2) * F), ?_⟩
  simp [hY]; erw [hj, j']; congr!
  simp [ε, ← J.symm.sum_comp, @sum_prod_type_right _ _ H, ← mulVec_mulVec, sq,
    mul_apply, blockDiagonal, diagonal, ← w_sq, mul_pow, ite_and]
  congr!; rw [sum_comm_cycle]; clear * - hρ; grind
end TwistingData
