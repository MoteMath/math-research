import Lib.General.Analysis.ZpowSum
import Lib.General.NumberTheory.Embeddings
noncomputable section
open NumberField Complex Polynomial InfinitePlace Module IntermediateField AddChar
instance (d : Nat.Primes) : Fact d.1.Prime := ⟨d.2⟩
variable {N} [NeZero N] (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]
def chiK : DirichletCharacter ℤ d := open Calc in quadraticChar _
lemma chiK_eq_legendreSym (n : ℕ) : chiK d n = legendreSym d n := by simp [chiK, legendreSym]
def quadTwist :=
  χ.changeLevel ⟨d, rfl⟩ * .changeLevel (by simp) ((chiK d).ringHomComp (algebraMap ..))
def entireL := ite (χ = 1) (DirichletCharacter.LFunctionTrivChar₁ N) χ.LFunction
def chowlaSelbergConst := .eulerMascheroniConstant - (logDeriv (entireL (@quadTwist 1 1 d _)) 1).re
variable (d n : ℕ) [NeZero n] {M : Type} [Field M] [CharZero M] {x y : M}
class PrimeSevenModEight extends Fact d.Prime where mod_eight : d % 8 = 7
attribute [local simp] neg_eq_self NeZero.ne NeZero.pos mul_pow RingOfIntegers.ext_iff
attribute [local simp ←] ofReal_pow
lemma totient_mul_totient_le_finrank [NeZero d] [NumberField M] (c : n.Coprime d) (hx : IsPrimitiveRoot x n) (hy : IsPrimitiveRoot y d) : d.totient * n.totient ≤ finrank ℚ M := by grind
  [n.totient_mul, c.lcm_eq_mul, hx.lcm_totient_le_finrank hy (cyclotomic.irreducible_rat (by simp))]
def QuadField := ℚ⟮I * √d⟯
namespace QuadField
@[simps! coe] def sqrtNegD : QuadField d := AdjoinSimple.gen ..
@[local simp] lemma sqrtNegD_sq : sqrtNegD d ^ 2 = -d := by aesop
lemma y7 : IsIntegral ℚ (I * √d) := .of_pow two_pos (by simp [isIntegral_natCast])
instance : NumberField (QuadField d) where
  to_finiteDimensional := adjoin.finiteDimensional (y7 d)
instance [PrimeSevenModEight d] : Fact (d % 4 = 3) := ⟨by grind [PrimeSevenModEight]⟩
variable [h : Fact (d % 4 = 3)]
instance : NeZero d := ⟨by grind [Fact]⟩
lemma r2 : X ^ 2 - C (-d : ℚ) = minpoly ℚ (I * √d) := minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime Fact.out (sq_nonneg · |>.not_gt <| by simp [·])) (by simp) (by monicity!)
lemma finrank_K : finrank ℚ (QuadField d) = 2 := adjoin.finrank (y7 d) ▸ r2 d ▸ natDegree_X_pow_sub_C
instance : IsTotallyComplex (QuadField d) := ⟨fun _ ↦ not_isReal_iff_isComplex.1 (by simpa [← map_pow] using sq_nonneg <| embedding_of_isReal · (sqrtNegD d))⟩
instance : Unique (InfinitePlace (QuadField d)) := ⟨⟨mk (val _).1⟩, (Fintype.card_le_one_iff.1 (by grind [finrank_eq_two_mul_card_infinitePlace, finrank_K]) · _)⟩
def embOfSqrt (e : y ^ 2 = -d) : QuadField d →ₐ[ℚ] M :=
  (adjoin.powerBasis (y7 d)).lift y (by simp [minpoly_gen, ← r2, e])
open Subalgebra Int Algebra Ideal ZMod
def nonempty_algHom_of_isPrimitiveRoot [Fact d.Prime] (hx : IsPrimitiveRoot x d) : QuadField d →ₐ[ℚ] M := embOfSqrt d (by rw [gaussSum_sq (MulChar.ne_one_iff.2 ⟨-1, _⟩) ((quadraticChar_isQuadratic
  _).comp (castRingHom _)) (zmodChar_primitive_of_primitive_root _ hx)] <;>
  simp [quadraticCharFun, exists_sq_eq_neg_one_iff, h.1])
@[simp] lemma b9 : 4 ∣ d + 1 := by grind [Fact]
instance : IsQuadraticExtension ℚ (QuadField d) := ⟨finrank_K d⟩
instance : IsCMField (QuadField d) := .ofCMExtension ℚ _
@[simp] lemma s11_d3 (y : QuadField d) : star y = starRingEnd ℂ y := map_star_complex (QuadField d).val y
@[simp] lemma d4 : star (sqrtNegD d) = -sqrtNegD d := by aesop
lemma abs_norm_eq_norm_sq (x : QuadField d) : |(norm ℚ x : ℝ)| = ‖x.1‖ ^ 2 := by simpa using!
  (prod_eq_abs_norm x).symm
lemma absNorm_span_eq_mul_star (y : 𝓞 (QuadField d)) : (span {y}).absNorm = y * star y := by ext; simp [← coe_norm_int, ← abs_norm_eq_norm_sq, ← cast_abs, mul_conj']
def c₀ : 𝓞 (QuadField d) := ⟨(1 + sqrtNegD d) / 2, X ^ 2 - X + (d.succ / 4).cast, by monicity!,
  by simp; grind [sqrtNegD_sq]⟩
@[simp] lemma f0 : c₀ d = (1 + sqrtNegD d) / 2 := rfl
@[simp] lemma s11_d8 : star (c₀ d) = 1 - c₀ d := by simp; ring
lemma c₀_mul_one_sub : c₀ d * (1 - c₀ d) = ↑((d + 1) / 4) := by simp; grind [sqrtNegD_sq]
abbrev sqrtNegDInt := 2 * c₀ d - 1
lemma sqrtNegDInt_sq : sqrtNegDInt d ^ 2 = -d := by simp [two_mul]
lemma different_eq_span_and_adjoin_c₀ [PrimeSevenModEight d] : differentIdeal ℤ _ = span {sqrtNegDInt d} ∧ ℤ[c₀ d] = ⊤ := differentIdeal_eq_span_of_dvd ℚ ((( isSimpleOrder_of_finrank (finrank_K d)).2 _).resolve_left ((·.le (subset_adjoin rfl)).mt fun ⟨_, e⟩ ↦ by simpa using congr(-($e + $e).1.im))) ((d.succ / 4).cast - X * (1 - X)) (by simp [ c₀_mul_one_sub]) (by simp [two_mul, add_sub]) (dvd_differentIdeal_of_mem_sq (p :=
  d) (by simp [span_singleton_pow, sqrtNegDInt_sq]))
end QuadField
end
open Ideal FiniteField Int NumberField ZMod legendreSym Ideal.Quotient IsDedekindDomain.HeightOneSpectrum
variable {F} [Field F] [NumberField F] {d p : ℕ} [hp : Fact p.Prime] {R} [CommRing R] [CharP R p] [PrimeSevenModEight d] (h2 : p ≠ 2) (φ : 𝓞 (QuadField d) →+* R) (w : FinPlace F)
variable (F p) in
lemma FinPlace.exists_natCast_mem : ∃ w : FinPlace F, ↑p ∈ w.1 := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 F).elim
  fun ⟨P, i, ⟨e⟩⟩ ↦ ⟨⟨P, i, (by simp [·, NeZero.ne] at e)⟩, by simpa using e.le⟩
attribute [local instance] Quotient.field
lemma FinPlace.charP_quotient (h : ↑p ∈ w.1) : CharP (_ ⧸ w.1) p := .of_eq_zero hp.1 (eq_zero_iff_mem.2 h)
protected lemma FinPlace.natCast_mem_iff_dvd (h : ↑p ∈ w.1) {n} : ↑n ∈ w.1 ↔ p ∣ n := by erw [← (w.charP_quotient h).1, eq_zero_iff_mem]
attribute [local instance] ZMod.algebra
lemma FinPlace.exists_q_eq_pow (h : ↑p ∈ w.1) : ∃ f, w.q = p ^ f ∧ ∀ n, f ∣ n ↔ ∀ x, Ideal.Quotient.mk w.1 x ^ p ^ n = Ideal.Quotient.mk _ x := have := w.charP_quotient h
  ⟨_, .symm (pow_finrank_eq_natCard p (_ ⧸ w.1)), by simp [AlgHom.ext_iff, mk_surjective.forall, ← orderOf_frobeniusAlgHom, coe_frobeniusAlgHom, orderOf_dvd_iff_pow_eq_one]⟩
lemma QuadField.map_sqrtNegDInt_sq : φ (sqrtNegDInt d) ^ 2 = -d := by simp [↓← map_pow, sqrtNegDInt_sq]
omit [Fact p.Prime] in
lemma QuadField.chiK_two : p = 2 → chiK d p = 1 := by grind [chiK_eq_legendreSym, PrimeSevenModEight, at_two, χ₈_nat_eq_if_mod_eight]
lemma QuadField.legendreSym_eq_pow_of_sq_eq_neg (h2 : p ≠ 2) {x : R} (e : x ^ 2 = -d) : chiK d p = x ^ (p - 1) := by simpa [*, chiK_eq_legendreSym, neg_one_pow_eq_ite, quadratic_reciprocity' h2, neg_pow (d : R), pow_mul, ← p.two_mul_odd_div_two, hp.1.mod_two_eq_one_iff_ne_two, (by grind [PrimeSevenModEight] : d ≠ 2 ∧ Odd (d / 2)) ] using congr((-1) ^ (p / 2) * (cast $(eq_pow p d) : R))
include h2 in
lemma QuadField.eq_map_c₀_pow_iff n x : x = φ (c₀ d) ^ p ^ n ↔ 2 * x - 1 = chiK d p ^ n * φ (sqrtNegDInt d) := by rw [show _ * φ _ = φ (sqrtNegDInt d) ^ p ^ n by induction n <;> simp_all [pow_succ', pow_mul, mul_assoc, ← iterateFrobenius_def, ← pow_sub_one_mul hp.1.ne_zero, ← legendreSym_eq_pow_of_sq_eq_neg h2 (map_sqrtNegDInt_sq φ), -map_sub]]; simp [← iterateFrobenius_def, IsUnit.mul_right_inj, map_ofNat, *, CharP.isUnit_ofNat_iff, p.prime_dvd_prime_iff_eq, Fact.out]
abbrev primeNorm (d p : ℕ) [Fact d.Prime] := ite (chiK d p = -1) (p ^ 2) p
noncomputable def nonsplitWeight (d p : ℕ) [Fact d.Prime] : ℝ := (1 + chiK d p ^ 2) / 2 / (primeNorm d p - 1)
lemma chiK_cases (d p : ℕ) [hp : Fact p.Prime] [Fact d.Prime] : p = d ∧ chiK d p = 0 ∨ p ≠ d ∧ (chiK d p = 1 ∨ chiK d p = -1) := by simp [chiK, quadraticCharFun]; grind [prime_ne_zero, natCast_self d]
variable {q : ℤ} {o s d p : ℕ} [Fact (d % 4 = 3)] [hp : Fact p.Prime] (w : FinPlace (QuadField d))
lemma two_pow_dvd_or_of_pow_eq_one (ho : 0 < o) (h : (q : ZMod (2 ^ (s + 1))) ^ o = 1) : 2 ^ s ∣ (q - 1) * o ∨ 2 ^ s ∣ (q + 1) * o := by
  have := (intCast_eq_intCast_iff_dvd_sub 1 (q ^ (o * 2)) (2 ^ s.succ)).1 (by simp [h, pow_mul])
  cases (by grind [even_pow, → Even.trans_dvd] : 4 ∣ q - 1 ∨ 4 ∣ q - -1) <;>
   have := two_pow_sub_pow' (o * 2) ‹_› (by lia) <;> simp_all [pow_dvd_iff_le_emultiplicity, emultiplicity_mul prime_two, ← add_assoc, finiteMultiplicity_iff]
lemma two_pow_le_of_pow_eq_one (h1 : 1 < q.natAbs) {o s} (ho : 0 < o) (h : (q : ZMod (2 ^ (s + 1))) ^ o = 1) : 2 ^ s ≤ (q.natAbs + 1) * o := by cases two_pow_dvd_or_of_pow_eq_one ho h <;> zify <;>
  apply (le_abs_of_dvd _ ‹_›).trans <;> simp [*] <;> grind
lemma QuadField.q_eq_iff_legendreSym_ne_neg_one (hw : ↑p ∈ w.1) [PrimeSevenModEight d] : w.q = p ↔ chiK d p ≠ -1 := by
  obtain ⟨c, ⟨⟩⟩ := w.charP_quotient hw, w.exists_q_eq_pow hw, chiK_cases d p; simp [*, hp.1.pow_eq_iff, ← Nat.dvd_one]
  apply Iff.trans ⟨(· (c₀ d)), fun _ ↦
   (by induction (different_eq_span_and_adjoin_c₀ d).2.ge (x := ·) ⟨⟩ using
   Algebra.adjoin_induction <;> simp_all [← frobenius_def])⟩
  obtain rfl | h := eq_or_ne p 2; grind [chiK_two rfl, PrimeSevenModEight, c.1, congr(Ideal.Quotient.mk w $(c₀_mul_one_sub d)), map_natCast]; erw [← pow_one p, eq_comm, eq_map_c₀_pow_iff h, eq_comm, mul_left_eq_self₀, ← sq_eq_zero_iff, map_sqrtNegDInt_sq]; aesop (add simp [_root_.neg_one_eq_one_iff, ringChar.eq, (c.1), Nat.dvd_prime, Fact.out])
lemma QuadField.prime_inert_or_eq_mul (hw : ↑p ∈ w.1) : ∃ J, (∀ u, ↑p ∈ u.1 ↔ u = w ∨ u = J) ∧ (w = J ∧ w.q = p ^ 2 ∨ w.q = p ∧ J.q = p ∧ span {↑p} = w.1 * J.1) :=
   (dvd_span_singleton.2 hw).elim fun J _ ↦ by by_cases J = ⊤
  <;> (have := by simpa [*, ← Nat.cast_mul, sq p ▸ hp.1.mul_eq_prime_sq_iff, w.2.1] using absNorm_span_eq_mul_star d p) <;> [use w; use (ofPrime (irreducible_of_irreducible_absNorm
  (this.2 ▸ hp.1)).prime)] <;> generalize_proofs <;> simp_all [← dvd_span_singleton, prime, ofPrime, sq, Prime.dvd_mul, prime_dvd_prime_iff_eq, IsDedekindDomain.HeightOneSpectrum.ext_iff]
