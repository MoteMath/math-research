import Lib.GaloisRep.Hilbert90.UnitaryHilbert90
import Lib.DiscreteSeries.Bruhat.EichlerMaps
import Lib.Adelic.Adeles.AdelicModulus
noncomputable section
section
open Matrix NumberField MatMul InnerProductSpace
variable {E n k : Type*} [Field E] [NumberField E] [IsCMField E] [Fintype n]
  {R : Type _} [CommRing R] {O : Subring R} {X : Matrix n k R}
lemma IsPrimitiveMatrix.exists_map_subtype_eq : IsPrimitiveMatrix O X → ∃ Y, HasLeftInv Y ∧
  .map Y O.subtype = X | ⟨a, _, b, e⟩ => ⟨(⟨_, a · ·⟩),
  ⟨(⟨_, b · ·⟩), map_injective O.subtype_injective (Matrix.map_mul.trans (by simpa))⟩, rfl⟩
lemma isPrimitiveMatrix_iff {g} : IsPrimitiveMatrix O g ↔ ∃ x ∈ intGL n O, x.1 = g :=
  ⟨fun ⟨a, _, b, e⟩ ↦ ⟨(.mkOfMulEqOne _ _
  e)⁻¹, mem_intGL.2 ⟨a, b⟩, rfl⟩, fun ⟨x, h, e⟩ ↦ e ▸ (mem_intGL.1 h).imp_right (⟨_, ·, x.4⟩)⟩
variable [Fintype k] [StablyUnram E] {X Y : Matrix n k (𝔸f E)}
lemma exists_isUnit_sub_star_Ohat : ∃ z : Ô E, IsUnit (z - star z) := ‹StablyUnram
  E›.exists_isUnit_sub_star.imp' (algebraMap ..) fun _ ↦ Eq.subst (by aesop) ∘ .map (algebraMap ..)
lemma witt_Ô (hX : IsPrimitiveMatrix (Ô E) X) (hY : IsPrimitiveMatrix (Ô E) Y) (h : Xᴴ * X =
  Yᴴ * Y) : ∃ g ∈ Kf E n, g.1.1 * X = Y := by
  have A a x y : ∃ c : Matrix n n (Ô E), IsUnit (a + (1 - a * x) * c * (1 - y * a)) := by
    obtain ⟨p, _, q, _, d, rfl⟩ := isValuationPair_Ohat.top.smith_normal_form a
    let e := diagonal (Subtype.mk _ <| idem_mem_Ô {w | (reduceAt w ∘ d) · = 0})
    refine ⟨p * e * q, isUnit_of_mul_isUnit_left (y := q⁻¹ * (1 + e * q * y * p * diagonal d))
      (isUnit_of_mul_isUnit_right (x := (1 + diagonal d * q * x * p * e) * p⁻¹) ?_)⟩
    simp [isUnit_iff_isUnit_det, eq_iff_le_not_lt, mem_Ô.1, ← reduceAt_eq_zero,
      mul_assoc, add_assoc, sub_eq_add_neg, RingHom.map_det, ↓map_add, ↓map_neg, e, ← mul_assoc
      (diagonal _) (diagonal _), Finset.prod_eq_zero_iff, ite_eq_right_iff.2, idem_mul_self]
    grind
  obtain ⟨⟨X, ⟨L, l⟩, ⟨⟩⟩, Y, ⟨M, m⟩, ⟨⟩⟩ := hX.exists_map_subtype_eq, hY.exists_map_subtype_eq
  have : Xᴴ * X = Yᴴ * Y := by ext; simp_all [← ext_iff, mul_apply]
  have ⟨c, a, e⟩ := A (Y * L + Mᴴ * Xᴴ * (1 - X * L)) (Lᴴ * Yᴴ) (X * M)
  refine (exists_fixed_orthonormal_frame isProfiniteRing_intAdeles isTameAtLevel_one rfl
    exists_isUnit_sub_star_Ohat.choose_spec ?_ (star a * a).isUnit (by
    simp [star]) rfl).elim fun T ⟨_, _, _, t⟩ ↦ ⟨U.map _ ?_ ?_ (U.of isUnit_one (a.1 * T) (by simpa
    [star] using t)), ⟨_, rfl⟩, Matrix.map_mul.symm.trans ?_⟩ <;> simp [*, star, -Matrix.mul_sub]
lemma witt_Ohat_of_orthonormal (h : Xᴴ * (1 : Matrix n n (𝔸f E)) * X = 1) (h' : Yᴴ * (1 :
  Matrix n n (𝔸f E)) * Y = 1) (hX : IsIntMatrix (Ô E) X) (hY : IsIntMatrix (Ô E) Y) : ∃ g ∈ Kf E n,
  g.1.1 * X = Y := by apply witt_Ô ⟨_, _, _, h⟩ ⟨_, _, _, h'⟩ <;> simp_all [star_mem_Ô, IsIntMatrix]
lemma exists_orthonormal_mul {n k α} [Fintype n] [Fintype k] [LinearOrder α]
    (wt : k → α) {X : Matrix n k ℂ} : HasLeftInv X → ∃ b : GL k ℂ, b.1.BlockTriangular wt ∧
      (X * b.1)ᴴ * (X * b.1) = 1 | ⟨L, _⟩ => let B := PiLp.basisFun 2 ℂ k
  let := LinearOrder.lift' (toLex ∘ Function.prod wt embeddingToCardinal) (by aesop_cat)
  let := (monoEquivOfFin k rfl).symm.locallyFiniteOrderBot
  let := NormedAddCommGroup.induced _ _ X.toEuclideanLin (.of_comp (f := (L *ᵥ ·.1)) (by aesop_cat))
  let := induced X.toEuclideanLin
  have := (transpose_mul ..).symm.trans (gram_eq_one_iff_orthonormal.2
    (gramSchmidtNormed_orthonormal B.linearIndependent))
  ⟨(.mkOfMulEqOne _ _ ((Matrix.mul_assoc ..).trans this))⁻¹, fun _ _ _ ↦
    mul_eq_zero_of_right _ (gramSchmidt_triangular (by tauto) B), this⟩
variable {E n : Type _} [Field E] [NumberField E] [Fintype n] [IsCMField E] [StablyUnram E]
lemma exists_orthonormal_Ô {b} : IsUnimodular (Ô E) b → ∃ k ∈ intGL n (Ô E), k.1ᴴ * b * k.1 = 1
  | ⟨h, _, ⟨x, rfl⟩, c⟩ => c ▸ (exists_fixed_orthonormal_frame isProfiniteRing_intAdeles
    isTameAtLevel_one rfl exists_isUnit_sub_star_Ohat.choose_spec (by
    simp) x.isUnit (by ext; simp_all [← ext_iff]) rfl).elim fun _ ⟨_, _, _, e⟩ ↦ ⟨_, ⟨
    (.mkOfMulEqOne _ _ e)⁻¹, rfl⟩, by erw [← map_conjTranspose_mul_mul, e] <;> simp⟩
lemma exists_norm_eq_Ô {u} (hu : star u = u) (h : ∀ w, Valued.v (u w) = 1) : ∃ x : (Ô E)ˣ,
  star x.1.1 * x = u := by simpa [Finset.range, Subtype.ext_iff] using! ((IsTameAtLevel.of_skew
  (by bound) exists_isUnit_sub_star_Ohat.choose_spec (starRingEnd _).map_one).exists_norm
  (.inr isProfiniteRing_intAdeles) (isUnit_Ô (x := ⟨u, by grind [mem_Ô]⟩).2 h) (Subtype.ext hu))
end
open Matrix Sgn
attribute [local simp] Prod.ext_iff Space.gram_point funext_iff mem_U signMatrix stdForm
section
variable {m n R : Type*} [Fintype m] [Fintype n] [CommRing R] [StarRing R] {l : Type _} [Fintype l]
  (e : m ⊕ l ≃ n) (s : n → ℤˣ) {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]
  {t : m → ℤˣ}
@[simps! apply_val] def blockGL : GL m R × GL n R →* GL (m ⊕ n) R := by use! fun g ↦
  ⟨fromBlocks g.1 0 0 g.2, fromBlocks ↑g.1⁻¹ 0 0 ↑g.2⁻¹, ?_, ?_⟩ <;> aesop
omit [Fintype m] [Fintype n] in
lemma signMatrix_sum s t : fromBlocks (signMatrix s) 0 0 (signMatrix t) =
  signMatrix (n := m ⊕ n) (s ⊕ᵥ t) := by simp
omit [Fintype n] in
@[simp] lemma signMatrix_neg : signMatrix (-s) = -signMatrix s := by simp
@[simps! apply_val] def reindexGL (e : m ≃ n) :
    GL m R ≃* GL n R := Units.mapEquiv (reindexRingEquiv R e).toMulEquiv
def U.sum {J : Matrix m m R} {J' J''} (h : fromBlocks J 0 0 J' = J'') : U J × U (n := n) J' →* U
    J'' := (blockGL.comp ((U J).subtype.prodMap (U J').subtype)).codRestrict _ (by aesop)
abbrev U.blockSumOne := sum (@fromBlocks_one' m n R _ _)
def U.reindex (e : m ≃ n) {J : Matrix m m R} {J'} (h : J.submatrix e.symm e.symm = J' := by simp) :
    U J ≃* U J' := ⟨(reindexGL e).subtypeEquiv (h ▸ by simp [← ext_iff, reindex_equiv e]), by simp⟩
def U.block := (reindex (J' := 1) e).toMonoidHom.comp (blockSumOne (R := R))
@[simp] lemma U.block_val h : (block (R := R) e h).1.1 = (fromBlocks h.1 0 0 h.2).submatrix e.symm e.symm := rfl
variable {m n : Type*} [Fintype m] [Fintype n] {s : n → _} {t : m → ℤˣ} (e : n ≃ m)
  (h : s ∘ e.symm = t) (g : G E s)
def G.sum : G E s × G E t →* G E (s ⊕ᵥ t) :=
  .prod (.mk' (fun g w ↦ U.sum (signMatrix_sum ..) (g.1.1 w, g.2.1 w))
  (by simp [← map_mul, -signMatrix])) ((U.sum (by simp)).comp (.prodMap (.snd ..) (.snd ..)))
@[simp] lemma G.mat_sum g : (sum g : G E (s ⊕ᵥ t)).mat = g.1.mat.fromBlocks 0 0 g.2.mat := by bound
def G.neg : G E s ≃* G E (-s) := .prodCongr
    (.piCongrRight fun _ ↦ .subgroupCongr (by simp [U, -signMatrix])) (.refl _)
omit [NumberField.IsCMField E] [Fintype m] [Fintype n] in
lemma stdForm_sum : fromBlocks (stdForm E s) 0 0 (stdForm E t) = stdForm E (s ⊕ᵥ t) := by simp
lemma gram_mkAdelicGL {E : Type*} [Field E] [CMType E]
    {J a b} (ha : ∀ w, (a w).1ᴴ * map J (Φ w) * (a w).1 = signMatrix s)
    (hb : b.1ᴴ * J.map (↑) * b.1 = 1) : (mkAdelicGL (a, b)).1ᴴ * J.map toAdele * (mkAdelicGL (a,
  b)).1 = stdForm E s := by apply matrix_ext_𝔸 <;> simpa [↓Matrix.map_mul]
@[simp] lemma G.mat_neg : (neg g).mat = g.mat := by ext <;> rfl
def G.reindex : G E s ≃* G E t := toUnitary.trans ((U.reindex e (h ▸ by simp)).trans toUnitary.symm)
@[simp] lemma G.mat_reindex : (reindex e h g).mat = g.mat.submatrix e.symm e.symm := rfl
def Weil.normNegOne [StablyUnram E] :
  (Ô E)ˣ := have e := exists_norm_eq_Ô (u := -1) (by simp) (by simp)
  .mkOfMulEqOne e.choose (-star e.choose.1) (by ext1; simp; grind)
@[simp] lemma star_normNegOne_mul_self [StablyUnram E] :
    star Weil.normNegOne.1.1 * Weil.normNegOne.1.1 = (-1 : 𝔸f E) := by simp [Weil.normNegOne]; grind
variable (E) [StablyUnram E]
def normNegOneIdele : (𝔸 E)ˣ := Weil.normNegOne.map (.prod 1 (Ô E).subtype.1)
end
variable (E : Type*) [Field E] [CMType E] {m n : Type*} [Fintype m] [Fintype n] {s : n → _}
  {t : m → ℤˣ} (e : n ≃ m) (h : s ∘ e.symm = t) (g : G E s) (V : Space E n s)
  (e : n ≃ m) (h : s ∘ e.symm = t) [StablyUnram E] (W : Space E m t)
def signedSpace s : Space E n s := ⟨diagonal (s ·), diagGL fun i ↦
  ite (s i = 1) 1 (normNegOneIdele E), by simp_all [apply_ite, ite_apply, normNegOneIdele]⟩
namespace Space
variable {E}
def sum : Space E _ (s ⊕ᵥ t) := ⟨V.J.fromBlocks 0 0 W.J, blockGL (V.x, W.x), by simp⟩
def reindex : Space E m t := ⟨V.J.reindex e e, reindexGL e V.x, h ▸ by simp [← submatrix_map]⟩
def neg : Space E n (-s) := ⟨-V.J, normNegOneIdele E • V.x, by
  simp [Matrix.map_neg, normNegOneIdele, Units.smul_def,
    ← diagonal_smul]; grind [star_normNegOne_mul_self]⟩
def move (g : G E s) : Space E n s := ⟨_, _, gram_mul_of_gram_eq V.3 g.toUnitary.2⟩
attribute [simps J] signedSpace sum reindex neg move
