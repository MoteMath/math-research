import Lib.General.Measure.SubgroupIntegral
import Lib.Adelic.Adeles.AdditiveCharDefs
import Lib.General.LinearAlgebra.ValuedMatrix
noncomputable section
open NumberField MeasureTheory Measure Matrix GeneralLinearGroup WithZero Filter Valued
section
variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] (w : FinPlace E)
lemma matrix_ext_evalAt {m n} {M N : Matrix m n (𝔸f E)} (h : ∀ u, M.map (evalAt u) = N.map (evalAt u)) : M = N := by ext; simp_all [← ext_iff]
@[simps!] def evalInf (v : InfinitePlace E) : 𝔸 E →+* ℂ := (Pi.evalRingHom _ v).comp (.fst ..)
lemma matrix_ext_𝔸 {m n} {M N : Matrix m n (𝔸 E)} (h₁ : ∀ w, M.map (evalInf w) = N.map (evalInf w)) (h₂ : M.map (RingHom.snd ..) = N.map (RingHom.snd ..)) : M = N := by ext <;> simp_all [← ext_iff]
def locGL : GL n (LocField w) →* GL n (𝔸f E) := Units.map ⟨⟨fun g ↦ 1 + (g - 1).map (singleAdele w), by simp⟩, by noncomm_ring [← Matrix.map_mul, ← Matrix.map_add, map_add, implies_true]⟩
@[simp] lemma evalAt_locGL g : (locGL w g : GL n _).map (evalAt w) = g := by
 ext : 2; simp [locGL, -evalAt_apply]; simp
@[simp] lemma evalAt_locGL_of_ne {u w : FinPlace E} (h : u ≠ w) (g : GL n _) : (locGL w g).map (evalAt u) = 1 := by ext; simp [locGL, -evalAt_apply]; aesop
lemma GL_ext_evalAt {a b : GL n (𝔸f E)} (h : ∀ u, a.map (evalAt u) = b.map (evalAt u)) : a = b := Units.ext (matrix_ext_evalAt (congr($(h ·))))
variable {R : Type _} [CommRing R] [TopologicalSpace R] {O : Subring R}
lemma isOpen_intGL (h : @IsOpen R _ O) : (intGL n O).IsOpen := Eq.subst (by ext; exact mem_intGL.symm) (O.matrix.isOpen_units h.matrix)
variable [IsTopologicalRing R]
lemma isCompact_intGL [T2Space R] (h : @IsCompact R _ O) : IsCompact (SetLike.coe (intGL n O)) := Eq.subst (by ext; exact mem_intGL.symm) (O.matrix.units_isCompact h.matrix)
lemma isOpen_congruenceGL {m} {e : m → n} [Finite m] {M : Submodule O R} (h : @IsOpen R _ O) (k : @IsOpen R _ M) : (congruenceGL M e).IsOpen := (isOpen_intGL h).and k.matrix.preimage_of_continuous
lemma eventually_congruenceGL_subset {ι l s} {M : ι → Submodule O R} (h : @Tendsto _ (Set R) (M ·) l (nhds 0).smallSets) (k : s ∈ nhds (1 : GL n R)) : ∀ᶠ i in l, ∀ g ∈ congruenceGL (M i) id, g ∈ s := have H : (l.bind fun i ↦ 𝓟 (congruenceGL (M i) id).carrier).Tendsto (·.1) (nhds 1) := tendsto_sub_nhds_zero_iff.1 (tendsto_pi_nhds.2 fun _ ↦ tendsto_pi_nhds.2 fun _ _ u ↦ l.3 (h (mem_lift' u)) fun _ a _ b ↦ a (b.2 ..)); (H.prodMk_nhds fun _ u ↦ l.3 (H (MulOpposite.continuous_op.tendsto _ u)) fun _ a ↦ (@a ·⁻¹ ∘ by simp)).le_comap ((nhds_induced ..).ge k)
variable (n)
abbrev Kw : Subgroup (GL n (LocField w)) := intGL n (LocInt w).1
def basicDoubleCoset (j : ℕ) := {g : GL n (LocField w) | (∀ a b, v (g a b) ≤ 1) ∧ (∀ a b, v (g⁻¹ a b) ≤ exp 1) ∧ v g.1.det = exp (-↑j)}
variable (E) [IsCMField E]
@[instance_reducible] def Gf := ↥(U (1 : Matrix n n (𝔸f E))) deriving Group, TopologicalSpace, MeasurableSpace, DistribMulAction _ (n → 𝔸f E), PolishSpace, CoeOut _ (GL n (𝔸f E)), CoeOut _ (Matrix n n (𝔸f E)), SecondCountableTopology
instance : ContinuousSMul (Gf E n) (n → 𝔸f E) := ⟨.matrix_mulVec (by fun_prop) continuous_snd⟩
variable [IsEmpty n] in deriving instance Subsingleton for Gf E n
@[simp] lemma Gf.coe_mul (g k : Gf E n) : (g * k).1 = g.1 * k.1 := rfl
@[simp] lemma Gf.coe_mul' (g : Gf E n) (k : U 1) : (g * k).1 = g.1 * k.1 := rfl
@[simp] lemma Gf.coe_inv (g : Gf E n) : g⁻¹.1 = g.1⁻¹ := rfl
@[simp] lemma Gf.coe_one : (1 : Gf E n).1 = 1 := rfl
@[simp] lemma Gf.subtype_apply g : DFunLike.coe (F := Gf E n →* _) (U 1).subtype g = g.1 := rfl
@[simp] lemma Gf.codRestrict_apply {M} [Monoid M] (f : M →* _) h x : DFunLike.coe (F := M →* Gf E n) (f.codRestrict (U 1) h) x = ⟨f x, h x⟩ := rfl
@[ext] lemma Gf.val_ext {g k : Gf E n} : g.1 = k → g = k := by simp
def Kf : Subgroup (Gf E n) := (intGL n (Ô E)).subgroupOf _
variable {n} (s : n → ℤˣ)
abbrev GInf := InfinitePlace E → USign s
abbrev G := GInf E s × Gf E n
instance : Coe (Gf E n) (G E s) := ⟨(1, ·)⟩
def stdForm := diagonal (α := 𝔸 E) fun i ↦ (fun _ ↦ s i, 1)
variable {E s} {u w : FinPlace E} (hw : w.IsSplit)
@[simp] abbrev HasLevel {W S} [Membership _ S] (F : G E s → W) (K : S) := ∀ k ∈ K, ∀ g, F (g * (1, k)) = F g
def heckeGL {A W} [CommSemiring A] [AddCommMonoid W] [Module A W] (π : Representation A (GL n (LocField w)) W) j := heckeFun π (Kw ..) ((basicDoubleCoset n w j).indicator 1)
lemma evalAt_star_GL h (g : GL n _) : (map (evalAt w) (star g)).1 = ((map (evalAt u) g).1.map (conjLoc h))ᵀ := by ext1; apply adeleMap_apply
@[local simp] lemma evalAt_star_locGL (h : star u ≠ w) (g : GL n _) : (star (locGL w g)).map (evalAt u) = 1 := by ext1; simp_all [evalAt_star_GL (star_star u)]
def Gf.atPlace (w : FinPlace E) : Gf E n →* GL n (LocField w) := .comp (map (evalAt w)) (U 1).subtype
def atSplit : GL n (LocField w) →* Gf E n := by
 refine .mk' (fun g ↦ ⟨locGL w g * star (locGL w g⁻¹), Units.ext_iff.1 (?_ : star (_ : GL n _) *
   1 * _ = 1)⟩) fun _ _ ↦ Subtype.ext ?_ <;> exact GL_ext_evalAt (by by_cases · = w <;> aesop)
@[simp] lemma atPlace_atSplit (g : GL n _) : (atSplit hw g).atPlace w = g := by simp_all [Gf.atPlace, atSplit]
variable (n) (S : Set (FinPlace E))
def Kf.map {S} [CommRing S] (f : Ô E →+* S) : Kf E n →* GL n S := (intGL.map f).comp ((U 1).subtype.subgroupComap _)
def Gf.supportedOn := ⨅ w, ⨅ _ : w ∉ S ∧ star w ∉ S, (atPlace (n := n) w).ker
def localLevel (K := fun w : FinPlace E ↦ Kw n w) : Subgroup (Gf E n) := by
 use! {g | ∀ w ∈ S, g.atPlace w ∈ K w} <;> simp_all [mul_mem]
def Gf.trivialOn := ⨅ w ∈ S, (atPlace (n := n) w).ker
variable {n S} (w) (g k : G E s) {K : Subgroup (Gf E n)}
def Kf.reduceAt := map n (_root_.reduceAt w)
lemma mem_localLevel {K g} : g ∈ localLevel n S K ↔ ∀ w ∈ S, g.atPlace w ∈ K w := .rfl
lemma mem_Kf {g} : g ∈ Kf E n ↔ ∀ i j, g.1 i j ∈ Ô E := mem_intGL.trans (U.inv_val_eq_conjTranspose g ▸ by simp_all [star_mem_Ô])
lemma isOpen_Kf : (Kf E n).IsOpen := (isOpen_intGL isOpen_Ô).preimage_val
lemma isCompact_Kf : IsCompact (SetLike.coe (Kf E n)) := (isCompact_intGL isCompact_Ô).preimage_val (isClosed_U _)
class IsLevel K where
 le : K ≤ Kf E n
 isOpen : K.IsOpen
instance : IsLevel (Kf E n) := ⟨le_rfl, isOpen_Kf⟩
abbrev stdLevelIndex K := Subgroup.relIndex K (Kf E n)
@[simps! apply_val] def mkAdelicGL : (InfinitePlace E → GL n ℂ) × GL n (𝔸f E) →* GL n (𝔸 E) := .toHomUnits (by use! fun g ↦ of fun i j ↦ ((g.1 · i j), g.2 i j) <;>
 simp_all [entrywise, ← prod_mk_sum, funext_iff, apply_ite])
def G.toUnitary : G E s ≃* U (stdForm E s) where
 toFun g := ⟨mkAdelicGL (_, g.2), by apply matrix_ext_𝔸 <;> simp [stdForm,
         ↓Matrix.map_mul, -mul_one, -Matrix.mul_one]; exacts [(g.1 · |>.2), g.2.2]⟩
 invFun g := by refine (fun w ↦ U.map (evalInf w) ?_ ?_ g, U.map (.snd ..) ?_ ?_ g) <;>
   simp [stdForm, signMatrix]
 map_mul' _ _ := Subtype.ext (.symm (map_mul ..).symm)
@[local simp] def G.mat := g.toUnitary.1.1
@[simp] lemma G.mat_fst i j w : (g.mat i j).1 w = (g.1 w).1 i j := rfl
@[simp] lemma G.mat_snd i j : (g.mat i j).2 = g.2.1 i j := rfl
@[simp] lemma G.mat_one : mat (1 : G E s) = 1 := by simp
@[simp] lemma G.mat_mul : (g * k).mat = g.mat * k.mat := by simp
@[fun_prop] lemma G.continuous_mat : Continuous (mat : G E s → _) := by
 simp +unfoldPartialApp [toUnitary, mkAdelicGL]; fun_prop
instance : PolishSpace (GL n (𝔸f E)) where
deriving instance LocallyCompactSpace, BorelSpace, IsTopologicalGroup for Gf E n, G E s
lemma IsLevel.isCompact [h : IsLevel K] : IsCompact K.carrier := isCompact_Kf.of_isClosed_subset (K.isClosed_of_isOpen h.2) h.1
instance [h : IsLevel K] : CompactSpace K := h.isCompact.compactSpace
instance : MeasureSpace (Gf E n) := ⟨haarMeasure ⟨⟨_, isCompact_Kf⟩, by simp [isOpen_Kf.interior_eq]⟩⟩
instance : (@volume (Gf E n) _).IsHaarMeasure := isHaarMeasure_haarMeasure _
@[simp] lemma volume_Kf : volume (SetLike.coe (Kf E n)) = 1 := haarMeasure_self
end
attribute [local simp] evalAt_star_locGL
attribute [local simp] G.mat
variable (E : Type*) [Field E] [CMType E] {n : Type*} [Fintype n] {s : n → ℤˣ}
structure Space n [Fintype n] s where
 J : Matrix n n E
 x : GL n (𝔸 E)
 gram_point : x.1ᴴ * J.map toAdele * x.1 = stdForm E s
namespace Space
variable {E} (V : Space E n s)
def toRatCoords := G.toUnitary.trans (U.conj _ V.gram_point)
def ratEmbed := V.toRatCoords.symm.toMonoidHom.comp (U.map _ (by simp) rfl)
def embFin := (MonoidHom.snd ..).comp V.ratEmbed
def Γ := V.ratEmbed.range
abbrev Γf := V.embFin.range
def vecAtPoint := V.x⁻¹.1.mulVecLin ∘ₛₗ .mk (σ := toAdele) ⟨(toAdele ∘ ·), by simp⟩ (by simp [funext_iff])
def baseLattice : AddSubgroup (n → E) := by use! {y | ∀ i, (V.vecAtPoint y i).2 ∈ Ô E} <;> simp_all [add_mem]
end Space
variable (n)
@[simps] def stdSpace : Space E n 1 := ⟨1, 1, by simp [stdForm]; rfl⟩
def mass l := (classSum (stdSpace E (Fin l)).Γf (Kf ..) 1 : ℝ)
variable {E n}
abbrev stdEmbFin := (stdSpace E n).embFin
abbrev stdRatPoints := (stdSpace E n).Γf
