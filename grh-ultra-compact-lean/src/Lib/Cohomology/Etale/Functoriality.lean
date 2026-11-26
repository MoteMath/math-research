import Lib.General.LinearAlgebra.Base
noncomputable section
open CategoryTheory Functor AddCommGrpCat AddMonoidHom Function Abelian Ext FreeAbelianGroup
variable (C) {C'} [Category.{0,1} C] [Category.{0,1} C'] {D T : Type*} [Category* D] [Category* T]
instance : CoeFun (D ⥤ T) fun _ ↦ D → T := ⟨obj⟩
instance {F G : D ⥤ T} : CoeFun (F ⟶ G) fun _ ↦ ∀ A, F A ⟶ G A := ⟨(·.app)⟩
instance {F : D ⥤ _} : CoeFun (Subfunctor F) fun _ ↦ ∀ A, Set (F A) := ⟨(·.obj)⟩
abbrev AbFunctor := C ⥤ AddCommGrpCat.{1}
variable {C} {Y E : D ⥤ Type 1} (p : E ⟶ Y) {J : Type 1} (X : J → C ⥤ Type 1)
def cech m := mk ({e : Fin (m + 1) → _ // ∀ i j, p.app · (e i) = p _ (e j)}) fun f ↦ ↾fun e ↦ ⟨(E.map f <| e.1 ·), by simp; grind⟩
def cech.proj m (j : Fin (m + 1)) : cech p m ⟶ E where app _ := ↾(·.1 j)
def sigma := mk (Σ i, X i ·) fun f ↦ ↾(⟨_, (X _).map f ·.2⟩)
def sigma.ι i : X i ⟶ sigma X where app _ := ↾(⟨i, ·⟩)
variable {Y E W : C ⥤ Type 1} (ι : C ⥤ CommRingCat.{0}) (R) [Ring R] (N F G : AbFunctor C) (n : ℕ) (U : Subfunctor Y) (φ : C' ⥤ C) (u : W ⟶ Y) (p : E ⟶ Y)
instance : HasExt.{2} (AbFunctor C) := .standard _
abbrev H := Ext N F n
def freeAb : (D ⥤ Type 1) ⥤ D ⥤ Ab.{1} := (whiskeringRight ..) free
def liftCoeff (F : C ⥤ Ab.{0}) : AbFunctor C := F ⋙ uliftFunctor
def reprFunctor := @uliftCoyoneda.{1} C _
abbrev reprBy (A : C) := reprFunctor ⟨A⟩
abbrev reprMap {A B : C} (f : A ⟶ B) := reprFunctor.map f.op
abbrev restrictAlong : (C ⥤ D) ⥤ C' ⥤ D := (whiskeringLeft ..) φ
def H.map {N N'} F (α : N' ⟶ N) n : @H C _ N F n →+ H N' F n := (mk₀ α).precomp F n.zero_add
def H.push {F F'} (β : F ⟶ F') n : H N F n →+ H N F' n := (mk₀ β).postcomp N rfl
def H.pushHom := mk' (@push _ _ N F G · n) (by simp [push, mk₀_add])
class CoeffAction where act : R →+* End F
instance [CoeffAction R F] n : Module R (H N F n) := (ModuleCat.mkOfSMul (.comp (.mk' ((extFunctorObj N n).mapEnd F) fun _ _ ↦ End.ext (extFunctorObj N n).map_add) CoeffAction.act)).isModule
def IsCohomEquiv {N N'} α := ∀ n, Bijective (@H.map C _ N N' F α n)
structure Comparison (F' : AbFunctor C') where of :: (φ) coeffHom : φ ⋙ F ⟶ F'
abbrev Comparison.id := of (𝟭 C) (𝟙 F)
def Comparison.pull {F F'} (c : Comparison F F') {N : AbFunctor C} {N' : AbFunctor C'} (α : N' ⟶ c.φ ⋙ N) n : H N F n →+ H N' F' n := (H.map _ α n).comp ((H.push _ c.coeffHom n).comp ((restrictAlong _).mapExtAddHom ..))
def toArr {T} [Category* T] := (evaluation D T ⋙ mapArrowFunctor ..).flip
def cF m := toArr ⋙ (whiskeringRight C ..) (cech Arrow.leftToRight m)
def fibreProd := mk ({x // u.app · x.1 = p _ x.2}) fun f ↦ ↾fun x ↦ ⟨(W.map f x.1.1, E.map f x.1.2), by aesop⟩
def fibreProd.fst : fibreProd u p ⟶ W where app _ := ↾(·.1.1)
def fibreProd.snd : fibreProd u p ⟶ E where app _ := ↾(·.1.2)
def pointMap {A} (y : Y A) : reprBy A ⟶ Y := uliftCoyonedaEquiv.symm y
def sigma.desc {ι X} (f : ∀ i : ι, X i ⟶ Y) : sigma X ⟶ Y := ⟨fun A ↦ ↾(f _ A ·.2), by aesop (add simp sigma)⟩
def CategoryTheory.Subfunctor.whisker : Subfunctor (φ ⋙ Y) := ⟨_, fun _ ↦ U.map _⟩
def IsCohomDense := ∀ A y, IsCohomEquiv F (freeAb.map (U.preimage (pointMap (A := A) y)).ι)
def IsIdemQuotient {A B} e π := @ι.map A B π e = 0 ∧ (∀ B' f, @ι.map A B' f e = 0 → ∃! g, π ≫ g = f) ∧ Surjective (ι.map π) ∧ RingHom.ker (ι.map π).hom ≤ .span {e}
structure HasPartitions where
  exists_quotient A e : IsIdempotentElem e → e ≠ 1 → ∃ B π, @IsIdemQuotient _ _ ι A B e π
  bijective_prod {A B₁ B₂} π₁ π₂ : Bijective (fun x ↦ (@ι.map A B₁ π₁ x, @ι.map A B₂ π₂ x)) → Bijective fun x ↦ (F.map π₁ x, F.map π₂ x)
abbrev IsLocallyEverything := ∀ A y m, Ideal.IsMaximal m → ∃ a ∉ m, ∀ B f, IsUnit (@ι.map A B f a) → Y.map f y ∈ U B
def HasZariskiDescent := ∀ ⦃Y U⦄, IsLocallyEverything ι U → @IsCohomDense C _ Y F U
lemma IsLocallyEverything.whisker {ι U} (h : @IsLocallyEverything C _ Y ι U) : IsLocallyEverything (φ ⋙ ι) (U.whisker φ) := fun _ ↦ forall₃_imp (by tauto) (h _)
def IsPointwiseSurjective := ∀ A, Surjective (p A)
variable {R φ} {ι : Type} (F : ι → AbFunctor C) {I V V'} [Fintype I]
abbrev freeAbMap {Y Y'} (u : Y' ⟶ φ ⋙ Y) : freeAb Y' ⟶ φ ⋙ freeAb Y := freeAb.map u
def IsComparableRing {A} [Mul A] (f : A → R) := ∀ a b, ∃ e, IsIdempotentElem e ∧ a ∣ f e * b ∧ b ∣ (1 - f e) * a
def Cancels (m : I → ℤ) (v : I → V) := ∑ i, m i • of (v i) = 0
lemma Cancels.mono {m v v'} (h : @Cancels I V _ m v) (H : FactorsThrough v' v) : @Cancels I V' _ m v' := by simpa [(H.comp_left _).extend_apply] using! congr(lift (extend v (of ∘ v') 0) $h)
def piAbFunctor : AbFunctor C := .mk _ fun f ↦ ofHom (.piMap (F · |>.map f |>.hom))
def piAbFunctor.π i : piAbFunctor F ⟶ F i where app _ := ofHom (Pi.evalAddMonoidHom ..)
abbrev AllBijective {ι} {A B : ι → Type*} (f : ∀ i, A i → B i) := ∀ i, Bijective (f i)
abbrev isoOfAppBijective {C} [Category C] {P T} [∀ X Y, FunLike (P X Y) ..] {F G : C ⥤ D} [@ConcreteCategory D _ P T _] [(forget D).ReflectsIsomorphisms] (γ : F ⟶ G) (h : AllBijective (γ ·)) := @asIso _ _ _ _ γ (by simpa [γ.isIso_iff_isIso_app, ConcreteCategory.isIso_iff_bijective])
end
noncomputable section
open CategoryTheory Limits Abelian.Ext Functor Function H ShortComplex ShortExact
variable {D C C' C''} [Category D] [Category C] [Category C'] [Category C''] {F G N M K : AbFunctor C} {F' G' N' M' : AbFunctor C'} {F'' N'' : AbFunctor C''} {n} (c : Comparison F F') (c' : Comparison F' F'') (a' : M' ⟶ N') (a : N' ⟶ c.φ ⋙ N) (α' : K ⟶ M) (α : M ⟶ N) (β : F ⟶ G) (β' : G ⟶ K) (Ξ : (D ⥤ Ab) ⥤ AbFunctor C') {R} [Ring R]
class abbrev IsExactFunctor := Additive Ξ, PreservesFiniteLimits Ξ, PreservesFiniteColimits Ξ
lemma H.smul_eq_push [CoeffAction R F] (r : R) x : r • x = push N (CoeffAction.act r : End F).asHom n x := rfl
variable (R) {Φ Ψ} [@IsExactFunctor C C' _ _ Φ] [IsExactFunctor Ψ] {Θ} [@IsExactFunctor C' C'' _ _ Θ] (η : Φ ⟶ Ψ) (x : H N F n)
instance : IsGrothendieckAbelian.{1} (AbFunctor C) := {ab5OfSize.1 _ := inferInstance, hasSeparator := .of_equivalence (opOpEquivalence C).congrLeft}
@[induction_eliminator] lemma H.dimInd {P : ∀ {F n}, H N F n → Prop} (h₀ : ∀ F f, @P F 0 (mk₀ f)) (h : ∀ S (hS : ShortExact S) n x, @P _ n x → P (x.comp hS.extClass rfl)) : P x := n.rec ((mk₀_bijective ..).2.forall.2 <| h₀ ·) (fun _ _ F x ↦ (x.covariant_sequence_exact₁ _ ⟨exact_cokernel (Injective.ι F)⟩ (eq_zero_of_injective _) rfl).elim (by bound)) F x
attribute [simp] mapExactFunctor_comp mapExactFunctor_mk₀ mapExactFunctor_extClass mapExtAddHom
attribute [local simp] H.map H.push Comparison.pull mk₀_add
set_option backward.isDefEq.respectTransparency false
lemma mapExactFunctor_mapExactFunctor : (x.mapExactFunctor Φ).mapExactFunctor Θ = x.mapExactFunctor (Φ ⋙ Θ) := by induction x <;> simp_all
lemma mapExactFunctor_naturality : push _ (η F) n (x.mapExactFunctor Φ) = map _ (η N) n (x.mapExactFunctor Ψ) := by have := (extClass_naturality (f := mapNatTrans · η)); induction x <;> simp_all [map_of_exact, ← comp_assoc_of_second_deg_zero, comp_assoc (h₂₃ := rfl)]
namespace H
@[simp] lemma map_id : map F (𝟙 N) n x = x := by simp
lemma map_comp : map F (α' ≫ α) n x = map F α' n (map F α n x) := by simp
lemma push_comp : push N (β ≫ β') n x = push N β' n (push N β n x) := by simp
def mapHom F M N n := AddMonoidHom.mk' (@map C _ N M F · n) (by simp)
lemma map_push : map G α n (push N β n x) = push M β n (map F α n x) := by simp
def mapₗ F [CoeffAction R F] (α : M ⟶ N) n : H N F n →ₗ[R] H M F n := { map .. with map_smul' _ := map_push α (End.asHom _) }
lemma mapExactFunctor_restrictAlong_id : x.mapExactFunctor (restrictAlong (𝟭 _)) = x := by induction x <;> aesop
end H
lemma IsCohomEquiv.of_isIso [IsIso α] : IsCohomEquiv F α := (bijective_iff_has_inverse.2 ⟨map F (inv α) ·, by cat_disch⟩)
lemma Comparison.pull_push (β : _ ⋙ G ⟶ G') γ γ' (h : whiskerLeft _ γ ≫ β = c.coeffHom ≫ γ') α x : pull ⟨_, β⟩ α n (push N γ n x) = push N' γ' n (c.pull α n x) := by aesop
@[simp] lemma Comparison.id_pull : (id F).pull α = map F α := by ext n x; simp [mapExactFunctor_restrictAlong_id, x.comp_mk₀_id]
abbrev Comparison.trans : Comparison F F'' := ⟨_ ⋙ _, c'.φ.whiskerLeft c.coeffHom ≫ c'.coeffHom⟩
variable {c c' a a' α' α}
lemma IsCohomEquiv.comp_iff (h' : IsCohomEquiv F α') : IsCohomEquiv F (α' ≫ α) ↔ IsCohomEquiv F α := by simp [IsCohomEquiv, ← (h' _).of_comp_iff', comp_def]; rfl
namespace Comparison
lemma pull_id_eq_push : pull ⟨𝟭 C, β⟩ (𝟙 N) n = push N β n := by ext; simp [mapExactFunctor_restrictAlong_id]
lemma pull_whiskerRight {φ ψ} η (β : _ ⟶ F') (α : N' ⟶ _) : pull ⟨φ, whiskerRight η F ≫ β⟩ α n = pull ⟨ψ, β⟩ (α ≫ whiskerRight η N) n := by ext; simpa using! congr((push _ β n $(mapExactFunctor_naturality ((whiskeringLeft ..).map η) _)).map _ α n)
lemma map_pull_eq_pull_map {b} (w : a' ≫ a = b ≫ whiskerLeft _ α := by exact freeAb.hom_ext) n x : map _ a' n (c.pull a n x) = c.pull b n (map F α n x) := by aesop
lemma pull_trans {α' : N'' ⟶ _} x : c'.pull α' n (c.pull a n x) = (c.trans c').pull (α' ≫ whiskerLeft _ a) n x := by simp [mapExactFunctor_mapExactFunctor]; rfl
