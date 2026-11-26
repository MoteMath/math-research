import Lib.General.Algebra.DisjointUnions
open CategoryTheory Abelian.Ext Comparison piAbFunctor LongExactSeq Function AddCommGrpCat Limits cech fibreProd Fin
variable {C} [Category C] {N I} {F : I → AbFunctor C} {M G : AbFunctor C} (β : M ⟶ G)
def kerComplex : ShortComplex (AbFunctor C) := .mk (X₁ := .mk _ fun f ↦ ofHom (((M.map f).hom.domRestrict _).codRestrict _ (by simp_all))) {app c := ofHom (β c).hom.ker.subtype} β (by ext _ ⟨⟩; tauto)
lemma kerComplex_shortExact {α : M ⟶ G} (h : ∀ c, Surjective (α c)) : (kerComplex α).ShortExact := (shortExact_of_app (by simp) (by simp [Exact]) h).2
lemma acC M : ∃ ι, ∃ (c : ι → C) (g : freeAb (sigma (reprBy <| c ·)) ⟶ M) (h : (kerComplex g).ShortExact), ∀ F n, Surjective ((contravariant h F).δ n) := ⟨Σ _, _, _, (freeAb.homEquiv ..).2 (sigma.desc (pointMap ·.2)), kerComplex_shortExact (⟨.of ⟨⟨·, _⟩, _⟩, (homReprEquiv ..).right_inv ·⟩), fun _ _ _ ↦ (exact_delta_f ..).1 ((H.sigma_bijective ..).1 (by simp [eq_zero_of_projective]))⟩
def piAbFunctor.lift (f : ∀ i, N ⟶ F i) : N ⟶ piAbFunctor F := ⟨fun A ↦ ofHom (.pi (f · A |>.hom)), by aesop (add simp piAbFunctor)⟩
lemma H.pi_bijective n : Bijective fun x i ↦ push N (π F i) n x := by induction n generalizing N; exact (bijective_iff_of_comm_sq (funext <| mk₀_comp_mk₀ · ∘' _) (mk₀_bijective ..) (.piMap (mk₀_bijective _ ∘' F))).1 (Equiv.mk _ lift).bijective; choose _ _ _ h s using acC N; simp_all [← pull_id_eq_push]; apply Hom.bijective_succ_family fun _ ↦ pull_hom_contravariant h h ⟨𝟭 C, _⟩ (𝟙 _) <;> tauto
variable {C : _} [Category C] {Y E W V : C ⥤ Type 1} {p : E ⟶ Y} {u : W ⟶ Y} {q : V ⟶ W} {v}
lemma IsCohomEquiv.of_bijective {F} (h : AllBijective (p ·)) : IsCohomEquiv F (freeAb.map p) := of_isIso (freeAb.map (isoOfAppBijective p h).1)
@[local simp] lemma isPullback_iff : IsPullback v q p u ↔ (∀ B z, p B (v B z) = u B (q B z)) ∧ ∀ B w x, p B x = u B w → ∃! z, q B z = w ∧ v B z = x := by simp [IsPullback.iff_app, Types.isPullback_iff, ConcreteCategory.hom_ext_iff, ExistsUnique]; grind
lemma isPullback_fibreProd : IsPullback (snd u p) (fst ..) p u := by simp_all [fibreProd, fst, snd, ExistsUnique]
lemma isPullback_cech {m} : IsPullback (proj p _ 0) (Y := cech ..) { app _ := ↾fun e ↦ ⟨(e.1 ·.succ), by grind⟩ } p (proj p m 0 ≫ p) := by simpa [cech, proj, ExistsUnique] using ⟨by tauto, fun _ a _ x _ ↦ ⟨cons x a, by simp_all [funext_iff, forall_fin_succ]⟩⟩
open Abelian Functor Subfunctor Ext H IsCohomEquiv ConcreteCategory Arrow BijectiveUpTo sigma IsPointwiseSurjective Iso
variable {C : _} {C' C''} [Category C] [Category C'] [Category C''] {F G N : AbFunctor C} {F' G' N' : AbFunctor C'} {F'' N'' : AbFunctor C''} {Y E : C ⥤ Type 1} {Y' E' r φ} (c : Comparison F F') {A B} (u : Y' ⟶ c.φ ⋙ reprBy A)
def Comparison.IsBijective {N N'} α := ∀ n, Bijective (c.pull (N := N) (N' := N') α n)
lemma isCohomEquiv_iff_isBijective {α : N ⟶ G} : IsCohomEquiv F α ↔ (Comparison.id F).IsBijective α := by simp [IsCohomEquiv, Comparison.IsBijective]
alias ⟨IsCohomEquiv.bij, Comparison.IsBijective.eqv⟩ := isCohomEquiv_iff_isBijective
lemma H.push_bijective_of_isIso {γ : F ⟶ G} (_ : IsIso γ) n : Bijective (push N γ n) := bijective_of_isIso ((extFunctorObj ..).map γ)
lemma pointMap_comp y (p : E ⟶ Y) : pointMap y ≫ p = pointMap (p A y) := by ext; apply p.naturality_apply
lemma projective_and_eval_bijective F {B} z (hz : AllBijective (pointMap z ·)) : Projective (freeAb Y) ∧ Bijective (· B (.of z) : (freeAb Y ⟶ F) → _) := let e := freeAb.mapIso (isoOfAppBijective _ hz).symm
  Y.map_id_apply B z ▸ ⟨e.retract.projective, (e.homFromEquiv.trans (homReprEquiv ..).1).bijective⟩
lemma pointMap_id_bijective_of_fullyFaithful (ψ : C ⥤ C') [ψ.Full] [ψ.Faithful] c : AllBijective (@pointMap _ _ (ψ ⋙ reprBy _) c ⟨𝟙 _⟩ ·) := fun _ ↦ ULift.map_bijective.2 ((homFromEquiv (.refl _)).bijective.comp ⟨by grind, ψ.map_surjective⟩)
namespace Comparison
noncomputable def homOfValue := AddMonoidHom.mk' (fun x ↦ freeAbMap u ≫ whiskerLeft _ ((homReprEquiv ..).symm x) ≫ c.coeffHom) (by bound)
variable {c} {c' : Comparison F' F''} {α : N' ⟶ _ ⋙ N} {α' : N'' ⟶ _}
lemma IsBijective.trans_iff (h : c'.IsBijective α') {γ} (e : α' ≫ whiskerLeft _ α = γ := by exact freeAb.hom_ext) : (c.trans c').IsBijective γ ↔ c.IsBijective α := by simp [IsBijective, ← (h _).of_comp_iff', comp_def, pull_trans, e]
lemma IsBijective.trans (h : c.IsBijective α) (h' : c'.IsBijective α') {γ} (e : α' ≫ whiskerLeft _ α = γ := by exact freeAb.hom_ext) : (c.trans c').IsBijective γ := (h'.trans_iff e).2 h
lemma isBijective_iff_of_coeff_iso {β} (γ : F ⟶ G) (γ' : _ ⟶ G') [IsIso γ] [IsIso γ'] (w : whiskerLeft _ γ ≫ β = c.coeffHom ≫ γ') : c.IsBijective α ↔ IsBijective ⟨_, β⟩ α := by simp [IsBijective, bijective_iff_of_comm_sq (c.pull_push _ _ _ w _), push_bijective_of_isIso]
lemma homOfValue_app x B y : c.homOfValue u x B (.of y) = c.coeffHom B (F.map (u B y).down x) := add_zero (F.map ..) ▸ rfl
attribute [instance] subsingleton_of_projective
variable {u}
lemma isBijective_reprBy_iff : c.IsBijective (freeAbMap u) ↔ Bijective (c.homOfValue u) ∧ ∀ n, Subsingleton (H (freeAb Y') F' (n + 1)) := Nat.and_forall_add_one.symm.trans (.and (bijective_iff_of_comm_sq (by aesop (add simp [pull, H.map, H.push])) (homEquiv₀.trans _).symm.bijective (mk₀_bijective ..)).symm ⟨(· · |>.2.subsingleton), by simp_all [Bijective, Surjective, nontriviality]⟩)
lemma isBijective_of_repr z (hz : AllBijective (pointMap z ·)) : Bijective (c.coeffHom B <| F.map (u B z).down ·) → c.IsBijective (freeAbMap u) := let ⟨_, b⟩ := projective_and_eval_bijective F' z hz
  by simp [isBijective_reprBy_iff, comp_def, ← b.of_comp_iff', subsingleton_iff, homOfValue_app]
variable {u : Y' ⟶ _ ⋙ Y} {v : E' ⟶ _ ⋙ E} {p : _} {p'} (w : p' ≫ u = v ≫ whiskerLeft _ p) (e : IsCohomEquiv F (freeAb.map p)) (e' : IsCohomEquiv F' (freeAb.map p'))
lemma IsBijective.precomp_of_bijective (h : c.IsBijective (freeAbMap u)) {v} (p' : E' ⟶ _) (w : p' ≫ u = v) : AllBijective (p' ·) → c.IsBijective (freeAbMap v) := w ▸ (h.trans <| bij <| of_bijective ·)
lemma bijectiveUpTo_of_cech_pred (hp : IsCover F p) (hp' : IsCover F' p') (hv : c.IsBijective (freeAbMap v)) (H : ∀ m, BijectiveUpTo (c.pull (freeAbMap (Y := cech p m) (Y' := cech p' m) ((cF m).map (homMk' v u w.symm))) ·) (r - 1)) : BijectiveUpTo (c.pull (freeAbMap u) ·) r := (congr hp hp' map_pull_eq_pull_map).2 (cech_descent_step leftToRight (c.devissage ((whiskeringLeft ..) (toArr (.mk p))) ((whiskeringLeft ..).2 (toArr.2 (homMk' v u w.symm)))).1 (forall_bijective_iff_bijectiveUpTo.1 hv r) H)
lemma isBijective_of_fibres t (s : IsPullback v p' (whiskerLeft _ t) u) (h : ∀ A x, c.IsBijective (freeAbMap (snd u (whiskerLeft _ (pointMap (t A x)))))) : c.IsBijective (freeAbMap v) := forall_bijective_iff_bijectiveUpTo.2 (by
  induction' · with r ih generalizing Y Y' E E'; tauto
  let p := desc (ι := E.Elements) (pointMap ·.2)
  have k A x := (pointMap_comp x t ▸ h A x).precomp_of_bijective _
    ((isPullback_fibreProd (p := whiskerLeft _ (pointMap x)).paste_vert s).isoIsPullback_hom_fst _ _ isPullback_fibreProd) (app _ · |>.toEquiv.bijective)
  let q := desc fun x : E.Elements ↦ fst v (whiskerLeft _ (pointMap x.2))
  exact bijectiveUpTo_of_cech_pred (by ext _ ⟨_, ⟨⟩⟩; tauto) (isCover p fun _ y ↦ (⟨⟨⟨y⟩, ⟨𝟙 _⟩⟩, E.map_id_apply ..⟩)) (isCover q (⟨⟨⟨v · ·⟩, ⟨_, ⟨_⟩⟩, (E.map_id_apply ..).symm⟩, rfl⟩))
    (fun n ↦ (bijective_iff_of_comm_sq (fun _ ↦ funext fun _ ↦ (map_pull_eq_pull_map ..).symm) (sigma_bijective ..) (sigma_bijective ..)).2 (.piMap (k _ ·.2 n))) (v := desc fun x ↦ snd .. ≫ whiskerLeft _ (ι _ x)) fun _ ↦ ih (p' := proj .. ≫ q) (proj .. ≫ p) (isPullback_iff.2 ⟨fun _ ↦ (·.1 0 |>.2.2.symm), fun _ _ g e ↦ ⟨⟨(⟨_, ⟨_, _⟩, e ▸ g.2 0 ·⟩), by tauto⟩, by tauto, by rintro z ⟨⟨⟩, ⟨⟩⟩; congrm ⟨(⟨_, ⟨$(z.2 · 0), _⟩, _⟩), _⟩⟩⟩) (k · ∘' _))
variable (c u) in
def HasUnivPoints := ∀ A (y : Y A), ∃ B x s, u B x = Y.map s y ∧ (∀ D z f, u D z = Y.map f y → ∃! g, Y'.map g x = z ∧ s ≫ c.φ.map g = f) ∧ Bijective fun a ↦ c.coeffHom B (F.map s a)
lemma HasUnivPoints.bijPb (h : c.HasUnivPoints u) w t (s : IsPullback v w (whiskerLeft _ t) u) : c.IsBijective (freeAbMap v) := isBijective_of_fibres t s fun _ _ ↦ let ⟨_, x, _, e, H, b⟩ := h ..
  isBijective_of_repr ⟨(x, _), e⟩ (fun D ↦ .of_existsUnique _ ((Equiv.ulift.existsUnique_congr fun _ ↦ ⟨by bound, fun ⟨a, b⟩ ↦ congr(⟨($a, ⟨$b⟩), _⟩)⟩).2 <| H D _ _ ·.2)) b
lemma HasUnivPoints.isBijective (h : c.HasUnivPoints u) : c.IsBijective (freeAbMap u) := h.bijPb _ (𝟙 _) .of_id_snd
lemma HasUnivPoints.bijSub (h : c.HasUnivPoints u) U : c.IsBijective (freeAbMap (Y := toFunctor U) ((U.whisker _).fromPreimage u)) := h.bijPb _ U.ι (isPullback_iff.2 (by aesop (add simp [ExistsUnique, toFunctor])))
lemma HasUnivPoints.isCohomEquiv_incl_iff (h : c.HasUnivPoints u) U {S} (e : S = (whisker U _).preimage u) : IsCohomEquiv F (freeAb.map U.ι) ↔ IsCohomEquiv F' (freeAb.map S.ι) := e ▸ forall_congr' (bijective_iff_of_comm_sq (map_pull_eq_pull_map (n := _)) (h.isBijective _) ∘' h.bijSub U)
lemma isBijective_of_adj {U} (a : φ ⊣ U) : IsBijective (F := φ ⋙ F) ⟨U, whiskerRight a.2 F⟩ (freeAbMap (𝟙 (U ⋙ Y'))) := HasUnivPoints.isBijective fun A y ↦ ⟨_, _, a.1 A, rfl, fun _ _ f _ ↦ ((a.homEquiv ..).bijective.existsUnique f).imp (by aesop (add simp a.homEquiv_unit)), by simpa [← map_comp_apply] using! bijective_id⟩
include w e e'
lemma bijectiveUpTo_congr : BijectiveUpTo (c.pull (freeAbMap u) ·) r ↔ BijectiveUpTo (c.pull (freeAbMap v) ·) r := congr e e' (map_pull_eq_pull_map (freeAb.map_commSq ⟨w⟩).1)
lemma isBijective_congr : c.IsBijective (freeAbMap u) ↔ c.IsBijective (freeAbMap v) := by simp_all
  [IsBijective, forall_bijective_iff_bijectiveUpTo, bijectiveUpTo_congr w]
