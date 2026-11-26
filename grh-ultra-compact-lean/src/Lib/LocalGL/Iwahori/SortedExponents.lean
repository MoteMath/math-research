import Lib.General.Groups.CyclicSubrep
import Lib.GaloisRep.Main.HeckeOperatorOfFunction
section
open Matrix WithZero Valued GeneralLinearGroup DoubleCoset Filter
attribute [local simp] zero_lt_iff mul_assoc zpow_ne_zero _root_.zpow_add mem_proIwahori
attribute [local simp ←] map_zpow
variable {F F' N} [Field F] [Valued F ℤᵐ⁰] [Field F'] [Valued F' ℤᵐ⁰] {g : GL (Fin N) F} {t : Fin N → Fˣ} (ht : StrictMono (v <| t · |>.1))
abbrev iwahoriDoubleCoset (t : Fin N → Fˣ) := doubleCoset (diagGL t) (SetLike.coe proIwahori) (SetLike.coe proIwahori)
lemma diagGL_mem_proIwahori : diagGL t ∈ proIwahori ↔ ∀ i, v ((t i).1 - 1) < 1 := by simp [diagonal]; grind [v.map_eq_of_sub_lt, one_pos]
lemma map_mem_proIwahori_iff_of_isEquiv {ι : F →+* F'} (h : (v.comap ι).IsEquiv v) : g.map ι ∈ proIwahori ↔ g ∈ proIwahori := by simp [← h.le_one_iff_le_one, ← h.lt_one_iff_lt_one]
include ht
private lemma k7 (a : _ → _ → F) : ∀ᶠ k in atTop, ∀ i j, i < j → v (t i ^ k / t j ^ k * a i j) ≤ 1 := by
  simp_rw [eventually_all, ← div_pow]
  exact fun i j h ↦ (tendsto_zero_pow_of_v_lt_one (by simp [ht h, field])).mul_const _
   ((isOpen_integer F).mem_nhds (by simp))
private lemma v7 s : ∀ᶠ k in atTop, t ^ k * s ∈ dominantTorus := (k7 ht (s · / s ·)).mono (by simp [dominantTorus, monotone_iff_forall_lt, field])
lemma exists_twisted_conj_diag [CompactSpace 𝒪[F]] (σ : F →+* F) (hσ : ∀ x, v (σ x) = v x) (cont : Continuous σ) (sur : (⇑(map (n := Fin N) σ)).Surjective) (hg : g ∈ iwahoriDoubleCoset t) : ∃ k ∈ proIwahori, ∃ d,
  diagGL d ∈ proIwahori ∧ k⁻¹ * g * k.map σ = diagGL (t * d) := by
  let H (j : ℤ) := (MulAut.conj (diagGL t) ^ j).comapSubgroup proIwahori; let X (k : proIwahori) := (diagGL t)⁻¹ * (k.1⁻¹ * g * .map σ k)
  have L {j g} : g.map σ ∈ H j ↔ g ∈ H j := by
   simp [H, ← map_inv, ← hσ (g _ _ - 1), mul_left_comm (_ ^ j), *]
  choose f h using (Nat.rec (Nat.rec (let ⟨k, p, _, q, e⟩ := mem_doubleCoset.1 hg
   ⟨⟨k, p⟩, by simp [X, (H 0).mul_mem q (L.2 p), *]⟩) fun y ⟨k, hc⟩ ↦
   (exists_unipotent_conj_mem_proIwahori ht.monotone (hc 0)).rec fun u ⟨hu,
   _⟩ ↦ let ⟨z, hp⟩ := sur (u⁻¹ * X k)
   have U (j : ℕ) : u ∈ H j := by simpa [H, ← map_pow] using
    conj_unitriangular_mem_proIwahori (pow_mem ht.monotone j) hu
   have B (j : ℕ) (h : j ≤ y.succ := by grind) : z ∈ H (j + -1) :=
    by cases j; rwa [← L, hp]; grind [mul_mem, inv_mem]
   ⟨k * ⟨_, B 1⟩⁻¹, fun j a ↦ by lift j to ℕ using a.1; simpa [X, H, *] using
    (proIwahori.mul_mem (B j) (U j))⟩) fun _ h y ↦ let ⟨k, hc⟩ := h y.succ
   ⟨k * ⟨_, hc 1⟩, fun j a ↦ by simpa [X] using (@L _ (⟨_, hc 1⟩ : proIwahori)).2 (by simpa [H] using (hc (j + 1)))⟩ : ∀ x y : ℕ, ∃ k, ∀ j (_ : j ∈ Set.Icc (-↑x) ↑y := by grind), X k ∈ H j)
  have ⟨k, K⟩ := exists_clusterPt_of_compactSpace (atTop.map (diag f))
  have K j : k ∈ X ⁻¹' H j := ((proIwahori.isClosed_of_isOpen isOpen_proIwahori).preimage
   (by simp; fun_prop)).mem_of_mapClusterPt K (.mono (mem_atTop j.natAbs) fun _ _ ↦ h ..)
  use k, k.2, (.mk0 _ <| v.pos_iff.1 <| v_diag_eq_one_of_mem_proIwahori (K 0) · ▸ one_pos),
   diagGL_mem_proIwahori.2 (K 0).2.2,
   map_mul diagGL t _ ▸ eq_mul_of_inv_mul_eq (Units.ext (IsDiag.diagonal_diag fun i j h ↦ by_contra
   fun e : X k i j ≠ 0 ↦ have A m := (by simpa [← map_inv, ← log_le_log, e] using
    (mem_proIwahori.1 (K (m - m * (v (X k i j)).log))).1 i j)
   by cases h.lt_or_gt <;> nlinarith [A 1, A (-1), by simpa [← log_lt_log] using ht ‹_›]).symm)
end
section
open Finset Equiv Fint Function IsLocalRing Matrix OrderDual Units Valued WithZero
attribute [local simp] Pi.mulSingle_apply transvectionGL_mem_proIwahori
variable {F W} [Field F] [Valued F ℤᵐ⁰] [AddCommGroup W] [Module ℂ W] {N} {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] {x c d} {g : GL (Fin N) F} {a b : Fin N} {φ : ρ →ₗ[ℂ] W} (h : a ⋖ b) {h' : a ≠ b} {ϖ : Fˣ} (hϖ : v ϖ.1 = exp (-1)) {y z ξ l t K}
@[grind] lemma mem_blockParahoric {c : ℕ → ℕ} : g ∈ blockParahoric c ↔ g ∈ intGL _ 𝒪[F] ∧ ∀ i j, c j.1 < c i.1 → v (g i j) < 1 := .rfl
lemma s11_q8 : g ∈ proIwahori ↔ g ∈ blockParahoric id ∧ ∀ i, g i i ∈ {x | v (x - 1) < 1} := and_assoc.symm
lemma s11_w9 {c d : ℕ → ℕ} t (σ : Equiv.Perm (Fin N)) (S : Set F) (hk : g ∈ blockParahoric d ∧ ∀ i, g i i ∈ S) (h : ∀ a b, g (σ a) (σ b) = 0 ∨ log (v (t b).1) + ite (c b < c a) 1 0 ≤ log (v (t a).1) + ite (d (σ b) < d (σ a)) 1 0) : let k :=
   (permGL σ * diagGL t)⁻¹ * g * (permGL σ * diagGL t); k ∈ blockParahoric c ∧ ∀ i, k i i ∈ S := by
  simp_all only [mem_blockParahoric, mem_intGL_iff_det]; erw [det_units_conj']; simp [← map_inv, mul_apply, symm_apply_eq, diagonal, mul_assoc]; grind [ne_zero, one_pos, =_ log_le_log, =_ log_lt_log, map_eq_zero, log_mul, log_inv, mul_eq_zero]
omit [IsSmoothRep ρ.ρ] in
private lemma z8 {σ} {x : ρ} (hx : x ∈ levelSpace ρ.ρ proIwahori) (e : σ a < σ b) c (hc : v c ≤ 1) : ρ (transvectionGL h' c) (ρ (permGL σ⁻¹) x) = ρ (permGL σ⁻¹) x :=
  cast (by simp_all) congr(ρ $(permGL_mul_transvectionGL σ⁻¹ e.ne c) x).symm
lemma proIwahori_le_blockParahoric {c : ℕ → ℕ} (h : ∀ i j, c j < c i → j < i := by grind) :
  proIwahori ≤ @blockParahoric F _ _ N c := fun _ ↦ by grind [s11_q8]
omit [Valued F ℤᵐ⁰] in
@[local simp] private lemma p4 (h : a ≠ b) (u : Fˣ) : permGL (swap a b) * transvectionGL h u.1 = transvectionGL h u.1⁻¹ * diagGL (Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b u) * transvectionGL h.symm u.1⁻¹ := by ext; simp [PEquiv.toMatrix_mul_apply, transvection, mul_add, add_mul, single_apply, diagonal_apply, @apply_ite Fˣ]; grind
private lemma k0 (hg : g ∈ proIwahori) : ∃ c : 𝒪[F], MulAut.conj (permGL (swap a b)) (g * transvectionGL h.ne c.1) ∈ proIwahori :=
  have : v (-g a b / g a a) ≤ 1 := by simp_all [v_diag_eq_one_of_mem_proIwahori, mem_proIwahori]
  ⟨⟨_, this⟩, by cases h; simpa using! s11_q8.2 (s11_w9 1 (swap a b) _ (s11_q8.1 (by aesop)) (by simp; grind [mul_transvection_apply_same, v_diag_eq_one_of_mem_proIwahori, one_pos]))⟩
variable [CompactSpace 𝒪[F]] (hl : IsExponent ρ ξ l)
private lemma x0 c (hφ : ∀ k ∈ proIwahori, ∀ z, φ (ρ k z) = φ z) (hx : ∀ c, v c ≤ 1 → ρ (transvectionGL h.ne' c) x = x) (hc : ∀ u, v u.1 = 1 → letI t := Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b u
  (∀ i, v (t i).1 = 1) → φ (ρ (diagGL t) x) = c) : letI s := ρ (permGL (swap a b))
  Nat.card 𝓀[F] • φ (s (compactMean ρ.ρ proIwahori x)) = φ (s x) + (.card 𝓀[F] - 1) • c := by
  have A (k : proIwahori) {w} (o : v w ≤ 1) : φ (ρ (k.1 * (permGL (swap a b) * transvectionGL h.ne
   w)) x) = ite (v w < 1) (φ (ρ (permGL (swap a b)) x)) c := by
   cases h; cases o.lt_or_eq
   simp_all [permGL_mul_transvectionGL]
   lift w to Fˣ <;> aesop
  simpa [h.1, ← v.mem_integer_iff] using (map_compactMean_of_const (φ ∘ₗ _) fun _ k ↦
   (k0 h k).rec
   fun z o ↦ by simpa [h.ne, ↓← residue_eq_zero_iff_lt, sum_ite, mul_assoc, ← map_sum, (Units.ext (transvection_mul_transvection_same ..) : transvectionGL .. * transvectionGL .. =
   transvectionGL ..), surjInv_eq, filter_ne', card_filter] using congr(∑ r, $(A ⟨_, o⟩ (surjInv residue_surjective r - z).2)) :)
lemma exists_iwahoriHeckeHom_injective (ρ : Rep ℂ (GL (Fin N) F)) [IsSmoothRep ρ.ρ] (hϖ : v ϖ.1 = exp (-1)) : ∃ t, ∃ h : StrictMono _, Injective (iwahoriHeckeHom ρ ⟨t, h.monotone⟩) := let s a : dominantTorus := ⟨(if a ≤
   · then ϖ⁻¹ else 1), by simp_all +decide [dominantTorus, Monotone, apply_ite, ite_apply]; lia⟩
  ⟨(∏ a, s a).1, by simp_all [StrictMono, prod_ite, filter_ge_eq_Iic, s], .of_ker _
   (((nonZeroSMulDivisors ..).comap (iwahoriHeckeHom ρ)).prod_mem fun a _ x h ↦ have := a.neZero
   let n := permGL (finCycle a)⁻¹ * diagGL (s a)
   have hy : ρ n x ∈ levelSpace _ _ := by simpa using fun k h ↦ x.2 ⟨n⁻¹ * k * n,
    s11_q8.2 (s11_w9 _
    _ _ (s11_q8.1 h)
    (by simp_all [s, @apply_ite Fˣ, apply_ite v, apply_ite log]; fin_omega))⟩
   by simpa [Perm.monotone_iff, *, (ρ.ρ.apply_bijective n).1] using (exists_antitone_of_swap toDual
    (fun σ ↦ compactMean ρ.ρ proIwahori (ρ (permGL σ⁻¹) (ρ n x)) = 0)
    ⟨(finCycle a)⁻¹, by simp [n]; injection h⟩ fun σ _ _ c e _ ↦ by simpa [*, -map_inv] using
    (x0 c 0 (fun _ ↦ compactMean_apply) (z8 hy e)
    (by intros; rw [← map_compactMean_of_factor _ (⟨·, diagGL_conj_mem_proIwahori · fun _ ↦ _,
    _⟩)] <;> simp_all)).symm))⟩
lemma IsExponent.apply_compactMean (hl : IsExponent ρ ξ l) : l (compactMean ρ.ρ proIwahori z) = l z := by simpa using hl (one_mem _) z
lemma IsExponent.w1 (hl : IsExponent ρ ξ l) k (hk : k ∈ proIwahori) z : l (ρ k z) = l z := by simp [← hl.apply_compactMean, hk]
include hl in
lemma IsExponent.z5 (ht : ∀ a, v (t a).1 = 1) z : l (ρ (diagGL t) z) = ξ t * l z := by rw [← map_compactMean_of_factor hl.w1 (⟨·,
  diagGL_conj_mem_proIwahori · fun _ ↦ _, _⟩), hl] <;> aesop_cat
lemma IsExponent.v0 {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] (hϖ : v ϖ.1 = exp (-1)) {y ξ l t K c} (hl : IsExponent ρ ξ l) (hz : y ∈ levelSpace ρ.ρ K) (o : ∀ {g}, g ∈ blockParahoric c ∧ (∀ i, v (g i i - 1) < 1) → g ∈ K) σ (H : ∀ a b, σ b < σ a → v (t (σ b)).1 ≤ v (t (σ a)).1 ∨ c a.1 ≤ c b.1 ∧ v (t (σ b)).1 ≤ v (t (σ a)).1 * exp 1) : l (ρ (diagGL t * permGL σ) y) = ξ t * l (ρ (permGL σ) y) := by
  have key {d} hd s (e : s = 1 ∨ s = t) := (map_compactMean_of_factor hl.w1 fun g k ↦
   (exists_iwasawa_bruhat g).imp fun _ _ ↦ ⟨conj_unitriangular_mem_proIwahori hd (by tauto), by
   simpa using hz ⟨_, o (diagGL_mul_permGL s σ ▸ s11_w9 _ σ
    _ (s11_q8.1 (mul_mem (inv_mem (by tauto)) k)) (by
    cases e <;> simp_all [← log_le_log] <;> grind [σ.injective, le_total]))⟩⟩) ▸ @hl d hd _
  have ⟨s, hs, _⟩ := exists_iwahoriHeckeHom_injective ρ hϖ; have ⟨k, h⟩ := (v7 hs t).exists; simpa [key (pow_mem hs.monotone k), mul_assoc, -map_pow] using key h 1
end
open Module ComplexOrder Equiv Matrix Pi Submodule Units Valued WithZero Filter.Germ Submonoid.LocalizationMap
attribute [-simp] Fin.val_rev map_pow WithZero.inv_exp
attribute [local simp] LinearMap.domRestrict₁₂_apply Monotone mulSingle_apply mulSingle_comp_equiv diagGL_mem_intGL normAbsChar transvectionGL_mem_proIwahori WithZero.exp_neg
variable {F : Type*} [Field F] [Valued F _] [CompactSpace 𝒪[F]] {N} {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] {ϖ : Fˣ} {θ l x} {τ : _ → ℂ} (hϖ : v ϖ.1 = exp (-1)) (hx : x ∈ levelSpace ρ.ρ proIwahori) (hτ : ∀ t, diagGL t ∈ intGL _ 𝒪[F] → ρ (diagGL t) x = τ t • x) (hP : ∀ σ, (∀ i ε, v ε.1 = 1 → τ (mulSingle i ε) = τ (mulSingle (σ i) ε)) → ∃ c : ℂ, ρ (permGL σ) x = c • x)
include hϖ hx hτ hP in
lemma IsExponent.b2 (hl : IsExponent ρ (torusChar θ) l) (h0 : l x ≠ 0) : ∃ σ : Perm _, (∃ l, IsExponent ρ (torusChar (θ ∘ σ)) l ∧ l (ρ (permGL σ⁻¹) x) ≠ 0) ∧ Antitone ((‖θ · ϖ |>.1‖) ∘ σ) := exists_antitone_of_swap _ _ ⟨1, l, hl, by simpa⟩ fun σ i j c hf ⟨l, hl, h0⟩ ↦ by
  have ⟨h, n, k⟩ : i < j ∧ i ≠ j ∧ i.rev.1 = j.rev + 1 := by simp at c; grind
  let π := σ * swap i j; set y := ρ _ x; set ξ := torusChar (θ ∘ σ)
  have χ t : torusChar (θ ∘ π) t = ξ (t ∘ swap i j) * normAbsChar
   (t i / t j) := by
   ext; induction t using mulSingle_induction <;> simp [-normAbsChar, mul_comp, ξ, field, *]
   grind [Perm.mul_apply, val_one]
  let s := l ∘ₗ ρ (permGL (swap i j))
  have h1 : s y ≠ 0 := by simpa [y, s, -swap_inv]
  let S := s ∘ₗ compactMean ρ.ρ proIwahori; let U t := ρ (diagGL t) * compactMean ρ.ρ proIwahori
  have D t (ht : t ∈ dominantTorus) (e : log (v (t j / t i).1) ≤ 1) z : _ = ξ (t ∘ swap i j) * S
   z := .trans (by simp [↓diagGL_mul_permGL, Function.comp_def]; rfl) (hl.v0
   hϖ (compactMean_mem_levelSpace _) s11_q8.2 _
   (by simp_all [dominantTorus, log_le_iff_le_exp]; grind))
  let w := (if · < j then ϖ else 1)
  have hw : w ∈ dominantTorus := by simp +decide [dominantTorus, w, apply_ite, ite_apply, *]; omega
  have K : w ∘ swap i j = w * mulSingle j ϖ * mulSingle i ϖ⁻¹ := by ext; simp [w]; grind
  have T {a b t c z} {h : a ≠ b} (H : transvectionGL h ((t b).1 / (t a).1 * c) ∈ proIwahori) :
   ρ (transvectionGL h c) (U t z) =
   U t z := by simpa [U, H] using congr(ρ $((by ext; simp [transvection]; grind [ne_zero] :
   transvectionGL h c * diagGL t = diagGL t * (⟨_, H⟩ : proIwahori))) (U 1 z))
  have W {y} (hy : ∀ a, v a ≤ 1 → ρ (transvectionGL n a) y = y) : S y = s y :=
   map_compactMean_of_factor hl.w1 fun k o ↦
   (k0 c o).imp' _ fun c ↦ (⟨·, by simp [hy _ c.2]⟩)
  have G z κ : _ → _ • S _ = _ + _ := D w hw (by simp [w, *]) z ▸ x0 c κ
   hl.w1 fun _ a ↦ T (by simp +decide [w, field, a.trans_lt, *])
  have P t (ht : t ∈ dominantTorus) z (h0 : l z = 0) : S (U t z) = torusChar (θ ∘ π) t * S z := by
   induction' e : (v (t j / t i).1).log.toNat with _ ih generalizing t z
   · simp [(ht h.le).ge_iff_eq] at e; simpa [χ, e, ← D _ ht] using! W fun _ _ ↦ T (by simp [*])
   refine div_mul_cancel t w ▸ congr(s $(iwahori_operator_mul ?e hw
    (compactMean_mem_levelSpace z))).symm.trans ((ih _ ?e _
    (by simp [*]) ?_).trans (by simpa [χ w, w, field, hϖ, h] using! G z 0 (by
    simp +contextual [↓hl.z5, U, *])))
   all_goals simp [dominantTorus, w, ← log_le_log, apply_ite, *] at ht e c ⊢; clear * - ht e c; rcases @ht j, (@ht · i); grind
  use S ∘ₗ (U w - (ξ w).1 • 1), fun d e z ↦ .trans
   (by simp [S, U, iwahori_operator_mul, mul_comm, *]) (P d e _ (by simp [U, *]))
  simp_intro H
  cases hP (swap (σ i) (σ j)) fun a ε _ ↦ by
   by_contra; have Z π := congr(l (ρ $(diagGL_mul_permGL (mulSingle (σ⁻¹ a) ε) π⁻¹) x)); simp [apply_ite, hl.z5, *] at Z; have z0 := (Z π).resolve_left (by simpa [π, mul_swap_eq_swap_mul, (Z σ).resolve_right h0])
   grind [by simpa [P w hw y z0, ξ, w, *, mul_assoc] using H, (π.injective.ne n).lt_or_gt.elim
    (z8 hx · |> W |>.trans_ne h1) fun C ↦ right_ne_zero_of_smul
    ((x0 c 0 hl.w1 (z8 hx C)
    (by simp +contextual [↓hl.z5, *])).trans_ne (by simpa))]
  have E {a b} (p : σ a < σ b ∨ π a < π b) h c k : ρ (transvectionGL h c) y = y := p.rec (by simp
      [y, mul_swap_eq_swap_mul σ, -map_inv, z8 hx ·, *]) (z8 hx · c k)
  simp [NeZero.ne, (by simpa [W (E _ n), π, ξ, *, field, pow_succ, ← sub_eq_iff_eq_add] using
   (G y (ξ w * s y) fun u _ _ ↦ by simpa [hl.z5, apply_ite, U, field, π, n.symm, hl.w1, *] using! (congr(l (ρ $(p4 n u) y)).symm)))] at hf
variable {B} (hB : IsUnitary ρ.ρ B) [Module.Finite ℂ ((cyclicSpan ρ.ρ x).submoduleOf (levelSpace ρ.ρ proIwahori))]
lemma IsIwahoriEigen.exists_isExponent (hB : IsUnitary ρ.ρ B) {ξ y} (H : IsIwahoriEigen ρ ξ y) (hy : y ∈ cyclicSpan ρ.ρ x) : ∃ w ∈ cyclicSpan ρ.ρ x, B w w ≠ 0 ∧ IsExponent ρ ξ (B w) := by
  obtain ⟨_, ⟨w, h, rfl⟩, z, e⟩ := exists_eigenvector_of_functional' (iwahoriHeckeHom ρ · |>.dualMap)
   (S := .map (B.domRestrict₁₂ ..) ((cyclicSpan _ x).submoduleOf _)) (fun | t, _, ⟨w, h, rfl⟩ => ⟨⟨_,
    compactMean_mem_levelSpace _⟩, compactMean_mem_cyclicSpan (diagGL t)⁻¹ h, by ext; simp [hB.adjoint_eq_inv, hB.compactMean_adjoint, ← hB.compactMean_adjoint w, iwahoriHeckeHom]⟩) (fun _
   _ l _ ↦ congr(l ∘ₗ $((Commute.all ..).map (iwahoriHeckeHom ρ)))) (.applyₗ ⟨y, H.2.1⟩) ((hB.1 _ H.1).ne' <|
   · ⟨⟨y, H.2.1⟩, hy, rfl⟩) fun t l ↦ (l.congr_arg (Subtype.ext (H.2.2 _ t.2))).trans (l.2 ..)
  use w, h, (hB.1 w fun _ ↦ by simp_all).ne', fun _ a z ↦
   by simpa [← hB.compactMean_adjoint, iwahoriHeckeHom] using congr($(e ⟨_, a⟩) ⟨_,
   compactMean_mem_levelSpace z⟩)
include hϖ hx hτ hP hB in
lemma exists_sorted_of_type (h0 : x ≠ 0) : ∃ θ, (∃ l, IsExponent ρ (torusChar θ) l ∧ l x ≠ 0) ∧ (∀ i ε, v ε.1 = 1 → θ i ε = τ (mulSingle i ε)) ∧ ∃ σ : Perm _, Antitone ((‖θ · ϖ |>.1‖) ∘ σ) ∧ ∃ y ∈ cyclicSpan ρ.ρ x, IsIwahoriEigen ρ (torusChar (θ ∘ σ)) y := by
  have ⟨s, ht, I⟩ := exists_iwahoriHeckeHom_injective ρ hϖ
  have R t : (cyclicSpan _ x).submoduleOf _ ∈ (iwahoriHeckeHom ρ t).invtSubmodule := fun _ ↦
   compactMean_mem_cyclicSpan _
  have ⟨χ, y, ⟨Y, Q⟩, z, e⟩ := exists_eigencharacter (S := _ ⊓ ⨅ (i) (ε : Fˣ) (h : v ε.1 = 1),
   (iwahoriHeckeHom ρ ⟨mulSingle i ε, by simp [dominantTorus, apply_ite, h]⟩).eigenspace
   (τ (mulSingle i ε))) _ (fun t y h ↦
   ⟨R t h.1, by simp [← End.mul_apply, ← map_mul, mul_comm]; aesop⟩) (h0 congr($(@· ⟨x, hx⟩
   ⟨self_mem_cyclicSpan, by aesop (add simp [iwahoriHeckeHom, apply_ite])⟩)))
  have ⟨θ, c⟩ : ∃ θ, ∀ t, χ t = torusChar θ t :=
   ⟨torusChar.2 (AwayMap.lift ⟨s, _⟩ (dominantTorus.subtype.toLocalizationMap (Group.isUnit ·.1.1)
   (v7 ht · |>.exists.rec fun k ↦ (⟨⟨⟨_, ·⟩, _, k, rfl⟩,
   by ac_rfl⟩)) (by simp)) (by simpa [*] using I.ne z)).toHomUnits, fun t ↦ by simp; erw [lift_eq]⟩
  simp +contextual [smul_left_inj, *] at Q e; have ⟨w, Y, z, hl⟩ := IsIwahoriEigen.exists_isExponent hB ⟨by simpa, y.2, (congr($(e · ·)))⟩ Y
  refine ⟨θ, ⟨_, hl, ?o⟩, Q, (hl.b2 hϖ hx hτ hP ?o).imp fun σ ⟨⟨l, L, h⟩, H⟩ ↦ ⟨H,
   (exists_eigenvector_of_functional' _ R (by simp [← End.mul_apply, ← map_mul, mul_comm])
   (l.domRestrict _) (h <| L.apply_compactMean ▸ @· ⟨_, compactMean_mem_levelSpace _⟩
   (compactMean_mem_cyclicSpan _ self_mem_cyclicSpan)) fun m z ↦ L.apply_compactMean ▸
   compactMean_eq_self _ z.2 ▸ L m.2 _).rec fun y ⟨Y, z, G⟩ ↦
   ⟨y, Y, by simpa, y.2, (congr($(G ⟨·, ·⟩)))⟩⟩⟩
  refine fun o ↦ (coe_eq.1 (span_le (p := ((RingHom.ker
   (coeRingHom (R := ℂ) (.atTop : Filter ℕ))).restrictScalars
   _).comap (.pi fun n ↦ B w ∘ₗ ρ (diagGL (s ^ n)))).2 (Set.range_subset_iff.2 fun g ↦ coe_eq.2 ?_)
   (compactMean_mem_cyclicSpan (K :=
   proIwahori) 1 Y))).exists.rec (by simp [hl (pow_mem ht.monotone _), z])
  have ⟨u, _, ⟨t, σ, k⟩, _⟩ := exists_iwasawa_bruhat g
  filter_upwards [k7 ht u, v7 ht t] with n a d
  simpa [by simpa using hx ⟨_, k⟩, (by_contra fun h ↦ (hP σ fun i ε _ ↦ by simpa [*, hl.z5, apply_ite] using (congr(B w (ρ $(diagGL_mul_permGL (mulSingle (σ i) ε) σ)
   x)).symm)).rec (by aesop) : B w (ρ (permGL σ) x) = 0)] using (hl.w1 (MulAut.conj
   (diagGL (s ^ n)) u) (by simp_all [mem_proIwahori_iff_of_unitriangular, diagGL, field]) _).trans (hl.v0 hϖ hx s11_q8.2
   σ fun _ _ h ↦ .inl (d h.le))
