import Lib.General.LinearAlgebra.CommonEigenvectors
section
open Algebra ConjAct Fintype IsArtinianRing LinearMap Matrix Pi Submodule Units
attribute [local simp ←] single_mul_left
attribute [local simp] sum_sigma Matrix.mul_assoc Matrix.mul_sum Matrix.sum_mul
variable {k G H n N B : Type} [Field k] [Group G] [Fintype n] [Fintype N] {m} {d : Fin m → ℕ} {r : G →* GL n k} [∀ i, NeZero (d i)]
private abbrev m9 k (d : Fin m → ℕ) := ∀ i, Matrix (Fin (d i)) (Fin (d i)) k
@[simps!] noncomputable def blockDiagonalAlgHom {R o} {m : o → Type} [CommRing R] [DecidableEq o] [Fintype o] [∀ i, Fintype (m i)] : (∀ i, Matrix (m i) (m i) R) →ₐ[R] Matrix (Σ i, m i) (Σ i, m i) R := .mk' (by use! blockDiagonal' <;> simp [Pi.mul_def]) (by simp)
noncomputable abbrev n1 i (a b : Fin (d i) := 0) : m9 k d := single i (single a b 1)
lemma n3 : ∑ i, ∑ a, (n1 i a a : m9 k d) = 1 := funext (by simp_all [sum_eq_single ·, sum_single_one])
variable {p : Matrix n n k} (f : m9 k d →ₐ[k] Matrix N N k) (f' : m9 k d →ₐ[k] Matrix n n k) [CharZero k] [IsAlgClosed k] [Ring B] [Group H] [Algebra k B] [Module.Finite k B] (ρ : G →* B)
lemma n4 (e : IsIdempotentElem p) : p.trace = p.rank ∧ (p = 0 ↔ p.trace = 0) := by
 simp [p.trace_toLin'_eq ▸ (e.map toLinAlgEquiv').isProj_range.trace, range_eq_bot]; rfl
attribute [local ext] ext_linearMap
omit [CharZero k] [IsAlgClosed k] [Module.Finite k B] in
lemma n5 (f : m9 k d →ₐ[k] B) i : IsIdempotentElem (f (n1 i)) := .map (symm (by simp)) f
omit [∀ i, NeZero (d i)] in
lemma IsTraceNondeg.n6 {s} (u : span k (.range s) = ⊤) (e : ∀ g, f' (s g) = r g) : IsTraceNondeg r := fun x hx h ↦ (mem_span.1 hx f'.range.toSubmodule (by aesop)).rec fun a E ↦ by
 choose c he b hb using by simpa [le_antisymm_iff, mem_span_singleton] using IsSemisimpleRing.ideal_eq_span_idempotent (_ ∙ a)
 rw [← E, ← hb, map_mul, (n4 (he.map _)).2.2, mul_zero]
 refine closure_induction ?_ ?_ ?_ (u.ge ⟨⟩ : c ∈ _) <;> simp_all [x.trace_mul_comm, add_mul]
private lemma n7 {s : G →* m9 k d} (u : span k (.range s) = ⊤) (τ : m9 k d →ₗ[k] k) (c : ∀ x y, τ (x * y) = τ (y * x)) (h : ∀ i, ∃ m : ℕ, τ (n1 i) = m) (e : τ 1 = card n) : ∃ r, IsTraceNondeg (n := n) r ∧ ∀ g, (r g).1.trace = τ (s g) := by
 choose m h using h
 obtain rfl : τ = lsum k _ k (m · • traceLinearMap ..); ext i a b; by_cases a = b <;> simpa [-lsum_apply, lsum_piSingle, eq_comm, *] using c (n1 i a) (n1 i 0 b)
 exact (fun φ ↦ (⟨.toHomUnits (.comp φ s), .n6 φ u (by simp), ·⟩)) ((reindexAlgEquiv k k (equivOfCardEq (by simp_all [← @Nat.cast_inj k]))).toAlgHom.comp (.comp blockDiagonalAlgHom (.pi (evalAlgHom k _ <| @Sigma.fst _ (Fin <| m ·) ·))))
  (by simp +instances [-coe_reindexAlgEquiv, trace_blockDiagonal'])
noncomputable def intertwiner (U : _ → Matrix N n k) := ∑ i, ∑ a, f (n1 i a) * U i * f' (n1 i 0 a)
section
omit [CharZero k] [IsAlgClosed k]
lemma n8 U i a b : let x := f (n1 i a) * U i * f' (n1 i 0 b)
 intertwiner f f' U * f' (n1 i a b) = x ∧ f (n1 i a b) * intertwiner f f' U = x := by simp_all [intertwiner, ← map_mul, ← (f _).mul_assoc (f _), eq_comm, sum_eq_single i, sum_eq_single a, sum_eq_single b]
lemma n9 U z : f z * intertwiner f f' U = intertwiner f f' U * f' z := (Pi.basis fun _ ↦ stdBasis
 ..).sum_repr z ▸ by simp [sum_prod_type, stdBasis_eq_single, n8]
lemma k3 (h : ∀ i, (f' (n1 i)).rank ≤ (f (n1 i)).rank) : ∃ (P : Matrix N n k) (Q : Matrix n N k), Q * P = 1 ∧ ∀ z, f z * P = P * f' z := by
 choose J j using (finrank_le_iff_exists_linearMap.1 <| h ·)
 choose U u using (J · |> (Module.projective_lifting_property _ · (surjective_rangeRestrict _)))
 choose L l using (Submodule.subtype _ ∘ₗ J · |>.exists_leftInverse_of_injective (by aesop))
 refine ⟨_, intertwiner f' f (Submodule.subtype _ ∘ₗ L · |>.toMatrix'), ?_, n9 f _ (U · ∘ₗ rangeRestrict _ |>.toMatrix')⟩
 simp_all [intertwiner.eq_1 f', n8, ext_iff_mulVec, ← mulVec_mulVec, sum_mulVec, DFunLike.ext_iff, ← SetLike.coe_eq_coe, -Subtype.forall]
 simp [← sum_mulVec, ← map_mul, ← map_sum, n3]
end
variable (k) in
def HasSemiprimeSpan := ∀ x ∈ span k (.range ρ), (∀ g, x * ρ g * x = 0) → x = 0
lemma s08_k4 (f : H →* G) (h : HasSemiprimeSpan k ρ) (hf : f.range.Normal := by exact ⟨by simp⟩) : ∃ b d, ∃ (_ : ∀ i : Fin b, NeZero (d i)) (s : H →* m9 k d) (F : _ →ₐ[k] B), (∀ i, F (n1 i) ≠ 0) ∧ span k (Set.range s) = ⊤ ∧ ∀ g, F (s g) = ρ (f g) := let A := adjoin k (Set.range (ρ.comp f))
  have u := MonoidHom.mclosure_range (ρ.comp f) ▸ adjoin_eq_span k _
  have := of_finite k A
  have c g : A ≤ A.comap (MulSemiringAction.toAlgHom k B (toConjAct (ρ.toHomUnits g))) := adjoin_le fun _ ⟨y, _⟩ ↦ subset_adjoin ((hf.1 _ ⟨y, rfl⟩ g).imp (by aesop))
  have ⟨_, d, h, ⟨e⟩⟩ := (isSemisimpleRing_iff_jacobson.2
    ((eq_bot_or_exists_atom_le _).resolve_right fun ⟨_, a, l⟩ ↦ a.bot_lt.2 fun (x : A) m ↦ x.ext (h _ (span_mono (by simp) (u.le x.2)) fun g ↦ by
    simpa [units_smul_def, mul_assoc, Subtype.ext_iff] using (a.2 _ (FG.of_finite.jacobson_smul_lt
      a.1)).le (smul_mem_smul (@Ring.le_comap_jacobson _ _ _ _ (.restrict _ _ _ (c g⁻¹)) ⟨(⟨⟨_, c g
      ·.2⟩, by aesop⟩)⟩ _ (l m)) m)))).exists_algEquiv_pi_matrix_of_isAlgClosed k
  have e : A ≃ₐ[k] m9 k d := by convert! e
  ⟨_, _, h, .comp e ((ρ.comp f).codRestrict A (by bound)), A.val.comp e.symm, by
  erw [Set.range_comp e, span_image e.toLinearMap, (span_range_subtype_eq_top_iff ..).2 u.symm]
  simp [← ext_iff, Matrix.single]⟩
omit [CharZero k] [IsAlgClosed k] in
lemma IsTraceNondeg.hasSemiprimeSpan (h : IsTraceNondeg r) : HasSemiprimeSpan k ((coeHom _).comp r) := (h · · ∘ fun H g ↦ (Matrix.isNilpotent_trace_of_isNilpotent ⟨2, by erw [sq, ← mul_assoc, H, zero_mul]⟩).eq_zero)
lemma IsTraceNondeg.comp (h : IsTraceNondeg r) (f : H →* G) (hf : f.range.Normal := by simp <;> infer_instance) :
 IsTraceNondeg (r.comp f) := let ⟨_, _, _, _, F, h⟩ := s08_k4 _ f h.hasSemiprimeSpan hf
 h.2.elim (n6 F)
lemma IsTraceNondeg.exists_conj_of_trace_eq (h : IsTraceNondeg r) (φ : B →ₐ[k] _) (j : HasSemiprimeSpan k ρ) (t : ∀ g, (r g).1.trace = (φ (ρ g)).trace) : ∃ P : GL n k, ∀ g, (r g).1 * P = P * φ (ρ g) := have ⟨_, _, _, s, f, _, u, a⟩ := s08_k4 (((coeHom _).comp r).prod ρ) (.id G) fun x m ↦ by simp_all [Prod.ext_iff, (span_prod_le _ _ (span_mono _ m)).imp (h.hasSemiprimeSpan _) (j _)]
 have ⟨_, _, e, H⟩ := k3 (.comp (.fst ..) f) (φ.comp (.comp (.snd ..) f)) fun i ↦ Eq.le (by simp only [← @Nat.cast_inj k, ← n4, n5]; refine closure_induction ?_ ?_ ?_ (u.ge ⟨⟩ : n1 i ∈ _) <;> simp_all)
 ⟨⟨_, _, mul_eq_one_symm e, e⟩, (by simpa [a] using H <| s ·)⟩
omit [CharZero k] [IsAlgClosed k] in
lemma IsTraceNondeg.k5 [TopologicalSpace k] [IsTopologicalRing k] [TopologicalSpace G] [IsTopologicalGroup G] (h : IsTraceNondeg r) (hc : Continuous (r · |>.1.trace)) : Continuous r := .of_coeHom_comp (continuous_matrix fun i j ↦ mem_span.1
 (FiniteDimensional.mem_span_of_iInf_ker_le_ker (K := (entryLinearMap k k i j).domRestrict (span
 k (Set.range (r ·)))) (L := fun g ↦ (traceLinearMap .. ∘ₗ .mulRight _ ↑(r g)).domRestrict _)
 (by simp_all [IsTraceNondeg, LE.le])) ((continuousSubmodule ..).comap (.pi (applyₗ ⟨r ·, by aesop⟩))) (by simpa using! hc.comp' ∘' continuous_mul_const))
end
section
section
variable {k G m : Type} [Field k] [Group G] [Fintype m] (μ : G →* kˣ) (R : G →* GL m k)
noncomputable abbrev twistByChar := MonoidHom.mk' (fun g ↦ μ g • R g) (by aesop (add simp smul_mul_smul))
lemma IsTraceNondeg.twist {R : G →* GL m k} (h : IsTraceNondeg R) μ : IsTraceNondeg (twistByChar μ R) := by simp_all [IsTraceNondeg, Submodule.mem_span, Units.smul_def]
lemma IsTraceNondeg.t5 {n t : Type} [Fintype n] [Fintype t] [CharZero k] [IsAlgClosed k] (hN : Fintype.card m = Fintype.card n + Fintype.card t) {r : _ → G →* GL m k} (h : ∀ i, IsTraceNondeg (r i)) {ψ : Fin 2 → t → G →* kˣ} (hne : ∀ i j, ψ 0 i ≠ ψ 1 j) {T : G → k} (ht : ∀ i g, (r i g).1.trace = T g + ∑ j, (ψ i j g).1) : ∃ s : G →* GL n k, IsTraceNondeg s ∧ ∀ g, T g = (s g).1.trace := by
 choose _ _ _ s f _ u a using s08_k4 (k := k) ⟨⟨fun g i ↦ ((r i g).1, (ψ i · g |>.1)), by aesop⟩, by bound⟩ (.id _) fun x m ↦ by simp_all [funext_iff, Prod.ext_iff, forall_and, fun i ↦ (h i).hasSemiprimeSpan (x i).1 (by induction m using Submodule.span_induction <;> aesop)]
 let τ i := (Matrix.traceLinearMap ..).coprod (-∑ j, .proj j) ∘ₗ .proj i ∘ₗ f.toLinearMap
 exact (n7 u (τ 0) (by simp [τ]; grind [Matrix.trace_mul_comm]) (fun i ↦ by
  by_contra H; choose j _ using fun o ↦ Function.ne_iff.1 fun E : (f (n1 i) o).2 = 0 ↦ H (by simp [τ, E, n4 congr(($(n5 f i) o).1), (LinearMap.ext_on_range u (by simp_all) : τ 0 = τ o)])
  have (g) o := congr((f $(show n1 i * (s g - s g i 0 0 • 1) * n1 i = 0 by
   simp [← Pi.single_mul_left]) o).2 (j o))
  exact hne (j 0) (j 1) (by ext; simp_all)) (by aesop)).imp (by aesop)
open Matrix Polynomial IsAlgClosed
variable {k : _} {n} [Field k] [IsAlgClosed k] [Fintype n] (A : Matrix n n k)
lemma det_aeval_neg_eq_prod_roots q : (aeval (-A) q).det = (A.charpoly.roots.map (q.eval <| -·)).prod := by refine Submonoid.closure_induction_left ?_ ?_ (splits q) <;> simp_all [or_imp, forall_and, ← (splits _).eval_eq_prod_roots_of_monic, charpoly_monic, card_roots_eq_natDegree, neg_add_eq_sub, eval_charpoly, algebraMap]
lemma t6 m : (A ^ m).trace = (A.charpoly.roots.map (· ^ m)).sum := by
 rw [trace_eq_sum_roots_charpoly, (charpoly _).funext, roots_multiset_prod_X_sub_C]
 simpa [eval_charpoly, eval_multiset_prod] using! (det_aeval_neg_eq_prod_roots A <| C · - (-X) ^ m :)
lemma charpoly_eq_mul_of_trace_pow_add [CharZero k] {r ι} [Fintype r] {B : Matrix r r k} S (α : ι → k) (h : ∀ m, (A ^ m).trace = (B ^ m).trace + ∑ e ∈ S, α e ^ m) : A.charpoly = B.charpoly * ∏ e ∈ S, (X - C (α e)) :=
 have H s t := by simpa [Finsupp.linearCombination, Finsupp.sum, -nsmul_eq_mul, ← Finset.sum_multiset_map_count] using (Multiset.toFinsupp.injective <| ((linearIndependent_monoidHom ..).comp _ (powersHom k).injective).restrict_scalars' ℕ · : _ → s = t)
 funext (by simp [eval_prod, (splits _).eval_eq_prod_roots_of_monic, charpoly_monic, H _ (_ + S.1.map α) (funext (by simpa [Pi.multiset_sum_apply, t6] using! h))])
end
open Filter MvPolynomial Finset Submodule Metric Matrix MonoidAlgebra Ideal.Quotient LinearMap Module IsAlgClosed IsUniformAddGroup
variable {k K G n ι : Type} [Field k] [NormedField K] [Group G] [Fintype n] (S : Set (ι → K))
def t7 : Submodule K (ι → K) := (topologicalClosure (M := UniformFun ..) (span K S) :)
variable {S f}
lemma t8 : f ∈ t7 S ↔ ∀ ε > 0, ∃ g ∈ span K S, ∀ x, ‖f x - g x‖ ≤ ε := by simpa [dist_eq_norm] using! mem_closure_iff_nhds_basis (UniformFun.hasBasis_nhds_of_basis _ _ f uniformity_basis_dist_le)
def t9 (s : Set.Ioi (0 : ℝ) → ℕ) (c : ∀ _, _ → K) (N : Submonoid (K × ((Σ η, Fin (s η)) → K))) := IsClosed N.carrier ∧ TendstoUniformly (fun η (p : N) ↦ ∑ i, c η i * p.1.2 ⟨η, i⟩) (·.1.1) atBot
lemma s08_m3 (hf : f ≠ 0) (h : f ∈ t7 S) : ∃ s c N, t9 s c N ∧ ∃ y : _ → S, ∀ p : K × (_ → K), (∃ T : End K (ι → K), (∀ f r, (∀ x, ‖f x‖ ≤ r) → ∀ x, ‖T f x‖ ≤ r) ∧ T f = p.1 • f ∧ ∀ i, T (y i) = p.2 i • y i) → p ∈ N := (Function.ne_iff.1 hf).elim fun z (o : _ ≠ 0) ↦ by
  choose s a y b using Subtype.forall'.1 (by
    simpa [mem_span_set', t8, ↓← Pi.sub_apply] using smul_mem _ (f z)⁻¹ h)
  refine ⟨s, _, .topologicalClosure ⟨⟨_, (·.rec fun T _ ↦ .imp' (· * T) (by simp_all [mul_smul]))⟩, .intro 1 (by simp)⟩, ⟨isClosed_closure, tendstoUniformly_iff.2 (eventually_lt_atBot ⟨·, ·⟩
    |>.mono fun η e p ↦ (le_on_closure (by rintro q ⟨T, t, _, v⟩; simpa [v ⟨η, _⟩, *, ← dist_eq_norm, mul_comm, ← mul_assoc] using t _ _ (b η) z) ?_ ?_ p.2).trans_lt e)⟩, (·.rec y), subset_closure⟩ <;> fun_prop
attribute [local simp] Multiset.esymm det_apply DFunLike.ext_iff Finsupp.sum lift_apply Function.comp_def mul_assoc Prod.fst_prod Prod.snd_prod eval_monomial mul_sum Finsupp.prod
lemma t9.m4 {P s c N} (h : t9 s c N) (B : MvPolynomial ι K) (f : P → ι → N) : TendstoUniformly (fun η p ↦ ∑ i, c η i * B.eval (f p · |>.1.2 ⟨η, i⟩)) (fun p ↦ B.eval (f p · |>.1.1)) atBot := B.induction_on' (fun m a ↦ by
 simpa [mul_left_comm] using (uniformContinuous_mul_left' a).comp_tendstoUniformly (h.2.comp
 fun p ↦ m.prod (f p · ^ ·))) fun _ _ ↦ by simpa [mul_add] using .add
noncomputable def s08_m5 : ℕ → ℕ → MvPolynomial ℕ k := Nat.rec 1 fun j b m ↦ X m * b 1 - j • b (m + 1)
lemma fs_m6 (s : Multiset k) : ∀ j, eval (fun m ↦ (s.map (· ^ m)).sum) (s08_m5 j 1) = j.factorial * s.esymm j :=
 have (a : k) p j : ∀ m, eval (fun m ↦ a ^ m + p m) (s08_m5 j.succ m) = eval p (s08_m5 j.succ m + j • a • s08_m5 j m + a ^ m • s08_m5 j 1) ∧ (s08_m5 j.succ m).constantCoeff = (0 : k) := by induction j with (simp_all [s08_m5]; grind)
 by induction s using Multiset.induction with rintro ⟨⟩ <;> simp! [*, this 0 0, s08_m5.eq_1 0, Multiset.sum_map_mul_left, Multiset.powersetCard_zero_right] <;> ring
lemma s08_m7 [IsAlgClosed k] [CharZero k] {T} (h : ∀ B, (∀ x : G →* GL n k, eval (x ·
    |>.1.trace) B = 0) → eval T B = 0) : ∃ r, IsTraceNondeg (n := n) r ∧ ∀ g, (r g).1.trace = T g := by
  let t := (aeval T).toLinearMap ∘ₗ Finsupp.lift _ k G X ∘ₗ (coeffLinearEquiv k).1
  have h B (b : ∀ ρ : _ →ₐ[k] _, eval (trace <| ρ ·) B = 0) : B.eval t = 0 := B.aeval_bind₁ T _ ▸ h _ (by simpa [← aeval_eq_eval, aeval_bind₁] using b <| lift _ _ _ <| (Units.coeHom _).comp ·)
  have c x y := by simpa [@trace_mul_comm n n] using h (X (x * y - y * x))
  let I : Ideal _ := ⟨((mul k _).compr₂ t).ker.1, (by simp_all [c ·])⟩
  have : I.IsTwoSided := ⟨by aesop⟩
  let τ : _ ⧸ I →ₗ[k] _ := liftQ _ t (mul_one · ▸ congr($(·) 1))
  have hN l : ∀ x, (∀ m, x ^ m.succ = l ^ m • x) → ∃ j : ℕ, τ x = j * l := mk_surjective.forall.2
    fun x _ ↦ have e j : ∀ m, (s08_m5 j.succ m.succ).eval (τ <| x ^ ·) = l ^ m * ∏ i ∈ range (j + 1), (τ x - i * l) := by induction j with simp_all [s08_m5, prod_range_succ] <;> grind [‹∀ _, _› 0]
    by grind [e (Fintype.card n) 0 ▸ eval_rename (x ^ ·) t _ ▸ h _ (by simp [eval_rename, fs_m6, t6, card_roots_eq_natDegree]), prod_eq_zero_iff]
  have : Module.Finite k (_ ⧸ I) := rank_lt_aleph0_iff.1 (.trans' Cardinal.natCast_lt_aleph0 (not_le.1
    ((le_rank_iff.trans mk_surjective.comp_left.exists).not.2 (·.rec fun (s : Fin (Module.finrank k
    (Matrix n n k) + 1) → _) l ↦ minors_eq_zero_iff.1 (fun b ↦ by simpa using! h (of (X <| s · * b ·))ᵀ.det (by simpa using! minors_eq_zero_iff.2 (mt (·.of_comp (pi (traceLinearMap n k k ∘ₗ mulRight k ·)) |>.fintype_card_le_finrank) (by simp)) <| · ∘ b)) ((l.map' _ (ker_liftQ_eq_bot' _ _ rfl)).map' (ltoFun ..) (by aesop))))))
  choose _ _ _ s f _ u _ using s08_k4 (k := k) ((mk I).1.comp (of ..))
    (.id G) (mk_surjective.forall.2 fun x _ _ ↦ eq_zero_iff_mem.2 (by
    ext; simpa using! hN 0 ↑(x * _) (by cases · with simp_all [pow_succ', ← mul_assoc])))
  peel n7 u (τ ∘ₗ f) (by simpa using fun x y ↦ (f x).ind₂ c (f y)) (by
    simpa using hN 1 _ <| by simp [n5 f · |>.pow_succ_eq])
      (by simpa using! (h (X 1 - ∑ _ : n, 1):))
  simp_all; show t _ = _; aesop
lemma s08_m8 [TopologicalSpace G] [IsTopologicalGroup G] [IsAlgClosed K] [CharZero K] {s c N} (h : t9 s c N) (F : G → Filter N) [∀ g, (F g).NeBot] {L} (hL : IsComplete L) (w : ∀ g, ∀ᶠ p in F g, p.1.1 ∈ L) {r : _ → G →* GL n K} (hr : ∀ x, Continuous (r x)) (hφ : ∀ g x, (F g).Tendsto (·.1.2 x) (nhds (r x g).1.trace)) : ∃ R : G →* GL n K, Continuous R ∧ IsTraceNondeg R ∧ ∀ g, ((R g).1.trace, (r · g |>.1.trace)) ∈ N := by
 choose T _ hT using fun g ↦ hL _ ((cauchy_map_iff_tendsto ..).2 ⟨map_neBot, ((h.2.comp _).sub
  (h.2.comp _)).tendsto_of_eventually_tendsto (univ_mem' fun _ ↦ ((cauchy_map_iff_tendsto ..).1
  (tendsto_finsetSum _ fun _ _ ↦ (hφ g _).const_mul _).cauchy_map).2) (by simp)⟩)
  (tendsto_principal.2 (w g))
 have m g := h.1.mem_of_tendsto (.prodMk_nhds (hT g) (tendsto_pi_nhds.2 (hφ g))) (by simp)
 refine (s08_m7 fun D _ ↦ ?_).imp fun R ⟨n, e⟩ ↦ ⟨n.k5 (funext e ▸ (h.2.comp (⟨_, m ·⟩)).continuous (.of_forall (by fun_prop))), n, (e · ▸ m _)⟩
 simpa [*, eq_comm] using (h.m4 D ![(⟨_, m ·⟩)]).tendsto_at 0
lemma det_one_sub_smul_eq_prod_roots {n} [Fintype n] (N : Matrix n n ℂ) c : (1 - c • N).det = (N.charpoly.roots.map (1 - c * ·)).prod := by simpa using! det_aeval_neg_eq_prod_roots N (1 + c • .X)
lemma finsum_image_eq_zero_of_fibers {T C S} (hS : S.Finite) ψ {G : T → ℂ} {F : C → ℂ} {D} (h₀ : ∑ᶠ t ∈ S, G t = 0) (hN : ∀ t ∈ S, F (ψ t) / Nat.card {s ∈ S | ψ s = ψ t} = G t / D) : ∑ᶠ c ∈ ψ '' S, F c = 0 := by
 lift S to Finset T using hS; rw_mod_cast [finsum_mem_finset_eq_sum] at *; rw [S.sum_image', ← S.sum_div, h₀, zero_div D]
 intros; rw [Finset.sum_eq_card_nsmul, nsmul_eq_mul, mul_div_cancel₀] <;> simp_all [← hN]; tauto
end
