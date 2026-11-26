import Lib.Adelic.Witt.FrameAction
open Matrix Submodule Finset Pointwise Module
variable {O U V ι} [CommRing O] [AddCommGroup U] [Module O U] [AddCommGroup V] [Module O V]
  {M N P : Submodule O V} {M' N' : Submodule O U} {z z' a : O} {f : V →ₗ[O] V}
attribute [local simp] sum_smul_mem
variable (M N z) in
def IndexDvd := ∀ n (Φ : Fin n → V), (∀ k, Φ k ∈ M) → ∃ m, det m ∣ z ∧ ∀ i, ∑ k, m i k • Φ k ∈ N
lemma IndexDvd.comap (h : IndexDvd M N z) (f : U →ₗ[O] V) : M' ≤ M.comap f → (∀ x ∈ M', f x ∈ N →
  x ∈ N') → IndexDvd M' N' z := fun a _ _ _ c ↦ (h _ _ (a <| c ·)).imp (by aesop)
@[simp] lemma IndexDvd.of_le : M ≤ N → IndexDvd M N z := fun _ _ _ _ ↦ ⟨1, by aesop⟩
lemma IndexDvd.trans (h : IndexDvd M N z) (g : IndexDvd N P a) : IndexDvd M P (z * a) :=
  (h · · · |>.rec fun m b ↦
  (g _ _ b.2).imp' (· * m) (by simp_all [mul_comm, mul_dvd_mul, mul_smul, ← Module.smul_apply]))
lemma IndexDvd.map (h : IndexDvd M N z) (f : V →ₗ[O] U) : M' ≤ M.map f ⊔ N' → N.map f ≤ N' →
  IndexDvd M' N' z := by
  intro a b _ _ H; choose x hx y hy e using by simpa using (mem_sup.1 <| a <| H ·)
  peel h _ x hx
  simpa [← e, add_mem_cancel_right, hy] using b ⟨_, this, rfl⟩
lemma IndexDvd.sup {f : ι → V →ₗ[O] U} (h : ∀ i, IndexDvd M (.comap (f i) N') z) (s : Finset ι) :
    IndexDvd (span O (.image2 (f ·) s M ∪ N')) N' (z ^ #s) := s.cons_induction (by simp) fun i _
  _ ↦ by simp [pow_succ', *]; use ((h i).map _ (by order) (by simp [map_comap_eq])).trans
lemma IndexDvd.comp (e : M.map f ≤ M) : IndexDvd M (M.map f ⊔ a • M) z → IndexDvd M (N ⊔ a • M) z' →
  IndexDvd M (N.map f ⊔ a • M) (z * z') := (·.trans <| ·.map f (by order) (by grw [← e]; simp))
def HasType p M n (y : End O V) (c : ℝ) :=
  M.map y ≤ M ∧ ∃ l : ℕ, l ≤ c ∧ IndexDvd M (M.map y ⊔ p ^ n • M) (p ^ l)
lemma HasType.prod {s T t} (L : List ι) : (∀ l ∈ L, HasType z M s (T l) (t l)) →
    HasType z M s (L.map T).prod (L.map t).sum := by
  induction L <;> simp [HasType, End.one_eq_id, End.mul_eq_comp, map_comp]
  next I => exact fun e i _ _ H ↦
    (I H).imp (by grw [·, e]) (.imp' (i + ·) (by grind [IndexDvd.comp]))
lemma IndexDvd.of_det_dvd [IsDomain O] [ValuationRing O] [Fintype ι] {A : Matrix ι ι O} {N}
    (h : A.det ∣ z) (e : .map A.mulVecLin ⊤ ≤ N) : IndexDvd ⊤ N z := fun _ Φ _ ↦
  (isValuationPair_top.hermite (.refl _) (fromBlocks 1 (-of Φ) 0 Aᵀ) (1 ⊕ᵥ 0)).elim fun _ ⟨_, D, t,
  a, b⟩ ↦ ⟨_, .trans ⟨_, by simpa [mul_left_comm, (ext (by tauto) : D.toBlocks₁₂ = 0)] using
  (D.fromBlocks_toBlocks ▸ congr(($a).det) :)⟩ h, fun i ↦ e ⟨_ ∘ _, ⟨⟩, funext (by simpa [← b,
  toBlocks₁₁, mul_apply, mulVec_eq_sum, neg_add_eq_sub] using (@t (.inl i) <| .inr ·))⟩⟩
