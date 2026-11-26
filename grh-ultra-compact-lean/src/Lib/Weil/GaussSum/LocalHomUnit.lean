import Lib.General.LinearAlgebra.AdelicRingDefs
open AddChar Finset Function Matrix MulAction TensorProduct
lemma exists_primitive_residue_addChar {R F} [CommRing R] [CommRing F] {O : Subring F} {π : O →+* R} {g} {ψ : AddChar F ℂ} (h : Surjective π ∧ ∀ x, π x = 0 ↔ g * x.1 ∈ O) (hψ : ∀ t, (∀ s ∈ O, ψ (t * s) = 1) ↔ t ∈ O) : ∃ φ : AddChar R ℂ, φ.IsPrimitive ∧ ∀ x, φ (π x) = ψ (g * x) := by have e := FactorsThrough.extend_apply (f := π) (fun x y k ↦ eq_of_div_eq_one (by simpa [mul_sub, map_sub_eq_div] using (hψ (g * ↑(x - y))).2 (by grind) 1)) 1; use ⟨_, by simpa using e 0, ?_⟩ <;> simp [AddChar.IsPrimitive, h.1.forall, *, AddChar.ext_iff, ← map_mul, ← mul_assoc, ← map_add, mul_add, map_add_eq_mul, -not_forall]
variable {R a N} [CommRing R] [Fintype R] [Fintype a] [Fintype N] {ψ : AddChar R ℂ} (ψ' : AddChar R ℂ) {χ : MulChar R ℂ} {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) (f : Matrix N a R → ℂ) {n} [Fintype n]
noncomputable def matrixFourier (f : Matrix N a R → ℂ) (ρ : Matrix a N R) := ∑ v, f v * ψ' (ρ * v).trace
def IsPrimitiveMulChar (χ : MulChar R ℂ) := ∀ a ≠ 0, ∃ c, χ (1 + c * a) ≠ 0 ∧ χ (1 + c * a) ≠ 1
include hψ
lemma sum_addChar_dotProduct (z : a → R) : ∑ x, ψ (z ⬝ᵥ x) = ite (z = 0) (Fintype.card (a → R)) 0 := by convert (Fintype.prod_sum (ψ <| z · * ·)).symm; erw [← map_prod ψ.toMonoidHom]; rfl'; simp [mul_comm, sum_mulShift, hψ, Fintype.prod_ite_zero, funext_iff]
lemma sum_addChar_trace_mul (ρ : Matrix a N R) : ∑ v : Matrix N a R, ψ (ρ * v).trace = ite (ρ = 0) (Fintype.card (Matrix N a R)) 0 := by simpa [← vec_bijective.sum_comp, vec_dotProduct_vec, Fintype.card_of_bijective vec_bijective] using sum_addChar_dotProduct hψ ρᵀ.vec
lemma matrixFourier_matrixFourier y : matrixFourier ψ (matrixFourier ψ f) y = f (-y) * Fintype.card (Matrix a N R) := by simp [matrixFourier, sum_mul, mul_assoc, ← map_add_eq_mul, @trace_mul_comm a, ← trace_add, sum_comm, ← Matrix.add_mul, ← mul_sum, sum_addChar_trace_mul hψ, add_eq_zero_iff_eq_neg]
lemma exists_sum_smul_addChar_trace_eq : ∃ c : Matrix a N R → ℂ, ∑ u, c u • (ψ <| trace <| · * u) = f := ⟨_, funext (by simpa using! matrixFourier_matrixFourier hψ fun t ↦ f (-t) / Fintype.card (Matrix a N R))⟩
lemma matrix_gauss_sum (hχ : IsPrimitiveMulChar χ) S (h : ∀ (g : GL a R) d, S (g.1 * d) = χ g.1.det * S d) : (∀ y, matrixFourier ψ S y = χ⁻¹ y.det * matrixFourier ψ S 1) ∧ star (matrixFourier ψ (a := a) (χ ·.det) 1) * matrixFourier ψ S 1 = S 1 * Fintype.card (Matrix a a R) := have h y (g : GL a R) : χ g.det * matrixFourier ψ S (y * g) = matrixFourier ψ S y := .trans (by simp_all [matrixFourier, mul_sum, mul_assoc]) (g.mulLeft_bijective.sum_comp _); (⟨·, by simpa [matrixFourier, sum_mul, mul_right_comm, ← χ.star_eq_inv, ψ.map_neg_eq_conj] using (funext ‹_› ▸ matrixFourier_matrixFourier hψ S (-1) :)⟩) fun y ↦ by
 by_contra; obtain ⟨y, rfl⟩ := (isLeftRegular_of_non_zero_divisor y fun v _ ↦ Matrix.ext fun i j ↦ by_contra (hχ _ · |>.elim fun u _ ↦ by specialize h y (.mk'' (1 + v * single j () (1 : R) * single () i u) ?_) <;> simp_all [mul_add, det_one_add_mul_comm, ← y.mul_assoc, MulChar.apply_eq_zero_iff, mul_left_eq_self₀, ← isUnit_iff_isUnit_det, IsUnit.mul_right_eq_zero])).isUnit_of_finite
 simp_all [χ.inv_apply, ← h y y⁻¹]
def compUpTo {M : ℕ → _} [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] (L : ∀ j, M j →ₗ[R] M (j + 1)) : ∀ j, M 0 →ₗ[R] M j | 0 => .id | j + 1 => L j ∘ₗ compUpTo L j
omit [Fintype R] hψ
lemma exists_GL_smul_single {v : n → R} (h : ∃ j, IsUnit (v j)) i : ∃ g : GL n R, g • Pi.single i 1 = v := h.rec fun j _ ↦ by
 use .mk'' (updateCol 1 j v) (by simpa [← cramer_apply]) * .swap _ j i; simp [funext_iff, Units.smul_def]
lemma index_stabilizer_GL_vector {F} [Field F] [Finite F] {u : n → F} (h : u ≠ 0) : (stabilizer (GL n F) u).index = .card F ^ Fintype.card n - 1 := have t : {0}ᶜ ⊆ orbit _ (_ : n → F) := fun _ ↦ (exists_GL_smul_single · (ne_iff.1 h).choose) ∘ by simp [funext_iff]
 by rw [index_stabilizer, orbit_eq_iff.2 (t h), ← t.antisymm, Set.ncard_compl] <;> simp [Nat.card_pi, orbit, smul_eq_zero_iff_eq]
variable {S : ℕ → Type} {M : ℕ → Type*} [∀ j, AddCommGroup (S j)] [∀ j, Module ℂ (S j)] [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)] (b : ∀ j, S j →ₗ[ℂ] M j →ₗ[ℂ] M (j + 1)) (t : ∀ j, S j →ₗ[ℂ] S j) (f : ∀ j, S j) {g h : ∀ j, S j}
variable (S) in
def TensorChain : ℕ → ModuleCat ℂ | 0 => .of ℂ ℂ | j + 1 => .of ℂ (S j ⊗[ℂ] TensorChain j)
def TensorChain.pure j := compUpTo (M := (TensorChain S ·)) (TensorProduct.mk _ _ _ <| f ·) j (1 : ℂ)
def TensorChain.liftInPairs i : S (2 * i) ⊗[ℂ] S (2 * i + 1) →ₗ[ℂ] M (2 * i) →ₗ[ℂ] M (2 * (i + 1)) := lift ((LinearMap.llcomp ..).compl₁₂ (b _) (b _)).flip
def TensorChain.lift (x : M 0) : ∀ j, TensorChain S j →ₗ[ℂ] M j | 0 => .toSpanSingleton _ _ x | j + 1 => TensorProduct.lift ((b j).compl₂ (lift x j))
@[simp] lemma TensorChain.lift_pure x j : lift b x j (pure f j) = compUpTo (b · (f _)) j x := j.rec (one_smul ..) fun _ ↦ congrArg _
def TensorChain.map := lift (M := (TensorChain S ·)) (TensorProduct.mk .. ∘ₗ t ·) (1 : ℂ)
@[simp] lemma TensorChain.map_pure j : map t j (pure f j) = pure (t · (f _)) j := lift_pure ..
lemma TensorChain.pure_smul (c : ℕ → ℂ) m : (∀ j < m, g j = c j • f j) → pure g m = (range m).prod c • pure f m := m.rec (by aesop) fun m i h ↦ by
 erw [prod_range_succ_comm, ← smul_tmul_smul, ← h, ← i] <;> bound
@[congr] lemma TensorChain.pure_congr {m} : (∀ j < m, g j = h j) → pure g m = pure h m := by simpa using pure_smul h 1 m
lemma TensorChain.liftInPairs_pure p x : compUpTo (liftInPairs b · (f _ ⊗ₜ f _)) p x = compUpTo (b · (f _)) _ x := p.rec rfl fun _ ↦ congrArg (_ ∘ _)
lemma isUnit_of_mapMatrix {R n} [CommRing R] [Fintype n] {S} [CommRing S] (f : R →+* S) [IsLocalHom f] {M} : IsUnit (f.mapMatrix (m := n) M) → IsUnit M := by simp [↓isUnit_iff_isUnit_det, ↓← f.map_det]
