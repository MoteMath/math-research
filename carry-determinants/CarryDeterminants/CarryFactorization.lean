import CarryDeterminants.MixedRadix
import CarryDeterminants.CantorNonVanishing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 2: Exact Closed-Form Factorization of Multivariate Mixed-Radix
# Hankel and Carry Determinants (and Kummer / Binary Carry-Word Corollaries)

For any mixed-radix sequence `b : ℕ → ℕ` with `∀ r, 1 ≤ b r`, any depth `k`,
`N = place b k`, and any commutative ring `R`:

1. **Theorem 2A (`det_mixedHankelMatrix`)**: For any `y : Fin (k + 1) → R`,
   $$\det \left( \prod_{r=0}^{k-1} y_r^{d_r(i+j)} \cdot y_k^{\lfloor (i+j)/N \rfloor} \right)_{0 \le i, j < N}
     = (-1)^{\binom{N-1}{2}} \prod_{r=0}^{k-1} \left( y_k - y_r^{N / P_r} \right)^{(b_r - 1) P_r}.$$

2. **Theorem 2B (`det_carryMatrix_full`)**: For any `x : ℕ → R`,
   $$\det \left( \prod_{r=0}^{k-1} x_r^{e_r(i, j)} \right)_{0 \le i, j < N}
     = (-1)^{\binom{N-1}{2}} \prod_{r=0}^{k-1} \left( \left(\prod_{j=r}^{k-1} x_j^{Q_j}\right) - 1 \right)^{(b_r - 1) P_r}$$
   where `Q_j = N / P_{j+1}` is the suffix product `∏_{t=j+1}^{k-1} b_t`.

3. **Corollary 2.1 (`det_weightedLinearCarryMatrix`)**: For any linear carry weights `w : ℕ → R`,
   $$\det \left( \sum_{r=0}^{k-1} w_r e_r(i, j) \right)_{1 \le i, j < N}
     = (-1)^{\binom{N-1}{2}} \prod_{r=0}^{k-1} \left( \sum_{j=r}^{k-1} Q_j w_j \right)^{(b_r - 1) P_r}.$$

4. **Corollary 2.2 (`det_kummer_padicValNat_choose`)**: For every prime `p` and every `k : ℕ`,
   $$\det \left( v_p \binom{i+j}{i} \right)_{1 \le i, j < p^k}
     = (-1)^{\binom{p^k - 1}{2}} \prod_{r=0}^{k-1} \left( \frac{p^{k-r} - 1}{p - 1} \right)^{(p - 1) p^r}.$$

5. **Corollary 2.3 (`det_binary_carry_word`)**: For every `k : ℕ`,
   $$\det \Big( (i + j) \oplus i \oplus j \Big)_{1 \le i, j < 2^k}
     = (-1)^{\binom{2^k - 1}{2}} \cdot 2^{k(2^k - 1)} \cdot \prod_{r=0}^{k-1} (k - r)^{2^r}.$$

6. **Corollary 2.4 (`det_thueMorse_pow_two`)**: For every `k ≥ 2`,
   $$\det \left( (-1)^{s_2(i + j)} \right)_{0 \le i, j < 2^k} = 2^{2^k - 1}.$$
-/

namespace NovelCarry

open Matrix

lemma suffixProd_mul_place (b : ℕ → ℕ) {k j : ℕ} (hj : j < k) :
    place b (j + 1) * suffixProd b k j = place b k :=
  Nat.mul_div_cancel' (place_dvd_of_le b (by omega))

lemma suffixProd_const (B k j : ℕ) (hB : 0 < B) (hj : j < k) :
    suffixProd (fun _ => B) k j = B ^ (k - 1 - j) := by
  unfold suffixProd
  rw [place_const, place_const]
  have h1 : B ^ k = B ^ (j + 1) * B ^ (k - 1 - j) := by
    rw [← pow_add]; congr 1; omega
  rw [h1, Nat.mul_div_right _ (pow_pos hB _)]

/-! ### Step 1: Order-Reversal Permutation and Its Sign -/

/-- Reversal permutation `i ↦ N - 1 - i` on `Fin N`. -/
def revPerm (N : ℕ) : Equiv.Perm (Fin N) where
  toFun i := ⟨N - 1 - i.1, by omega⟩
  invFun i := ⟨N - 1 - i.1, by omega⟩
  left_inv i := by ext; dsimp; omega
  right_inv i := by ext; dsimp; omega

lemma choose_two_mod_two (N : ℕ) : N.choose 2 % 2 = (N / 2) % 2 := by
  induction N using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | m + 2 =>
      have hm := ih m (by omega)
      have h1 : (m + 2).choose 2 = m.choose 2 + (2 * m + 1) := by
        rw [Nat.choose_succ_succ (m + 1) 1, Nat.choose_succ_succ m 1,
          Nat.choose_one_right, Nat.choose_one_right]
        change (m + 1) + (m + m.choose 2) = m.choose 2 + (2 * m + 1)
        omega
      have hdiv : (m + 2) / 2 = m / 2 + 1 := by omega
      rw [h1, hdiv]
      omega

/-- Sign of the reversal permutation `revPerm N` is `(-1) ^ (N.choose 2)`. -/
lemma sign_revPerm (N : ℕ) : (Equiv.Perm.sign (revPerm N) : ℤ) = (-1 : ℤ) ^ (N.choose 2) := by
  have hbuild : ∀ m ≤ N / 2, ∃ σ : Equiv.Perm (Fin N),
      (∀ i : Fin N, (σ i).1 = if i.1 < m ∨ N - m ≤ i.1 then N - 1 - i.1 else i.1) ∧
      (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ m := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨1, fun i => ?_, by simp⟩
      simp
    | succ m ih =>
      intro hm
      obtain ⟨σ, hσ, hsign⟩ := ih (by omega)
      have ha_lt : m < N := by omega
      have hb_lt : N - 1 - m < N := by omega
      let a : Fin N := ⟨m, ha_lt⟩
      let b' : Fin N := ⟨N - 1 - m, hb_lt⟩
      have hab : a ≠ b' := by
        intro h
        have := congrArg Fin.val h
        dsimp [a, b'] at this
        omega
      refine ⟨Equiv.swap a b' * σ, ?_, ?_⟩
      · intro i
        simp only [Equiv.Perm.mul_apply]
        by_cases h1 : i.1 < m ∨ N - m ≤ i.1
        · have hσi : (σ i).1 = N - 1 - i.1 := by rw [hσ i]; simp only [h1, ↓reduceIte]
          have hne_a : σ i ≠ a := by intro h; have := congrArg Fin.val h; dsimp [a] at this; omega
          have hne_b : σ i ≠ b' := by intro h; have := congrArg Fin.val h; dsimp [b'] at this; omega
          rw [Equiv.swap_apply_of_ne_of_ne hne_a hne_b, hσi]
          have h1' : i.1 < m + 1 ∨ N - (m + 1) ≤ i.1 := by omega
          simp only [h1', ↓reduceIte]
        · have hσi : σ i = i := Fin.ext (by rw [hσ i]; simp only [h1, ↓reduceIte])
          rw [hσi]
          by_cases hia : i = a
          · subst hia
            rw [Equiv.swap_apply_left]
            have h1' : a.1 < m + 1 ∨ N - (m + 1) ≤ a.1 := by dsimp [a]; omega
            simp only [h1', ↓reduceIte, a, b']
          · by_cases hib : i = b'
            · subst hib
              rw [Equiv.swap_apply_right]
              have h1' : b'.1 < m + 1 ∨ N - (m + 1) ≤ b'.1 := by dsimp [b']; omega
              simp only [h1', ↓reduceIte, a, b']; omega
            · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
              have hne1 : i.1 ≠ m := fun h => hia (Fin.ext h)
              have hne2 : i.1 ≠ N - 1 - m := fun h => hib (Fin.ext h)
              have h1' : ¬ (i.1 < m + 1 ∨ N - (m + 1) ≤ i.1) := by omega
              simp only [h1', ↓reduceIte]
      · rw [map_mul, Units.val_mul, Equiv.Perm.sign_swap hab, Units.val_neg, Units.val_one,
          hsign, pow_succ']
  obtain ⟨σ, hσ, hsign⟩ := hbuild (N / 2) (le_refl _)
  have hσ_eq : σ = revPerm N := by
    ext i
    rw [hσ i]
    dsimp [revPerm]
    by_cases h : i.1 < N / 2 ∨ N - N / 2 ≤ i.1
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]; omega
  rw [← hσ_eq, hsign]
  have hmod := choose_two_mod_two N
  have hpow : ∀ a b : ℕ, a % 2 = b % 2 → (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
    intro a b hab
    rw [← Nat.div_add_mod a 2, ← Nat.div_add_mod b 2, hab, pow_add, pow_add, pow_mul, pow_mul]
    norm_num
  exact hpow (N / 2) (N.choose 2) hmod.symm

/-! ### Step 2: Complex Root-of-Unity Product & Fourier Diagonalization -/

/-- For a primitive `M`-th root of unity `η : ℂ` (`M ≥ 1`), `a ≠ 0`, and `c : ℂ`,
    `∏_{j < M} (c - a * η^j) = c^M - a^M`. -/
private lemma prod_sub_root_of_unity {M : ℕ} (hM : 0 < M) {η : ℂ} (hη : IsPrimitiveRoot η M)
    {a : ℂ} (ha : a ≠ 0) (c : ℂ) :
    ∏ j : Fin M, (c - a * η ^ j.1) = c ^ M - a ^ M := by
  let P : Polynomial ℂ := Polynomial.X ^ M - Polynomial.C (a ^ M)
  let Q : Polynomial ℂ := ∏ j : Fin M, (Polynomial.X - Polynomial.C (a * η ^ j.1))
  have hP_monic : P.Monic := Polynomial.monic_X_pow_sub_C (a ^ M) (by omega)
  have hQ_monic : Q.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)
  have hP_deg : P.natDegree = M := by
    dsimp [P]
    exact Polynomial.natDegree_X_pow_sub_C
  have hQ_deg : Q.natDegree = M := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one]
  have hinj : ∀ j₁ j₂ : Fin M, a * η ^ j₁.1 = a * η ^ j₂.1 → j₁ = j₂ := by
    intro j₁ j₂ h
    have hpow : η ^ j₁.1 = η ^ j₂.1 := mul_left_cancel₀ ha h
    exact Fin.ext (hη.injOn_pow (Finset.mem_coe.mpr (Finset.mem_range.mpr j₁.2))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr j₂.2)) hpow)
  have hdvd : Q ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro j₁ _ j₂ _ hne
      have hne_val : a * η ^ j₁.1 ≠ a * η ^ j₂.1 := fun h => hne (hinj j₁ j₂ h)
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne_val))
    · intro j _
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, mul_pow,
        ← pow_mul, mul_comm j.1 M, pow_mul, hη.pow_eq_one, one_pow, mul_one, sub_self]
  have hPQ : P = Q :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hQ_monic hP_monic hdvd (by omega)
  have hev := congrArg (Polynomial.eval c) hPQ.symm
  simp only [Q, P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow] at hev
  exact hev

/-- Reindexing product over `Fin N` for any divisor `D ∣ N` (`M = N / D`):
    `∏_{m < N} ((lam * ζ^m)^D - c) = (-1)^(N - D) * (lam^N - c^M)^D`. -/
private lemma prod_pow_root_sub {N D : ℕ} (hN : 0 < N) (hD : 0 < D) (hDN : D ∣ N)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {lam : ℂ} (hlam : lam ≠ 0) (c : ℂ) :
    ∏ m : Fin N, ((lam * ζ ^ m.1) ^ D - c) =
      (-1 : ℂ) ^ (N - D) * (lam ^ N - c ^ (N / D)) ^ D := by
  set M := N / D
  have hDM : D * M = N := Nat.mul_div_cancel' hDN
  have hM : 0 < M := by nlinarith
  have hη : IsPrimitiveRoot (ζ ^ D) M := by
    have h1 := hζ.pow_of_dvd (by omega : D ≠ 0) hDN
    simpa [M] using h1
  let e : Fin D × Fin M ≃ Fin N :=
    { toFun := fun p => ⟨p.1.1 * M + p.2.1, by nlinarith [p.1.2, p.2.2]⟩
      invFun := fun m => (⟨m.1 / M, by
        have hlt : m.1 < D * M := hDM.symm ▸ m.2
        exact Nat.div_lt_of_lt_mul (by linarith)⟩,
        ⟨m.1 % M, Nat.mod_lt _ hM⟩)
      left_inv := by
        rintro ⟨⟨q, hq⟩, ⟨j, hj⟩⟩
        ext
        · dsimp
          rw [mul_comm q M, Nat.mul_add_div hM, Nat.div_eq_of_lt hj, add_zero]
        · dsimp
          rw [mul_comm q M, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      right_inv := by
        intro m
        ext; dsimp
        have := Nat.div_add_mod m.1 M
        linarith }
  rw [← Equiv.prod_comp e, Fintype.prod_prod_type]
  have hinner : ∀ q : Fin D,
      ∏ j : Fin M, ((lam * ζ ^ (e (q, j)).1) ^ D - c) =
        (-1 : ℂ) ^ (M - 1) * (lam ^ N - c ^ M) := by
    intro q
    have hterm : ∀ j : Fin M,
        (lam * ζ ^ (e (q, j)).1) ^ D - c = -(c - lam ^ D * (ζ ^ D) ^ j.1) := by
      intro j
      dsimp [e]
      have hexp : (q.1 * M + j.1) * D = N * q.1 + D * j.1 := by
        calc (q.1 * M + j.1) * D = (D * M) * q.1 + D * j.1 := by ring
          _ = N * q.1 + D * j.1 := by rw [hDM]
      rw [mul_pow, ← pow_mul, hexp,
        pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul, pow_mul]
      ring
    simp_rw [hterm, Finset.prod_neg, Finset.card_fin]
    rw [prod_sub_root_of_unity hM hη (pow_ne_zero D hlam) c]
    have hpowN : (lam ^ D) ^ M = lam ^ N := by rw [← pow_mul, hDM]
    rw [hpowN]
    have hM1 : (-1 : ℂ) ^ M = -((-1 : ℂ) ^ (M - 1)) := by
      have h : M = (M - 1) + 1 := (Nat.sub_add_cancel hM).symm
      conv_lhs => rw [h, pow_succ]
      ring
    rw [hM1]; ring
  simp_rw [hinner, Finset.prod_const, Finset.card_fin, mul_pow, ← pow_mul]
  congr 2
  rw [Nat.sub_mul, one_mul, mul_comm M D, hDM]

/-- Reversed generating polynomial factorization over any commutative ring `R`. -/
lemma sum_hankel_rev_eq_prod {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (y : Fin k → R) (z : R) :
    ∑ t : Fin (place b k), (∏ r : Fin k, (y r) ^ mdigit b t.1 r.1) * z ^ (place b k - 1 - t.1) =
      ∏ r : Fin k, ∑ d ∈ Finset.range (b r.1), (y r) ^ d * (z ^ place b r.1) ^ (b r.1 - 1 - d) := by
  have hb0 : ∀ r, 0 < b r := hb
  induction k with
  | zero =>
    change ∑ t : Fin 1, (∏ r : Fin 0, (y r) ^ mdigit b t.1 r.1) * z ^ (1 - 1 - t.1) =
      ∏ r : Fin 0, ∑ d ∈ Finset.range (b r.1), (y r) ^ d * (z ^ place b r.1) ^ (b r.1 - 1 - d)
    simp
  | succ k ih =>
    have hP : 0 < place b k := place_pos b hb0 k
    have hB : 0 < b k := hb0 k
    let e : Fin (b k) × Fin (place b k) ≃ Fin (place b (k + 1)) :=
      { toFun := fun p => ⟨p.1.1 * place b k + p.2.1, by
          rw [place_succ]; nlinarith [p.1.2, p.2.2]⟩
        invFun := fun t => (⟨t.1 / place b k, by
          have hlt : t.1 < place b k * b k := t.2
          exact Nat.div_lt_of_lt_mul hlt⟩,
          ⟨t.1 % place b k, Nat.mod_lt _ hP⟩)
        left_inv := by
          rintro ⟨⟨q, hq⟩, ⟨u, hu⟩⟩
          ext
          · dsimp; rw [mul_comm q (place b k), Nat.mul_add_div hP, Nat.div_eq_of_lt hu, add_zero]
          · dsimp; rw [mul_comm q (place b k), Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
        right_inv := by
          intro t; ext; dsimp
          have := Nat.div_add_mod t.1 (place b k)
          linarith }
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    have hterm : ∀ (q : Fin (b k)) (u : Fin (place b k)),
        (∏ r : Fin (k + 1), (y r) ^ mdigit b (q.1 * place b k + u.1) r.1) *
            z ^ (place b (k + 1) - 1 - (q.1 * place b k + u.1)) =
          ((y (Fin.last k)) ^ q.1 * (z ^ place b k) ^ (b k - 1 - q.1)) *
          ((∏ r : Fin k, (y r.castSucc) ^ mdigit b u.1 r.1) * z ^ (place b k - 1 - u.1)) := by
      intro q u
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_last, Fin.val_castSucc]
      have hd_last : mdigit b (q.1 * place b k + u.1) k = q.1 := by
        unfold mdigit
        rw [mul_comm q.1 (place b k), Nat.mul_add_div hP, Nat.div_eq_of_lt u.2, add_zero,
          Nat.mod_eq_of_lt q.2]
      have hd_lt : ∀ r : Fin k, mdigit b (q.1 * place b k + u.1) r.1 = mdigit b u.1 r.1 := by
        intro r
        have hdvd : place b (r.1 + 1) ∣ place b k := place_dvd_of_le b (by omega)
        obtain ⟨Q, hQ⟩ := hdvd
        set uval := u.1
        have hsum : q.1 * place b k + uval = uval + place b r.1 * (b r.1 * (q.1 * Q)) := by
          calc q.1 * place b k + uval = q.1 * (place b (r.1 + 1) * Q) + uval := by rw [hQ]
            _ = q.1 * (place b r.1 * b r.1 * Q) + uval := by rw [place_succ]
            _ = uval + place b r.1 * (b r.1 * (q.1 * Q)) := by ring
        unfold mdigit
        change (q.1 * place b k + uval) / place b r.1 % b r.1 = uval / place b r.1 % b r.1
        rw [hsum, Nat.add_mul_div_left _ _ (place_pos b hb0 r.1), Nat.add_mul_mod_self_left]
      have hexp : place b (k + 1) - 1 - (q.1 * place b k + u.1) =
          place b k * (b k - 1 - q.1) + (place b k - 1 - u.1) := by
        have hPB : place b (k + 1) = place b k * b k := rfl
        have hqle : q.1 + 1 ≤ b k := q.2
        have hule : u.1 + 1 ≤ place b k := u.2
        have h1 : place b k * (b k - 1 - q.1) + place b k * q.1 + place b k = place b k * b k := by
          have : (b k - 1 - q.1) + q.1 + 1 = b k := by omega
          calc place b k * (b k - 1 - q.1) + place b k * q.1 + place b k
              = place b k * ((b k - 1 - q.1) + q.1 + 1) := by ring
            _ = place b k * b k := by rw [this]
        have h2 : place b k * q.1 = q.1 * place b k := mul_comm _ _
        omega
      rw [hd_last, hexp, pow_add, pow_mul]
      have hprod_eq : ∏ r : Fin k, (y r.castSucc) ^ mdigit b (q.1 * place b k + u.1) r.1 =
          ∏ r : Fin k, (y r.castSucc) ^ mdigit b u.1 r.1 :=
        Finset.prod_congr rfl (fun r _ => by rw [hd_lt r])
      rw [hprod_eq]
      ring
    dsimp only [e, Equiv.coe_fn_mk]
    simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [ih (fun r => y r.castSucc), Fin.prod_univ_castSucc, mul_comm,
      Fin.sum_univ_eq_sum_range (fun d => (y (Fin.last k)) ^ d * (z ^ place b k) ^ (b k - 1 - d)) (b k)]
    simp only [Fin.val_castSucc, Fin.val_last]

/-- Helper telescoping sum `∑_{r < k} (place b (r + 1) - place b r) = place b k - 1`. -/
private lemma sum_place_sub (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    ∑ r ∈ Finset.range k, (place b (r + 1) - place b r) = place b k - 1 := by
  induction k with
  | zero => simp [place]
  | succ m ihm =>
    rw [Finset.sum_range_succ, ihm]
    have h1 : 1 ≤ place b m := place_pos b hb m
    have h2 : place b m ≤ place b (m + 1) := place_mono b hb (Nat.le_succ _)
    omega

/-- Core Complex Fourier Diagonalization for `mixedHankelMatrix` at `y_k = lam^N` (`lam ≠ 0`,
    `lam^N ≠ y_r^(N / P_r)` for all `r < k`). -/
private lemma det_mixedHankelMatrix_complex_generic (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ)
    (y : Fin k → ℂ) {lam : ℂ} (hlam : lam ≠ 0)
    (hgen : ∀ r : Fin k, lam ^ place b k ≠ (y r) ^ (place b k / place b r.1)) :
    (mixedHankelMatrix b k (Fin.snoc y (lam ^ place b k))).det =
      (-1 : ℂ) ^ ((place b k - 1).choose 2) *
        ∏ r : Fin k, (lam ^ place b k - (y r) ^ (place b k / place b r.1)) ^
          ((b r.1 - 1) * place b r.1) := by
  have hb0 : ∀ r, 0 < b r := hb
  set N := place b k
  have hN : 0 < N := place_pos b hb0 k
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N (by omega)
  let ω : Fin N → ℂ := fun m => lam * ζ ^ m.1
  have hω_pow : ∀ m : Fin N, (ω m) ^ N = lam ^ N := fun m => by
    dsimp only [ω]
    rw [mul_pow, ← pow_mul, mul_comm m.1 N, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have hω_inj : Function.Injective ω := by
    intro m₁ m₂ h
    have hpow : ζ ^ m₁.1 = ζ ^ m₂.1 := mul_left_cancel₀ hlam h
    exact Fin.ext (hζ.injOn_pow (Finset.mem_coe.mpr (Finset.mem_range.mpr m₁.2))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr m₂.2)) hpow)
  let g : ℕ → ℂ := fun n => ∏ r : Fin k, (y r) ^ mdigit b n r.1
  let H : Matrix (Fin N) (Fin N) ℂ := mixedHankelMatrix b k (Fin.snoc y (lam ^ N))
  let V : Matrix (Fin N) (Fin N) ℂ := (Matrix.vandermonde ω)ᵀ
  let F : Matrix (Fin N) (Fin N) ℂ := V.submatrix (revPerm N) id
  let ev : Fin N → ℂ := fun m => ∑ t : Fin N, g t.1 * (ω m) ^ (N - 1 - t.1)
  have hHF : H * F = V * Matrix.diagonal ev := by
    ext i m
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [H, F, V, ev, Matrix.submatrix_apply, Matrix.transpose_apply,
      Matrix.vandermonde_apply, id_eq, revPerm, Equiv.coe_fn_mk,
      mixedHankelMatrix, Matrix.of_apply, hankelDigitVal, Fin.snoc_castSucc, Fin.snoc_last]
    change ∑ j : Fin N, (g (i.1 + j.1) * (lam ^ N) ^ ((i.1 + j.1) / N)) * (ω m) ^ (N - 1 - j.1) =
      (ω m) ^ i.1 * ∑ t : Fin N, g t.1 * (ω m) ^ (N - 1 - t.1)
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin N))
      (fun j => i.1 + j.1 < N)]
    have hpart1 : ∑ j ∈ Finset.univ.filter (fun j : Fin N => i.1 + j.1 < N),
        (g (i.1 + j.1) * (lam ^ N) ^ ((i.1 + j.1) / N)) * (ω m) ^ (N - 1 - j.1) =
        ∑ t ∈ Finset.univ.filter (fun t : Fin N => i.1 ≤ t.1),
          (ω m) ^ i.1 * (g t.1 * (ω m) ^ (N - 1 - t.1)) := by
      refine Finset.sum_bij (fun j hj => ⟨i.1 + j.1, (Finset.mem_filter.mp hj).2⟩) ?_ ?_ ?_ ?_
      · intro j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
      · intro j₁ _ j₂ _ h; ext; have := congrArg Fin.val h; dsimp at this; omega
      · intro t ht
        have hit : i.1 ≤ t.1 := (Finset.mem_filter.mp ht).2
        have htlt : t.1 < N := t.2
        refine ⟨⟨t.1 - i.1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, ?_⟩
        ext; dsimp; omega
      · intro j hj
        have hlt : i.1 + j.1 < N := (Finset.mem_filter.mp hj).2
        rw [Nat.div_eq_of_lt hlt, pow_zero, mul_one]
        have hexp : N - 1 - j.1 = i.1 + (N - 1 - (i.1 + j.1)) := by omega
        dsimp
        rw [hexp, pow_add]; ring
    have hpart2 : ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ i.1 + j.1 < N),
        (g (i.1 + j.1) * (lam ^ N) ^ ((i.1 + j.1) / N)) * (ω m) ^ (N - 1 - j.1) =
        ∑ t ∈ Finset.univ.filter (fun t : Fin N => ¬ i.1 ≤ t.1),
          (ω m) ^ i.1 * (g t.1 * (ω m) ^ (N - 1 - t.1)) := by
      refine Finset.sum_bij (fun j hj => ⟨i.1 + j.1 - N, by
          have := (Finset.mem_filter.mp hj).2; have := i.2; have := j.2; omega⟩) ?_ ?_ ?_ ?_
      · intro j hj
        have hge : ¬ i.1 + j.1 < N := (Finset.mem_filter.mp hj).2
        have hjlt : j.1 < N := j.2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
      · intro j₁ hj₁ j₂ hj₂ h
        have h1 : ¬ i.1 + j₁.1 < N := (Finset.mem_filter.mp hj₁).2
        have h2 : ¬ i.1 + j₂.1 < N := (Finset.mem_filter.mp hj₂).2
        ext; have := congrArg Fin.val h; dsimp at this; omega
      · intro t ht
        have hti : ¬ i.1 ≤ t.1 := (Finset.mem_filter.mp ht).2
        have hilt : i.1 < N := i.2
        refine ⟨⟨N + t.1 - i.1, by omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, ?_⟩
        ext; dsimp; omega
      · intro j hj
        have hge : N ≤ i.1 + j.1 := by have := (Finset.mem_filter.mp hj).2; omega
        have hdiv : (i.1 + j.1) / N = 1 := by
          have hilt : i.1 < N := i.2
          have hjlt : j.1 < N := j.2
          have hlt2 : i.1 + j.1 < N * 2 := by omega
          have h1 : 1 ≤ (i.1 + j.1) / N := Nat.div_pos hge hN
          have h2 : (i.1 + j.1) / N < 2 := Nat.div_lt_of_lt_mul hlt2
          omega
        have hg_eq : g (i.1 + j.1) = g (i.1 + j.1 - N) := by
          dsimp [g]
          apply Finset.prod_congr rfl
          intro r _
          congr 1
          have hdvd : place b (r.1 + 1) ∣ N := place_dvd_of_le b (by omega)
          obtain ⟨Q, hQ⟩ := hdvd
          have hsub : i.1 + j.1 = (i.1 + j.1 - N) + place b r.1 * (b r.1 * Q) := by
            have hN_eq : place b r.1 * (b r.1 * Q) = N := by
              calc place b r.1 * (b r.1 * Q) = (place b r.1 * b r.1) * Q := by ring
                _ = place b (r.1 + 1) * Q := rfl
                _ = N := hQ.symm
            omega
          unfold mdigit
          conv_lhs => rw [hsub, Nat.add_mul_div_left _ _ (place_pos b hb0 r.1),
            Nat.add_mul_mod_self_left]
        rw [hdiv, pow_one, hg_eq, ← hω_pow m]
        have hexp : N + (N - 1 - j.1) = i.1 + (N - 1 - (i.1 + j.1 - N)) := by omega
        dsimp
        calc g (i.1 + j.1 - N) * (ω m) ^ N * (ω m) ^ (N - 1 - j.1)
            = g (i.1 + j.1 - N) * ((ω m) ^ N * (ω m) ^ (N - 1 - j.1)) := by ring
          _ = g (i.1 + j.1 - N) * (ω m) ^ (N + (N - 1 - j.1)) := by rw [pow_add]
          _ = g (i.1 + j.1 - N) * (ω m) ^ (i.1 + (N - 1 - (i.1 + j.1 - N))) := by rw [hexp]
          _ = (ω m) ^ i.1 * (g (i.1 + j.1 - N) * (ω m) ^ (N - 1 - (i.1 + j.1 - N))) := by
                rw [pow_add]; ring
    rw [hpart1, hpart2, Finset.sum_filter_add_sum_filter_not, Finset.mul_sum]
  have hdet_eq := congrArg Matrix.det hHF
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet_eq
  have hF_det : F.det = (-1 : ℂ) ^ (N.choose 2) * V.det := by
    dsimp [F]
    rw [Matrix.det_permute (revPerm N) V]
    have hsign : (((Equiv.Perm.sign (revPerm N) : ℤ) : ℂ)) = (-1 : ℂ) ^ (N.choose 2) := by
      exact_mod_cast sign_revPerm N
    exact congrArg (· * V.det) hsign
  have hV_ne : V.det ≠ 0 := by
    dsimp [V]
    rw [Matrix.det_transpose, Matrix.det_vandermonde]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hne : j ≠ i := ne_of_gt (Finset.mem_Ioi.mp hj)
    exact sub_ne_zero.mpr (fun h => hne (hω_inj h))
  rw [hF_det] at hdet_eq
  have hH_det : H.det = (-1 : ℂ) ^ (N.choose 2) * ∏ m : Fin N, ev m := by
    have h1 : (H.det * (-1 : ℂ) ^ (N.choose 2)) * V.det = (∏ m : Fin N, ev m) * V.det := by
      calc (H.det * (-1 : ℂ) ^ (N.choose 2)) * V.det
          = H.det * ((-1 : ℂ) ^ (N.choose 2) * V.det) := by ring
        _ = V.det * ∏ m : Fin N, ev m := hdet_eq
        _ = (∏ m : Fin N, ev m) * V.det := mul_comm _ _
    have h2 : H.det * (-1 : ℂ) ^ (N.choose 2) = ∏ m : Fin N, ev m := mul_right_cancel₀ hV_ne h1
    have hsq : (-1 : ℂ) ^ (N.choose 2) * (-1 : ℂ) ^ (N.choose 2) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc H.det = H.det * ((-1 : ℂ) ^ (N.choose 2) * (-1 : ℂ) ^ (N.choose 2)) := by rw [hsq, mul_one]
      _ = (-1 : ℂ) ^ (N.choose 2) * (H.det * (-1 : ℂ) ^ (N.choose 2)) := by ring
      _ = (-1 : ℂ) ^ (N.choose 2) * ∏ m : Fin N, ev m := by rw [h2]
  rw [hH_det]
  have hev_prod : ∏ m : Fin N, ev m =
      ∏ r : Fin k, ∏ m : Fin N,
        ∑ d ∈ Finset.range (b r.1), (y r) ^ d * ((ω m) ^ place b r.1) ^ (b r.1 - 1 - d) := by
    have hev_eq : ∀ m : Fin N, ev m =
        ∏ r : Fin k, ∑ d ∈ Finset.range (b r.1),
          (y r) ^ d * ((ω m) ^ place b r.1) ^ (b r.1 - 1 - d) :=
      fun m => sum_hankel_rev_eq_prod b hb k y (ω m)
    simp_rw [hev_eq]
    exact Finset.prod_comm
  rw [hev_prod]
  have hfactor : ∀ r : Fin k,
      ∏ m : Fin N, ∑ d ∈ Finset.range (b r.1),
          (y r) ^ d * ((ω m) ^ place b r.1) ^ (b r.1 - 1 - d) =
        (-1 : ℂ) ^ (place b (r.1 + 1) - place b r.1) *
          (lam ^ N - (y r) ^ (N / place b r.1)) ^ ((b r.1 - 1) * place b r.1) := by
    intro r
    have hgeom : ∀ z : ℂ,
        (z ^ place b r.1 - y r) *
          (∑ d ∈ Finset.range (b r.1), (y r) ^ d * (z ^ place b r.1) ^ (b r.1 - 1 - d)) =
        z ^ place b (r.1 + 1) - (y r) ^ (b r.1) := by
      intro z
      have h1 := geom_sum₂_mul (z ^ place b r.1) (y r) (b r.1)
      have hrev_sum : ∑ d ∈ Finset.range (b r.1), (y r) ^ d * (z ^ place b r.1) ^ (b r.1 - 1 - d) =
          ∑ i ∈ Finset.range (b r.1), (z ^ place b r.1) ^ i * (y r) ^ (b r.1 - 1 - i) := by
        rw [← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl
        intro d hd
        have hlt : d < b r.1 := Finset.mem_range.mp hd
        have hsub : b r.1 - 1 - (b r.1 - 1 - d) = d := by omega
        rw [hsub, mul_comm]
      rw [hrev_sum, mul_comm, h1, ← pow_mul, place_succ]
    have hprod_mul :
        (∏ m : Fin N, ((ω m) ^ place b r.1 - y r)) *
        (∏ m : Fin N, ∑ d ∈ Finset.range (b r.1),
          (y r) ^ d * ((ω m) ^ place b r.1) ^ (b r.1 - 1 - d)) =
        ∏ m : Fin N, ((ω m) ^ place b (r.1 + 1) - (y r) ^ b r.1) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun m _ => hgeom (ω m))
    have hL := prod_pow_root_sub hN (place_pos b hb0 r.1) (place_dvd_of_le b (le_of_lt r.2))
      hζ hlam (y r)
    have hR := prod_pow_root_sub hN (place_pos b hb0 (r.1 + 1)) (place_dvd_of_le b r.2)
      hζ hlam ((y r) ^ b r.1)
    rw [hL, hR] at hprod_mul
    have hexp_eq : ((y r) ^ b r.1) ^ (N / place b (r.1 + 1)) = (y r) ^ (N / place b r.1) := by
      rw [← pow_mul]
      congr 1
      have h1 : place b (r.1 + 1) * (N / place b (r.1 + 1)) = N :=
        Nat.mul_div_cancel' (place_dvd_of_le b r.2)
      have h2 : place b r.1 * (N / place b r.1) = N :=
        Nat.mul_div_cancel' (place_dvd_of_le b (le_of_lt r.2))
      have hPr : 0 < place b r.1 := place_pos b hb0 r.1
      have hmul : place b r.1 * (b r.1 * (N / place b (r.1 + 1))) =
          place b r.1 * (N / place b r.1) := by
        rw [← mul_assoc, ← place_succ, h1, h2]
      exact Nat.eq_of_mul_eq_mul_left hPr hmul
    rw [hexp_eq] at hprod_mul
    have hdiff_ne : lam ^ N - (y r) ^ (N / place b r.1) ≠ 0 := sub_ne_zero.mpr (hgen r)
    have hcancel_ne :
        (-1 : ℂ) ^ (N - place b r.1) * (lam ^ N - (y r) ^ (N / place b r.1)) ^ place b r.1 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hdiff_ne)
    apply mul_left_cancel₀ hcancel_ne
    rw [hprod_mul]
    have hPr_le_Pr1 : place b r.1 ≤ place b (r.1 + 1) := place_mono b hb (Nat.le_succ _)
    have hPr1_le_N : place b (r.1 + 1) ≤ N := place_mono b hb r.2
    have hPdiff : place b (r.1 + 1) - place b r.1 = (b r.1 - 1) * place b r.1 := by
      rw [place_succ, mul_comm (place b r.1) (b r.1), Nat.sub_mul, one_mul]
    have hPadd : place b r.1 + (b r.1 - 1) * place b r.1 = place b (r.1 + 1) := by omega
    have hsign_eq : (-1 : ℂ) ^ (N - place b (r.1 + 1)) =
        (-1 : ℂ) ^ (N - place b r.1) * (-1 : ℂ) ^ (place b (r.1 + 1) - place b r.1) := by
      rw [← pow_add]
      have hmod : (N - place b (r.1 + 1)) % 2 =
          ((N - place b r.1) + (place b (r.1 + 1) - place b r.1)) % 2 := by omega
      rw [← Nat.div_add_mod (N - place b (r.1 + 1)) 2,
        ← Nat.div_add_mod ((N - place b r.1) + (place b (r.1 + 1) - place b r.1)) 2,
        hmod, pow_add, pow_add, pow_mul, pow_mul]
      norm_num
    calc (-1 : ℂ) ^ (N - place b (r.1 + 1)) *
            (lam ^ N - (y r) ^ (N / place b r.1)) ^ place b (r.1 + 1)
        = ((-1 : ℂ) ^ (N - place b r.1) * (-1 : ℂ) ^ (place b (r.1 + 1) - place b r.1)) *
            ((lam ^ N - (y r) ^ (N / place b r.1)) ^ place b r.1 *
              (lam ^ N - (y r) ^ (N / place b r.1)) ^ ((b r.1 - 1) * place b r.1)) := by
            rw [← hsign_eq, ← pow_add, hPadd]
      _ = ((-1 : ℂ) ^ (N - place b r.1) * (lam ^ N - (y r) ^ (N / place b r.1)) ^ place b r.1) *
            ((-1 : ℂ) ^ (place b (r.1 + 1) - place b r.1) *
              (lam ^ N - (y r) ^ (N / place b r.1)) ^ ((b r.1 - 1) * place b r.1)) := by ring
  simp_rw [hfactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have htelesc : ∑ r : Fin k, (place b (r.1 + 1) - place b r.1) = N - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun r => place b (r + 1) - place b r) k]
    exact sum_place_sub b hb k
  rw [htelesc, ← mul_assoc, ← pow_add]
  congr 1
  have hmod : (N.choose 2 + (N - 1)) % 2 = ((N - 1).choose 2) % 2 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    have hrec : (m + 1).choose 2 = m.choose 2 + m := by
      rw [Nat.choose_succ_succ m 1, Nat.choose_one_right]
      change m + m.choose 2 = m.choose 2 + m
      omega
    rw [hm, Nat.succ_eq_add_one, Nat.add_sub_cancel, hrec]
    omega
  rw [← Nat.div_add_mod (N.choose 2 + (N - 1)) 2, ← Nat.div_add_mod ((N - 1).choose 2) 2,
    hmod, pow_add, pow_add, pow_mul, pow_mul]
  norm_num

/-! ### Step 3: Multivariate Polynomial Identity Principle (from `ℕ` / `ℂ` to EVERY `CommRing R`) -/

/-- If `p : MvPolynomial (Fin m) ℤ` evaluates to `0` at every `v : Fin m → ℕ`, then `p = 0`. -/
lemma mvPolynomial_eq_zero_of_eval_nat :
    ∀ {m : ℕ} (p : MvPolynomial (Fin m) ℤ),
      (∀ v : Fin m → ℕ, MvPolynomial.eval (fun i => (v i : ℤ)) p = 0) → p = 0 := by
  intro m
  induction m with
  | zero =>
    intro p hp
    have h0 := hp Fin.elim0
    ext f
    have hf0 : f = 0 := by ext i; exact i.elim0
    subst hf0
    have hev0 : MvPolynomial.eval (fun i : Fin 0 => ((Fin.elim0 i : ℕ) : ℤ)) p = p.coeff 0 := by
      rw [MvPolynomial.eval_eq']
      rw [Finset.sum_eq_single (0 : Fin 0 →₀ ℕ)]
      · simp
      · intro b _ hb; exact (hb (by ext i; exact i.elim0)).elim
      · intro hnot
        rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]
    change p.coeff 0 = (0 : ℤ)
    rw [← hev0, h0]
  | succ m ih =>
    intro p hp
    let q := MvPolynomial.finSuccEquiv ℤ m p
    suffices hq : q = 0 by
      exact (MvPolynomial.finSuccEquiv ℤ m).injective (by simp [q, hq])
    apply Polynomial.ext
    intro d
    rw [Polynomial.coeff_zero]
    apply ih
    intro v
    let evTail : MvPolynomial (Fin m) ℤ →+* ℤ := MvPolynomial.eval (fun i => (v i : ℤ))
    let qv : Polynomial ℤ := q.map evTail
    have hqv_zero : qv = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      have hsub : Set.range (fun a : ℕ => (a : ℤ)) ⊆ {x : ℤ | qv.IsRoot x} := by
        rintro _ ⟨a, rfl⟩
        change qv.eval (a : ℤ) = 0
        have hev : qv.eval (a : ℤ) =
            MvPolynomial.eval (Fin.cons (a : ℤ) (fun i => (v i : ℤ))) p := by
          have hhom : ((Polynomial.evalRingHom (a : ℤ)).comp
              ((Polynomial.mapRingHom evTail).comp (MvPolynomial.finSuccEquiv ℤ m).toRingHom)) =
              MvPolynomial.eval (Fin.cons (a : ℤ) (fun i => (v i : ℤ))) := by
            apply MvPolynomial.ringHom_ext
            · intro c; simp [evTail]
            · intro i
              refine Fin.cases ?_ ?_ i
              · simp [evTail, MvPolynomial.finSuccEquiv_X_zero]
              · intro j; simp [evTail, MvPolynomial.finSuccEquiv_X_succ]
          exact RingHom.congr_fun hhom p
        rw [hev]
        have hcons : Fin.cons (a : ℤ) (fun i => (v i : ℤ)) =
            fun i => (((Fin.cons a v : Fin (m + 1) → ℕ) i : ℕ) : ℤ) := by
          ext i; refine Fin.cases ?_ ?_ i <;> simp
        rw [hcons]
        exact hp (Fin.cons a v)
      exact (Set.infinite_range_of_injective Nat.cast_injective).mono hsub
    have hcoeff : evTail (q.coeff d) = qv.coeff d := (Polynomial.coeff_map evTail d).symm
    rw [hcoeff, hqv_zero, Polynomial.coeff_zero]

/-- **Theorem 2A (Multivariate Mixed-Radix Multiplicative Hankel Determinant over ANY `CommRing R`)**:
    For any radices `b : ℕ → ℕ` with `∀ r, 1 ≤ b r`, any depth `k`, `N = place b k`,
    any commutative ring `R`, and any `y : Fin (k + 1) → R`:
    $$\det \left( \prod_{r=0}^{k-1} y_r^{d_r(i+j)} \cdot y_k^{\lfloor (i+j)/N \rfloor} \right)_{0 \le i, j < N}
      = (-1)^{\binom{N-1}{2}} \prod_{r=0}^{k-1} \left( y_k - y_r^{N / P_r} \right)^{(b_r - 1) P_r}.$$ -/
theorem det_mixedHankelMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (y : Fin (k + 1) → R) :
    (mixedHankelMatrix b k y).det =
      (-1 : R) ^ ((place b k - 1).choose 2) *
        ∏ r : Fin k, (y (Fin.last k) - (y r.castSucc) ^ (place b k / place b r.1)) ^
          ((b r.1 - 1) * place b r.1) := by
  set N := place b k
  have hN : 0 < N := place_pos b hb k
  let Xv : Fin (k + 1) → MvPolynomial (Fin (k + 1)) ℤ := MvPolynomial.X
  let LHS : MvPolynomial (Fin (k + 1)) ℤ := (mixedHankelMatrix b k Xv).det
  let RHS : MvPolynomial (Fin (k + 1)) ℤ :=
    (-1 : MvPolynomial (Fin (k + 1)) ℤ) ^ ((N - 1).choose 2) *
      ∏ r : Fin k, (Xv (Fin.last k) - (Xv r.castSucc) ^ (N / place b r.1)) ^
        ((b r.1 - 1) * place b r.1)
  have huniv : LHS = RHS := by
    rw [← sub_eq_zero]
    apply mvPolynomial_eq_zero_of_eval_nat
    intro v
    let v₀ : Fin k → ℕ := fun r => v r.castSucc
    let evPoly : MvPolynomial (Fin (k + 1)) ℤ →+* Polynomial ℤ :=
      (MvPolynomial.aeval
        (Fin.snoc (fun r : Fin k => Polynomial.C (v₀ r : ℤ)) Polynomial.X)).toRingHom
    let P_poly : Polynomial ℤ := evPoly (LHS - RHS)
    have hP_eval : ∀ z : ℤ, P_poly.eval z =
        MvPolynomial.eval (Fin.snoc (fun r : Fin k => (v₀ r : ℤ)) z) (LHS - RHS) := by
      intro z
      dsimp [P_poly]
      have hcomp : (Polynomial.evalRingHom z).comp evPoly =
          MvPolynomial.eval (Fin.snoc (fun r : Fin k => (v₀ r : ℤ)) z) := by
        apply MvPolynomial.ringHom_ext
        · intro c; simp [evPoly]
        · intro i
          refine Fin.lastCases ?_ ?_ i <;> simp [evPoly]
      exact RingHom.congr_fun hcomp (LHS - RHS)
    have hP_zero : P_poly = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      let M₀ : ℕ := 1 + ∑ r : Fin k, (v₀ r) ^ (N / place b r.1)
      have hsub : Set.range (fun t : ℕ => (((M₀ + t) ^ N : ℕ) : ℤ)) ⊆ {z : ℤ | P_poly.IsRoot z} := by
        rintro _ ⟨t, rfl⟩
        change P_poly.eval (((M₀ + t) ^ N : ℕ) : ℤ) = 0
        rw [hP_eval]
        apply Int.cast_injective (α := ℂ)
        rw [Int.cast_zero]
        set lam : ℂ := ((M₀ + t : ℕ) : ℂ)
        have hlam_ne : lam ≠ 0 := by
          have hpos : 0 < M₀ + t := by dsimp [M₀]; omega
          exact Nat.cast_ne_zero.mpr (by omega)
        have hgen : ∀ r : Fin k, lam ^ N ≠ ((v₀ r : ℂ)) ^ (N / place b r.1) := by
          intro r
          have hlt : (v₀ r) ^ (N / place b r.1) < (M₀ + t) ^ N := by
            have hle1 : (v₀ r) ^ (N / place b r.1) ≤
                ∑ r' : Fin k, (v₀ r') ^ (N / place b r'.1) :=
              Finset.single_le_sum (f := fun r' : Fin k => (v₀ r') ^ (N / place b r'.1))
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
            have hlt2 : (v₀ r) ^ (N / place b r.1) < M₀ + t := by dsimp [M₀]; omega
            have hle3 : M₀ + t ≤ (M₀ + t) ^ N := Nat.le_self_pow (by omega) _
            omega
          intro heq
          have heq_nat : (M₀ + t) ^ N = (v₀ r) ^ (N / place b r.1) := by
            apply Nat.cast_injective (R := ℂ)
            simpa [lam] using heq
          omega
        have hC := det_mixedHankelMatrix_complex_generic b hb k (fun r => (v₀ r : ℂ)) hlam_ne hgen
        let φ : MvPolynomial (Fin (k + 1)) ℤ →+* ℂ :=
          (Int.castRingHom ℂ).comp (MvPolynomial.eval (Fin.snoc (fun r : Fin k => (v₀ r : ℤ))
            (((M₀ + t) ^ N : ℕ) : ℤ)))
        let yC : Fin (k + 1) → ℂ := Fin.snoc (fun r : Fin k => (v₀ r : ℂ)) (lam ^ N)
        have hφ_X : ∀ i : Fin (k + 1), φ (Xv i) = yC i := by
          intro i
          refine Fin.lastCases ?_ ?_ i
          · simp [φ, Xv, yC, lam]
          · intro r; simp [φ, Xv, yC]
        change φ (LHS - RHS) = 0
        rw [map_sub, sub_eq_zero]
        have hφL : φ LHS = (mixedHankelMatrix b k yC).det := by
          dsimp [LHS]
          rw [RingHom.map_det]
          congr 1; ext i j
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, mixedHankelMatrix, Matrix.of_apply,
            hankelDigitVal, map_mul, map_prod, map_pow, hφ_X]
        have hφR : φ RHS = (-1 : ℂ) ^ ((N - 1).choose 2) *
            ∏ r : Fin k, (lam ^ N - (v₀ r : ℂ) ^ (N / place b r.1)) ^ ((b r.1 - 1) * place b r.1) := by
          simp only [RHS, map_mul, map_pow, map_neg, map_one, map_prod, map_sub, hφ_X, yC,
            Fin.snoc_last, Fin.snoc_castSucc]
        rw [hφL, hφR]
        exact hC
      have hinj : Function.Injective (fun t : ℕ => (((M₀ + t) ^ N : ℕ) : ℤ)) := by
        intro t₁ t₂ h
        have hnat : (M₀ + t₁) ^ N = (M₀ + t₂) ^ N := Nat.cast_injective h
        have hbase : M₀ + t₁ = M₀ + t₂ := Nat.pow_left_injective (by omega : N ≠ 0) hnat
        omega
      exact (Set.infinite_range_of_injective hinj).mono hsub
    have hsnoc : (fun i : Fin (k + 1) => (v i : ℤ)) =
        Fin.snoc (fun r : Fin k => (v₀ r : ℤ)) (v (Fin.last k) : ℤ) := by
      ext i; refine Fin.lastCases ?_ ?_ i <;> simp [v₀]
    rw [hsnoc, ← hP_eval (v (Fin.last k) : ℤ), hP_zero, Polynomial.eval_zero]
  have hev := congrArg (MvPolynomial.aeval y) huniv
  have hevL : MvPolynomial.aeval y LHS = (mixedHankelMatrix b k y).det := by
    dsimp [LHS]
    rw [AlgHom.map_det]
    congr 1; ext i j
    simp [mixedHankelMatrix, hankelDigitVal, Xv]
  have hevR : MvPolynomial.aeval y RHS =
      (-1 : R) ^ ((N - 1).choose 2) *
        ∏ r : Fin k, (y (Fin.last k) - (y r.castSucc) ^ (N / place b r.1)) ^
          ((b r.1 - 1) * place b r.1) := by
    simp [RHS, Xv]
  rw [← hevL, ← hevR, hev]

/-! ### Step 4: Theorem 2B — Multivariate Mixed-Radix Carry Determinant over ANY `CommRing R` -/

/-- Recursive monomial weights `y_0 = 1`, `y_{r+1} = x_r * y_r^{b_r}` in any `CommRing R`. -/
private def carryWeightY {R : Type*} [CommRing R] (b : ℕ → ℕ) (x : ℕ → R) : ℕ → R
  | 0 => 1
  | r + 1 => x r * (carryWeightY b x r) ^ (b r)

private lemma carryWeightY_eq_prod {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (x : ℕ → R) (m : ℕ) :
    carryWeightY b x m = ∏ j ∈ Finset.range m, (x j) ^ (place b m / place b (j + 1)) := by
  induction m with
  | zero => simp [carryWeightY]
  | succ m ih =>
    rw [carryWeightY, ih, Finset.prod_range_succ, mul_comm, ← Finset.prod_pow]
    congr 1
    · apply Finset.prod_congr rfl
      intro j hj
      have hj_lt : j < m := Finset.mem_range.mp hj
      rw [← pow_mul]
      congr 1
      have h1 : place b (j + 1) * (place b m / place b (j + 1)) = place b m :=
        Nat.mul_div_cancel' (place_dvd_of_le b (by omega))
      have h2 : place b (j + 1) * (place b (m + 1) / place b (j + 1)) = place b (m + 1) :=
        Nat.mul_div_cancel' (place_dvd_of_le b (by omega))
      have hP : 0 < place b (j + 1) := place_pos b hb (j + 1)
      have hmul : place b (j + 1) * ((place b m / place b (j + 1)) * b m) =
          place b (j + 1) * (place b (m + 1) / place b (j + 1)) := by
        rw [← mul_assoc, h1, h2, place_succ]
      exact Nat.eq_of_mul_eq_mul_left hP hmul
    · rw [Nat.div_self (place_pos b hb (m + 1)), pow_one]

/-- Key ripple-carry multiplicative identity (zero inverses needed!). -/
private lemma carryWeightY_mul_carry {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (x : ℕ → R) (k i j : ℕ) (hi : i < place b k) (hj : j < place b k) :
    (∏ r : Fin k, (carryWeightY b x r.1) ^ mdigit b i r.1) *
      (∏ r : Fin k, (carryWeightY b x r.1) ^ mdigit b j r.1) *
      (∏ r ∈ Finset.range k, (x r) ^ carryBit b i j r) =
    hankelDigitVal b k (fun r : Fin (k + 1) => carryWeightY b x r.1) (i + j) := by
  have hstep : ∀ m,
      (∏ r ∈ Finset.range m, (carryWeightY b x r) ^ (mdigit b i r + mdigit b j r) *
        (x r) ^ carryBit b i j r) =
      (∏ r ∈ Finset.range m, (carryWeightY b x r) ^ mdigit b (i + j) r) *
        (carryWeightY b x m) ^ carryIn b i j m := by
    intro m
    induction m with
    | zero => simp [carryIn_zero]
    | succ m ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
      have hd := digit_carry_eq b hb i j m
      have hci : carryIn b i j (m + 1) = carryBit b i j m := rfl
      rw [hci]
      calc (∏ r ∈ Finset.range m, (carryWeightY b x r) ^ mdigit b (i + j) r) *
              (carryWeightY b x m) ^ carryIn b i j m *
              ((carryWeightY b x m) ^ (mdigit b i m + mdigit b j m) * (x m) ^ carryBit b i j m)
          = (∏ r ∈ Finset.range m, (carryWeightY b x r) ^ mdigit b (i + j) r) *
              ((carryWeightY b x m) ^ (mdigit b i m + mdigit b j m + carryIn b i j m) *
                (x m) ^ carryBit b i j m) := by rw [pow_add]; ring
        _ = (∏ r ∈ Finset.range m, (carryWeightY b x r) ^ mdigit b (i + j) r) *
              ((carryWeightY b x m) ^ (mdigit b (i + j) m + b m * carryBit b i j m) *
                (x m) ^ carryBit b i j m) := by rw [hd]
        _ = (∏ r ∈ Finset.range m, (carryWeightY b x r) ^ mdigit b (i + j) r) *
              (carryWeightY b x m) ^ mdigit b (i + j) m *
              (x m * (carryWeightY b x m) ^ b m) ^ carryBit b i j m := by
              rw [pow_add, pow_mul, mul_pow]; ring
        _ = _ := rfl
  have hk := hstep k
  have hci_k : carryIn b i j k = (i + j) / place b k := by
    have h := add_div_place b hb i j k
    rw [Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj] at h
    omega
  rw [hci_k] at hk
  unfold hankelDigitVal
  simp only [Fin.val_last, Fin.val_castSucc]
  rw [Fin.prod_univ_eq_prod_range (fun r => (carryWeightY b x r) ^ mdigit b i r) k,
    Fin.prod_univ_eq_prod_range (fun r => (carryWeightY b x r) ^ mdigit b j r) k,
    Fin.prod_univ_eq_prod_range (fun r => (carryWeightY b x r) ^ mdigit b (i + j) r) k]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  convert hk using 2
  rw [pow_add]

/-- Exact sum of the `r`-th mixed-radix digit over all `0 ≤ i < place b k`:
    `2 * ∑_{i < N} d_r(i) = N * (b_r - 1)`. -/
private lemma two_mul_sum_mdigit (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) (r : Fin k) :
    2 * ∑ i : Fin (place b k), mdigit b i.1 r.1 = place b k * (b r.1 - 1) := by
  have hP : 0 < place b r.1 := place_pos b hb r.1
  have hB : 0 < b r.1 := hb r.1
  set Q := place b k / place b (r.1 + 1)
  have hPQB : place b k = place b r.1 * b r.1 * Q := by
    have := Nat.mul_div_cancel' (place_dvd_of_le b r.2)
    rw [place_succ] at this
    exact this.symm
  have hQ : 0 < Q := Nat.pos_of_ne_zero fun h => by
    have hN := place_pos b hb k; rw [h, mul_zero] at hPQB; omega
  let e : (Fin Q × Fin (b r.1)) × Fin (place b r.1) ≃ Fin (place b k) :=
    { toFun := fun p => ⟨(p.1.1.1 * b r.1 + p.1.2.1) * place b r.1 + p.2.1, by
        rw [hPQB]
        have hq : p.1.1.1 + 1 ≤ Q := p.1.1.2
        have hd : p.1.2.1 + 1 ≤ b r.1 := p.1.2.2
        have hu : p.2.1 < place b r.1 := p.2.2
        have h1 : p.1.1.1 * b r.1 + p.1.2.1 + 1 ≤ Q * b r.1 := by nlinarith
        nlinarith⟩
      invFun := fun i =>
        ((⟨i.1 / (place b r.1 * b r.1), by
            have hlt : i.1 < place b r.1 * b r.1 * Q := hPQB ▸ i.2
            exact Nat.div_lt_of_lt_mul hlt⟩,
          ⟨(i.1 / place b r.1) % b r.1, Nat.mod_lt _ hB⟩),
         ⟨i.1 % place b r.1, Nat.mod_lt _ hP⟩)
      left_inv := by
        rintro ⟨⟨⟨q, hq⟩, ⟨d, hd⟩⟩, ⟨u, hu⟩⟩
        ext
        · dsimp
          rw [show (q * b r.1 + d) * place b r.1 + u =
              (d * place b r.1 + u) + (place b r.1 * b r.1) * q by ring,
            Nat.add_mul_div_left _ _ (Nat.mul_pos hP hB),
            Nat.div_eq_of_lt (by nlinarith : d * place b r.1 + u < place b r.1 * b r.1), zero_add]
        · dsimp
          rw [mul_comm (q * b r.1 + d) (place b r.1), Nat.mul_add_div hP, Nat.div_eq_of_lt hu,
            add_zero, mul_comm q (b r.1), Nat.mul_add_mod, Nat.mod_eq_of_lt hd]
        · dsimp
          rw [mul_comm (q * b r.1 + d) (place b r.1), Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
      right_inv := by
        intro i; ext; dsimp
        have h1 : i.1 = place b r.1 * (i.1 / place b r.1) + i.1 % place b r.1 :=
          (Nat.div_add_mod i.1 (place b r.1)).symm
        have h2 : i.1 / place b r.1 = b r.1 * ((i.1 / place b r.1) / b r.1) +
            (i.1 / place b r.1) % b r.1 := (Nat.div_add_mod (i.1 / place b r.1) (b r.1)).symm
        have h3 : (i.1 / place b r.1) / b r.1 = i.1 / (place b r.1 * b r.1) :=
          Nat.div_div_eq_div_mul i.1 (place b r.1) (b r.1)
        rw [h3] at h2
        calc (i.1 / (place b r.1 * b r.1) * b r.1 + i.1 / place b r.1 % b r.1) * place b r.1 +
              i.1 % place b r.1
            = place b r.1 * (b r.1 * (i.1 / (place b r.1 * b r.1)) +
              i.1 / place b r.1 % b r.1) + i.1 % place b r.1 := by ring
          _ = place b r.1 * (i.1 / place b r.1) + i.1 % place b r.1 := by rw [← h2]
          _ = i.1 := h1.symm }
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hdig : ∀ (q : Fin Q) (d : Fin (b r.1)) (u : Fin (place b r.1)),
      mdigit b ((q.1 * b r.1 + d.1) * place b r.1 + u.1) r.1 = d.1 := by
    intro q d u
    unfold mdigit
    rw [mul_comm (q.1 * b r.1 + d.1) (place b r.1), Nat.mul_add_div hP, Nat.div_eq_of_lt u.2,
      add_zero, mul_comm q.1 (b r.1), Nat.mul_add_mod, Nat.mod_eq_of_lt d.2]
  dsimp only [e, Equiv.coe_fn_mk]
  simp_rw [hdig, Finset.sum_const, Finset.card_fin, smul_eq_mul, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun d => d) (b r.1)]
  have htri : 2 * ∑ d ∈ Finset.range (b r.1), d = b r.1 * (b r.1 - 1) := by
    have := Finset.sum_range_id_mul_two (b r.1)
    linarith
  calc 2 * (Q * (place b r.1 * ∑ d ∈ Finset.range (b r.1), d))
      = place b r.1 * (2 * ∑ d ∈ Finset.range (b r.1), d) * Q := by ring
    _ = place b r.1 * (b r.1 * (b r.1 - 1)) * Q := by rw [htri]
    _ = (place b r.1 * b r.1 * Q) * (b r.1 - 1) := by ring
    _ = place b k * (b r.1 - 1) := by rw [hPQB]

/-- **Theorem 2B (Multivariate Mixed-Radix Carry Determinant over ANY `CommRing R`)**:
    For any radices `b : ℕ → ℕ` (`∀ r, 1 ≤ b r`), any depth `k`, `N = place b k`,
    any commutative ring `R`, and any `x : ℕ → R`:
    $$\det \left( \prod_{r=0}^{k-1} x_r^{e_r(i, j)} \right)_{0 \le i, j < N}
      = (-1)^{\binom{N-1}{2}} \prod_{r=0}^{k-1} \left( \left(\prod_{j=r}^{k-1} x_j^{Q_j}\right) - 1 \right)^{(b_r - 1) P_r}.$$ -/
theorem det_carryMatrix_full {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (x : ℕ → R) :
    (carryMatrix b k (place b k) x).det =
      (-1 : R) ^ ((place b k - 1).choose 2) *
        ∏ r : Fin k, ((∏ j ∈ Finset.Ico r.1 k, (x j) ^ suffixProd b k j) - 1) ^
          ((b r.1 - 1) * place b r.1) := by
  set N := place b k
  let S := MvPolynomial (Fin k) ℤ
  let xU : ℕ → S := fun j => if h : j < k then MvPolynomial.X ⟨j, h⟩ else 1
  let yU : Fin (k + 1) → S := fun r => carryWeightY b xU r.1
  let gU : Fin N → S := fun i => ∏ r : Fin k, (yU r.castSucc) ^ mdigit b i.1 r.1
  have hcong : mixedHankelMatrix b k yU =
      Matrix.diagonal gU * carryMatrix b k N xU * Matrix.diagonal gU := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, mixedHankelMatrix, carryMatrix,
      Matrix.of_apply]
    change hankelDigitVal b k (fun r : Fin (k + 1) => carryWeightY b xU r.1) (i.1 + j.1) =
      (∏ r : Fin k, (carryWeightY b xU r.1) ^ mdigit b i.1 r.1) *
      (∏ r ∈ Finset.range k, (xU r) ^ carryBit b i.1 j.1 r) *
      (∏ r : Fin k, (carryWeightY b xU r.1) ^ mdigit b j.1 r.1)
    rw [← carryWeightY_mul_carry b hb xU k i.1 j.1 i.2 j.2]
    ring
  have hdet_cong := congrArg Matrix.det hcong
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_mixedHankelMatrix b hb k yU] at hdet_cong
  change (-1 : S) ^ ((N - 1).choose 2) *
      ∏ r : Fin k, (yU (Fin.last k) - (yU r.castSucc) ^ (N / place b r.1)) ^
        ((b r.1 - 1) * place b r.1) =
    (∏ i : Fin N, gU i) * (carryMatrix b k N xU).det * (∏ i : Fin N, gU i) at hdet_cong
  have hy_factor : ∀ r : Fin k,
      yU (Fin.last k) - (yU r.castSucc) ^ (N / place b r.1) =
        (yU r.castSucc) ^ (N / place b r.1) *
          ((∏ j ∈ Finset.Ico r.1 k, (xU j) ^ suffixProd b k j) - 1) := by
    intro r
    have hLast : yU (Fin.last k) = ∏ j ∈ Finset.range k, (xU j) ^ suffixProd b k j := by
      dsimp [yU, suffixProd]
      exact carryWeightY_eq_prod b hb xU k
    have hPow : (yU r.castSucc) ^ (N / place b r.1) =
        ∏ j ∈ Finset.range r.1, (xU j) ^ suffixProd b k j := by
      dsimp [yU, suffixProd]
      rw [carryWeightY_eq_prod b hb xU r.1, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro j hj
      have hj_lt : j < r.1 := Finset.mem_range.mp hj
      rw [← pow_mul]
      congr 1
      have h1 : place b (j + 1) * (place b r.1 / place b (j + 1)) = place b r.1 :=
        Nat.mul_div_cancel' (place_dvd_of_le b (by omega))
      have h2 : place b r.1 * (N / place b r.1) = N :=
        Nat.mul_div_cancel' (place_dvd_of_le b (le_of_lt r.2))
      have h3 : place b (j + 1) * (N / place b (j + 1)) = N :=
        Nat.mul_div_cancel' (place_dvd_of_le b (by omega))
      have hP : 0 < place b (j + 1) := place_pos b hb (j + 1)
      have hmul : place b (j + 1) * ((place b r.1 / place b (j + 1)) * (N / place b r.1)) =
          place b (j + 1) * (N / place b (j + 1)) := by
        rw [← mul_assoc, h1, h2, h3]
      exact Nat.eq_of_mul_eq_mul_left hP hmul
    have hsplit : ∏ j ∈ Finset.range k, (xU j) ^ suffixProd b k j =
        (∏ j ∈ Finset.range r.1, (xU j) ^ suffixProd b k j) *
        (∏ j ∈ Finset.Ico r.1 k, (xU j) ^ suffixProd b k j) := by
      have hdisj : Disjoint (Finset.range r.1) (Finset.Ico r.1 k) := by
        rw [Finset.disjoint_left]; intro a ha1 ha2
        have := Finset.mem_range.mp ha1; have := (Finset.mem_Ico.mp ha2).1; omega
      have hunion : Finset.range r.1 ∪ Finset.Ico r.1 k = Finset.range k := by
        ext a; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
      rw [← Finset.prod_union hdisj, hunion]
    rw [hLast, hPow, hsplit]
    ring
  simp_rw [hy_factor, mul_pow, Finset.prod_mul_distrib] at hdet_cong
  have hscale_eq : (∏ i : Fin N, gU i) * (∏ i : Fin N, gU i) =
      ∏ r : Fin k, ((yU r.castSucc) ^ (N / place b r.1)) ^ ((b r.1 - 1) * place b r.1) := by
    have hL : (∏ i : Fin N, gU i) * (∏ i : Fin N, gU i) =
        ∏ r : Fin k, (yU r.castSucc) ^ (2 * ∑ i : Fin N, mdigit b i.1 r.1) := by
      dsimp [gU]
      rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro r _
      rw [Finset.prod_pow_eq_pow_sum, ← pow_add, two_mul]
    rw [hL]
    apply Finset.prod_congr rfl
    intro r _
    rw [← pow_mul, two_mul_sum_mdigit b hb k r]
    congr 1
    have h1 : place b r.1 * (N / place b r.1) = N :=
      Nat.mul_div_cancel' (place_dvd_of_le b (le_of_lt r.2))
    calc N * (b r.1 - 1) = (place b r.1 * (N / place b r.1)) * (b r.1 - 1) := by rw [h1]
      _ = N / place b r.1 * ((b r.1 - 1) * place b r.1) := by ring
  have hscale_ne : (∏ i : Fin N, gU i) * (∏ i : Fin N, gU i) ≠ 0 := by
    rw [hscale_eq]
    apply Finset.prod_ne_zero_iff.mpr
    intro r _
    apply pow_ne_zero
    apply pow_ne_zero
    dsimp [yU]
    rw [carryWeightY_eq_prod b hb xU r.1]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hj_lt : j < k := lt_trans (Finset.mem_range.mp hj) r.2
    apply pow_ne_zero
    simp only [xU, hj_lt, ↓reduceDIte]
    exact MvPolynomial.X_ne_zero _
  have huniv : (carryMatrix b k N xU).det =
      (-1 : S) ^ ((N - 1).choose 2) *
        ∏ r : Fin k, ((∏ j ∈ Finset.Ico r.1 k, (xU j) ^ suffixProd b k j) - 1) ^
          ((b r.1 - 1) * place b r.1) := by
    apply mul_left_cancel₀ hscale_ne
    calc ((∏ i : Fin N, gU i) * (∏ i : Fin N, gU i)) * (carryMatrix b k N xU).det
        = (∏ i : Fin N, gU i) * (carryMatrix b k N xU).det * (∏ i : Fin N, gU i) := by ring
      _ = (-1 : S) ^ ((N - 1).choose 2) *
          ((∏ r : Fin k, ((yU r.castSucc) ^ (N / place b r.1)) ^ ((b r.1 - 1) * place b r.1)) *
            ∏ r : Fin k, ((∏ j ∈ Finset.Ico r.1 k, (xU j) ^ suffixProd b k j) - 1) ^
              ((b r.1 - 1) * place b r.1)) := hdet_cong.symm
      _ = ((∏ i : Fin N, gU i) * (∏ i : Fin N, gU i)) *
          ((-1 : S) ^ ((N - 1).choose 2) *
            ∏ r : Fin k, ((∏ j ∈ Finset.Ico r.1 k, (xU j) ^ suffixProd b k j) - 1) ^
              ((b r.1 - 1) * place b r.1)) := by rw [← hscale_eq]; ring
  let ev : S →ₐ[ℤ] R := MvPolynomial.aeval (fun j : Fin k => x j.1)
  have hev_x : ∀ j < k, ev (xU j) = x j := fun j hj => by
    dsimp only [ev, xU, S]
    simp only [hj, ↓reduceDIte, MvPolynomial.aeval_X]
  have hev := congrArg ev huniv
  have hevL : ev (carryMatrix b k N xU).det = (carryMatrix b k N x).det := by
    rw [AlgHom.map_det]
    congr 1; ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, carryMatrix, Matrix.of_apply, map_prod,
      map_pow]
    apply Finset.prod_congr rfl
    intro r hr
    rw [hev_x r (Finset.mem_range.mp hr)]
  have hevR : ev ((-1 : S) ^ ((N - 1).choose 2) *
        ∏ r : Fin k, ((∏ j ∈ Finset.Ico r.1 k, (xU j) ^ suffixProd b k j) - 1) ^
          ((b r.1 - 1) * place b r.1)) =
      (-1 : R) ^ ((N - 1).choose 2) *
        ∏ r : Fin k, ((∏ j ∈ Finset.Ico r.1 k, (x j) ^ suffixProd b k j) - 1) ^
          ((b r.1 - 1) * place b r.1) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_prod, map_sub]
    congr 1
    apply Finset.prod_congr rfl
    intro r _
    congr 2
    apply Finset.prod_congr rfl
    intro j hj
    rw [hev_x j (Finset.mem_Ico.mp hj).2]
  rw [← hevL, ← hevR, hev]

/-! ### Step 5: Corollaries — Linear Carry Matrix, Kummer Valuation Matrix, Binary Carry-Word Matrix -/

/-- Helper: extracting the `X^{m}`-coefficient of a product of `m` polynomials each divisible by `X`. -/
private lemma coeff_prod_of_coeff_zero_eq_zero {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (f : ι → Polynomial R) (hf0 : ∀ i ∈ s, (f i).coeff 0 = 0) :
    (∀ d < s.card, (∏ i ∈ s, f i).coeff d = 0) ∧
    (∏ i ∈ s, f i).coeff s.card = ∏ i ∈ s, (f i).coeff 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨hlo, htop⟩ := ih (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
    have ha0 : (f a).coeff 0 = 0 := hf0 a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Finset.prod_insert ha]
    constructor
    · intro d hd
      rw [Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨p, q⟩ hpq
      have hpq_sum : p + q = d := Finset.mem_antidiagonal.mp hpq
      by_cases hp0 : p = 0
      · rw [hp0, ha0, zero_mul]
      · have hq_lt : q < s.card := by omega
        rw [hlo q hq_lt, mul_zero]
    · rw [Polynomial.coeff_mul, Finset.sum_eq_single (1, s.card)]
      · rw [htop]
      · rintro ⟨p, q⟩ hpq hne
        have hpq_sum : p + q = s.card + 1 := Finset.mem_antidiagonal.mp hpq
        by_cases hp0 : p = 0
        · rw [hp0, ha0, zero_mul]
        · have hq_lt : q < s.card := by
            by_contra hge; push Not at hge
            have hp1 : p = 1 := by omega
            have hq1 : q = s.card := by omega
            exact hne (Prod.ext hp1 hq1)
          rw [hlo q hq_lt, mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_antidiagonal.mpr (by omega))).elim

/-- Helper: `(p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0`. -/
private lemma coeff_mul_one_eq {R : Type*} [CommRing R] (p q : Polynomial R) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero]
  simp

/-- Helper: `(∏ j ∈ s, (1 + C (w j) * X) ^ e j) - 1` has `coeff 0 = 0` and `coeff 1 = ∑ j ∈ s, e j * w j`. -/
private lemma coeff_prod_one_add_X_sub_one {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (w : ι → R) (e : ι → ℕ) :
    let P : Polynomial R := (∏ j ∈ s, (1 + Polynomial.C (w j) * Polynomial.X) ^ e j) - 1
    P.coeff 0 = 0 ∧ P.coeff 1 = ∑ j ∈ s, (e j : R) * w j := by
  intro P
  have hone1 : (1 : Polynomial R).coeff 1 = 0 := by
    rw [Polynomial.coeff_one]; simp
  suffices h : ∀ t : Finset ι,
      (∏ j ∈ t, (1 + Polynomial.C (w j) * Polynomial.X) ^ e j).coeff 0 = 1 ∧
      (∏ j ∈ t, (1 + Polynomial.C (w j) * Polynomial.X) ^ e j).coeff 1 =
        ∑ j ∈ t, (e j : R) * w j by
    obtain ⟨h0, h1⟩ := h s
    constructor
    · simp [P, h0]
    · simp [P, h1, hone1]
  have hlin0 : ∀ a : R, (1 + Polynomial.C a * Polynomial.X).coeff 0 = 1 := fun a => by simp
  have hlin1 : ∀ a : R, (1 + Polynomial.C a * Polynomial.X).coeff 1 = a := fun a => by
    rw [Polynomial.coeff_add, hone1, zero_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one]
  have hpow : ∀ (a : R) (m : ℕ),
      ((1 + Polynomial.C a * Polynomial.X) ^ m).coeff 0 = 1 ∧
      ((1 + Polynomial.C a * Polynomial.X) ^ m).coeff 1 = (m : R) * a := by
    intro a m
    induction m with
    | zero => simp [hone1]
    | succ m ihm =>
      rw [pow_succ]
      constructor
      · rw [Polynomial.mul_coeff_zero, ihm.1, hlin0, mul_one]
      · rw [coeff_mul_one_eq, ihm.1, ihm.2, hlin0, hlin1]
        push_cast; ring
  intro t
  classical
  induction t using Finset.induction_on with
  | empty => simp [hone1]
  | @insert j t hj iht =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    obtain ⟨hp0, hp1⟩ := hpow (w j) (e j)
    constructor
    · rw [Polynomial.mul_coeff_zero, hp0, iht.1, mul_one]
    · rw [coeff_mul_one_eq, hp0, hp1, iht.1, iht.2]
      ring

/-- Helper: `coeff (m)` of `det` of an `(m + 1) × (m + 1)` matrix whose row `0` is all `1`'s,
    col `0` is all `1`'s, and entry `(i, j) - 1` has `coeff 0 = 0`. -/
private lemma coeff_det_one_plus_X_succ {R : Type*} [CommRing R] (m : ℕ)
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (Polynomial R))
    (hrow0 : ∀ j : Fin (m + 1), M 0 j = 1)
    (hcol0 : ∀ i : Fin (m + 1), M i 0 = 1)
    (h0 : ∀ i j : Fin (m + 1), (M i j - 1).coeff 0 = 0) :
    M.det.coeff m =
      (Matrix.of fun i j : Fin m => (M i.succ j.succ - 1).coeff 1).det := by
  let M' : Matrix (Fin (m + 1)) (Fin (m + 1)) (Polynomial R) :=
    Matrix.of fun i j => if i = 0 then 1 else M i j - 1
  have hM'_det : M'.det = M.det := by
    suffices hstep : ∀ s : Finset (Fin (m + 1)),
        (Matrix.of fun i j => if i ∈ s ∧ i ≠ 0 then M i j - 1 else M i j).det = M.det by
      have heq : M' = Matrix.of fun i j =>
          if i ∈ (Finset.univ : Finset (Fin (m + 1))) ∧ i ≠ 0 then M i j - 1 else M i j := by
        ext i j
        simp only [M', Matrix.of_apply, Finset.mem_univ, true_and]
        by_cases hi : i = 0
        · subst hi; simp [hrow0 j]
        · simp [hi]
      rw [heq, hstep Finset.univ]
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      have : (Matrix.of fun i j =>
          if i ∈ (∅ : Finset (Fin (m + 1))) ∧ i ≠ 0 then M i j - 1 else M i j) = M := by
        ext i j; simp
      rw [this]
    | @insert i₀ s hi₀ ih =>
      by_cases h0i : i₀ = 0
      · subst h0i
        have heq : (Matrix.of fun i j =>
            if i ∈ insert (0 : Fin (m + 1)) s ∧ i ≠ 0 then M i j - 1 else M i j) =
            Matrix.of fun i j => if i ∈ s ∧ i ≠ 0 then M i j - 1 else M i j := by
          ext i j
          simp only [Matrix.of_apply, Finset.mem_insert]
          by_cases hi : i = 0 <;> simp [hi]
        rw [heq, ih]
      · set A : Matrix (Fin (m + 1)) (Fin (m + 1)) (Polynomial R) :=
          Matrix.of fun i j => if i ∈ s ∧ i ≠ 0 then M i j - 1 else M i j
        have hupd : (Matrix.of fun i j =>
            if i ∈ insert i₀ s ∧ i ≠ 0 then M i j - 1 else M i j) =
            A.updateRow i₀ (A i₀ - A 0) := by
          ext i j
          have hA0 : A 0 j = 1 := by simp [A, hrow0 j]
          have hAi₀ : A i₀ j = M i₀ j := by simp [A, hi₀]
          by_cases hi : i = i₀
          · subst hi; simp [h0i, hA0, hAi₀]
          · rw [Matrix.updateRow_ne hi]; simp [A, hi]
        have hsub : (A.updateRow i₀ (A i₀ - A 0)).det = A.det := by
          have h : A i₀ - A 0 = A i₀ + (-1 : Polynomial R) • A 0 := by
            ext j; simp [sub_eq_add_neg]
          rw [h, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul]
          have hz : (A.updateRow i₀ (A 0)).det = 0 :=
            Matrix.det_zero_of_row_eq h0i (by simp [Matrix.updateRow_ne (Ne.symm h0i)])
          rw [hz, mul_zero, add_zero]
        rw [hupd, hsub, ih]
  rw [← hM'_det]
  have hdet_sub : M'.det = (M'.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_column_zero]
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · simp [M']
    · intro i _ hi
      have hM'0 : M' i 0 = 0 := by
        simp only [M', Matrix.of_apply, hi, ↓reduceIte, hcol0 i, sub_self]
      rw [hM'0, mul_zero, zero_mul]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hdet_sub, Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ _
  have hsmul : ∀ (u : ℤˣ) (p : Polynomial R) (d : ℕ), (u • p).coeff d = u • p.coeff d := by
    intro u p d
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  rw [hsmul]
  congr 1
  have hprod_coeff := (coeff_prod_of_coeff_zero_eq_zero (Finset.univ : Finset (Fin m))
    (fun i => M'.submatrix Fin.succ Fin.succ (σ i) i)
    (fun i _ => by
      simp only [Matrix.submatrix_apply, M', Matrix.of_apply, Fin.succ_ne_zero, ↓reduceIte]
      exact h0 _ _)).2
  rw [Finset.card_fin] at hprod_coeff
  rw [hprod_coeff]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Matrix.submatrix_apply, M', Matrix.of_apply, Fin.succ_ne_zero, ↓reduceIte]

/-- **Corollary 2.1 (Weighted Linear Carry Determinant over ANY `CommRing R`)**:
    For any mixed-radix `b` (`∀ r, 1 ≤ b r`), depth `k`, `N = place b k`, and any weights `w : ℕ → R`:
    $$\det \left( \sum_{r=0}^{k-1} w_r e_r(i, j) \right)_{1 \le i, j < N}
      = (-1)^{\binom{N-1}{2}} \prod_{r=0}^{k-1} \left( \sum_{j=r}^{k-1} Q_j w_j \right)^{(b_r - 1) P_r}.$$ -/
theorem det_weightedLinearCarryMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (w : ℕ → R) :
    (Matrix.of fun i j : Fin (place b k - 1) =>
      ∑ r ∈ Finset.range k, (carryBit b (i.1 + 1) (j.1 + 1) r : R) * w r).det =
    (-1 : R) ^ ((place b k - 1).choose 2) *
      ∏ r : Fin k, (∑ j ∈ Finset.Ico r.1 k, (suffixProd b k j : R) * w j) ^
        ((b r.1 - 1) * place b r.1) := by
  set N := place b k
  have hN : 1 ≤ N := place_pos b hb k
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hm_eq : N - 1 = m := by omega
  let xP : ℕ → Polynomial R := fun r => 1 + Polynomial.C (w r) * Polynomial.X
  have hmain := congrArg (fun p : Polynomial R => p.coeff m) (det_carryMatrix_full b hb k xP)
  -- Reindex `carryMatrix b k N xP` to `Fin (m + 1)` via `finCongr hm`
  let M1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Polynomial R) :=
    (carryMatrix b k N xP).submatrix (finCongr hm.symm) (finCongr hm.symm)
  have hM1_det : M1.det = (carryMatrix b k N xP).det :=
    Matrix.det_submatrix_equiv_self (finCongr hm.symm) (carryMatrix b k N xP)
  have hLHS : (carryMatrix b k N xP).det.coeff m =
      (Matrix.of fun i j : Fin (N - 1) =>
        ∑ r ∈ Finset.range k, (carryBit b (i.1 + 1) (j.1 + 1) r : R) * w r).det := by
    rw [← hM1_det, coeff_det_one_plus_X_succ m M1]
    · have heq : (Matrix.of fun i j : Fin (N - 1) =>
            ∑ r ∈ Finset.range k, (carryBit b (i.1 + 1) (j.1 + 1) r : R) * w r) =
          (Matrix.of fun i j : Fin m => (M1 i.succ j.succ - 1).coeff 1).submatrix
            (finCongr hm_eq) (finCongr hm_eq) := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.of_apply, M1, carryMatrix, xP,
          finCongr_apply, Fin.val_succ, Fin.val_cast]
        exact ((coeff_prod_one_add_X_sub_one (Finset.range k) w
          (fun r => carryBit b (i.1 + 1) (j.1 + 1) r)).2).symm
      rw [heq, Matrix.det_submatrix_equiv_self]
    · intro j
      simp only [M1, Matrix.submatrix_apply, carryMatrix, Matrix.of_apply, finCongr_apply,
        Fin.val_cast, Fin.val_zero]
      apply Finset.prod_eq_one; intro r _
      rw [carryBit_zero_left b hb j.1 r, pow_zero]
    · intro i
      simp only [M1, Matrix.submatrix_apply, carryMatrix, Matrix.of_apply, finCongr_apply,
        Fin.val_cast, Fin.val_zero]
      apply Finset.prod_eq_one; intro r _
      rw [carryBit_zero_right b hb i.1 r, pow_zero]
    · intro i j
      exact (coeff_prod_one_add_X_sub_one (Finset.range k) w
        (fun r => carryBit b i.1 j.1 r)).1
  have hsum_exp : ∑ r : Fin k, (b r.1 - 1) * place b r.1 = m := by
    rw [Fin.sum_univ_eq_sum_range (fun r => (b r - 1) * place b r) k, sum_max_digits b hb k]
    exact hm_eq
  let F_r : Fin k → Polynomial R :=
    fun r => (∏ j ∈ Finset.Ico r.1 k, (xP j) ^ suffixProd b k j) - 1
  let idxType := Σ r : Fin k, Fin ((b r.1 - 1) * place b r.1)
  have hcard_idx : Fintype.card idxType = m := by
    simp [idxType, hsum_exp]
  have hprod_eq : ∏ r : Fin k, (F_r r) ^ ((b r.1 - 1) * place b r.1) =
      ∏ p : idxType, F_r p.1 := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro r _
    simp [Finset.prod_const]
  have hRHS_prod : (∏ r : Fin k, (F_r r) ^ ((b r.1 - 1) * place b r.1)).coeff m =
      ∏ r : Fin k, (∑ j ∈ Finset.Ico r.1 k, (suffixProd b k j : R) * w j) ^
        ((b r.1 - 1) * place b r.1) := by
    rw [hprod_eq, ← hcard_idx]
    have hc := (coeff_prod_of_coeff_zero_eq_zero (Finset.univ : Finset idxType)
      (fun p => F_r p.1)
      (fun p _ => (coeff_prod_one_add_X_sub_one (Finset.Ico p.1.1 k) w
        (fun j => suffixProd b k j)).1)).2
    rw [Finset.card_univ] at hc
    rw [hc, Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro r _
    simp only [Finset.prod_const, Finset.card_fin]
    congr 1
    exact (coeff_prod_one_add_X_sub_one (Finset.Ico r.1 k) w (fun j => suffixProd b k j)).2
  have hsign_coeff : ∀ (p : Polynomial R),
      ((-1 : Polynomial R) ^ ((N - 1).choose 2) * p).coeff m =
        (-1 : R) ^ ((N - 1).choose 2) * p.coeff m := by
    intro p
    have h1 : (-1 : Polynomial R) ^ ((N - 1).choose 2) =
        Polynomial.C ((-1 : R) ^ ((N - 1).choose 2)) := by simp
    rw [h1, Polynomial.coeff_C_mul]
  rw [hLHS, hsign_coeff, hRHS_prod] at hmain
  exact hmain

/-- **Corollary 2.2 (The Kummer `p`-adic Valuation Matrix Determinant)**:
    For every prime `p` and every `k : ℕ`:
    $$\det \left( v_p \binom{i+j}{i} \right)_{1 \le i, j < p^k}
      = (-1)^{\binom{p^k - 1}{2}} \prod_{r=0}^{k-1} \left( \frac{p^{k-r} - 1}{p - 1} \right)^{(p - 1) p^r}.$$ -/
theorem det_kummer_padicValNat_choose (p k : ℕ) [hp : Fact p.Prime] :
    (Matrix.of fun i j : Fin (p ^ k - 1) =>
      (padicValNat p ((i.1 + 1 + (j.1 + 1)).choose (i.1 + 1)) : ℤ)).det =
    (-1 : ℤ) ^ ((p ^ k - 1).choose 2) *
      ∏ r : Fin k, (((p ^ (k - r.1) - 1) / (p - 1) : ℕ) : ℤ) ^ ((p - 1) * p ^ r.1) := by
  have hp1 : 1 ≤ p := le_of_lt hp.out.one_lt
  have hp2 : 2 ≤ p := hp.out.two_le
  have hb : ∀ _r : ℕ, 1 ≤ p := fun _ => hp1
  have h1 := det_weightedLinearCarryMatrix (R := ℤ) (fun _ => p) hb k (fun _ => 1)
  have hpk : place (fun _ => p) k = p ^ k := place_const p k
  have hmat : (Matrix.of fun i j : Fin (p ^ k - 1) =>
        (padicValNat p ((i.1 + 1 + (j.1 + 1)).choose (i.1 + 1)) : ℤ)).det =
      (Matrix.of fun i j : Fin (place (fun _ => p) k - 1) =>
        ∑ r ∈ Finset.range k, (carryBit (fun _ => p) (i.1 + 1) (j.1 + 1) r : ℤ) * 1).det := by
    have heq : Matrix.of (fun i j : Fin (p ^ k - 1) =>
          (padicValNat p ((i.1 + 1 + (j.1 + 1)).choose (i.1 + 1)) : ℤ)) =
        (Matrix.of fun i j : Fin (place (fun _ => p) k - 1) =>
          ∑ r ∈ Finset.range k, (carryBit (fun _ => p) (i.1 + 1) (j.1 + 1) r : ℤ) * 1).submatrix
            (finCongr (by rw [hpk])) (finCongr (by rw [hpk])) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply, finCongr_apply, Fin.val_cast, mul_one]
      have hi : i.1 + 1 < p ^ k := by have := i.2; have : 1 ≤ p ^ k := Nat.one_le_pow k p hp1; omega
      have hj : j.1 + 1 < p ^ k := by have := j.2; have : 1 ≤ p ^ k := Nat.one_le_pow k p hp1; omega
      rw [kummer_padicValNat_choose p k (i.1 + 1) (j.1 + 1) hi hj]
      unfold carryCount
      push_cast
      rfl
    rw [heq, Matrix.det_submatrix_equiv_self]
  rw [hmat, h1, hpk]
  congr 1
  apply Finset.prod_congr rfl
  intro r _
  rw [place_const]
  congr 1
  have hsum : ∑ j ∈ Finset.Ico r.1 k, (suffixProd (fun _ => p) k j : ℤ) * 1 =
      (((p ^ (k - r.1) - 1) / (p - 1) : ℕ) : ℤ) := by
    have hnat : ∑ j ∈ Finset.Ico r.1 k, suffixProd (fun _ => p) k j =
        (p ^ (k - r.1) - 1) / (p - 1) := by
      have hgeom : (p - 1) * ∑ j ∈ Finset.Ico r.1 k, suffixProd (fun _ => p) k j =
          p ^ (k - r.1) - 1 := by
        have hbij : ∑ j ∈ Finset.Ico r.1 k, suffixProd (fun _ => p) k j =
            ∑ t ∈ Finset.range (k - r.1), p ^ t := by
          refine Finset.sum_bij (fun j hj => k - 1 - j) ?_ ?_ ?_ ?_
          · intro j hj
            have h1 := Finset.mem_Ico.mp hj
            exact Finset.mem_range.mpr (by omega)
          · intro j₁ hj₁ j₂ hj₂ h
            have h1 := Finset.mem_Ico.mp hj₁
            have h2 := Finset.mem_Ico.mp hj₂
            omega
          · intro t ht
            have ht' := Finset.mem_range.mp ht
            exact ⟨k - 1 - t, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro j hj
            exact suffixProd_const p k j hp1 (Finset.mem_Ico.mp hj).2
        rw [hbij]
        have hgs := geom_sum_mul (p : ℤ) (k - r.1)
        have hnat_gs : (∑ t ∈ Finset.range (k - r.1), p ^ t) * (p - 1) = p ^ (k - r.1) - 1 := by
          have h1 : 1 ≤ p ^ (k - r.1) := Nat.one_le_pow _ _ hp1
          zify [hp1, h1]
          linarith
        linarith
      rw [← hgeom, Nat.mul_div_right _ (by omega)]
    rw [← hnat]
    push_cast
    simp
  exact hsum

/-- **Corollary 2.3 (The Binary Carry-Word Determinant)**:
    For every `k : ℕ`:
    $$\det \Big( (i + j) \oplus i \oplus j \Big)_{1 \le i, j < 2^k}
      = (-1)^{\binom{2^k - 1}{2}} \cdot 2^{k (2^k - 1)} \cdot \prod_{r=0}^{k-1} (k - r)^{2^r}.$$ -/
theorem det_binary_carry_word (k : ℕ) :
    (Matrix.of fun i j : Fin (2 ^ k - 1) =>
      ((((i.1 + 1) + (j.1 + 1)) ^^^ (i.1 + 1) ^^^ (j.1 + 1)) : ℤ)).det =
    (-1 : ℤ) ^ ((2 ^ k - 1).choose 2) * (2 : ℤ) ^ (k * (2 ^ k - 1)) *
      ∏ r : Fin k, ((k - r.1 : ℤ)) ^ (2 ^ r.1) := by
  have hb : ∀ _r : ℕ, 1 ≤ 2 := fun _ => by omega
  have h1 := det_weightedLinearCarryMatrix (R := ℤ) (fun _ => 2) hb k (fun r => (2 : ℤ) ^ (r + 1))
  have h2k : place (fun _ => 2) k = 2 ^ k := place_const 2 k
  have hmat : (Matrix.of fun i j : Fin (2 ^ k - 1) =>
        ((((i.1 + 1) + (j.1 + 1)) ^^^ (i.1 + 1) ^^^ (j.1 + 1)) : ℤ)).det =
      (Matrix.of fun i j : Fin (place (fun _ => 2) k - 1) =>
        ∑ r ∈ Finset.range k, (carryBit (fun _ => 2) (i.1 + 1) (j.1 + 1) r : ℤ) *
          (2 : ℤ) ^ (r + 1)).det := by
    have heq : Matrix.of (fun i j : Fin (2 ^ k - 1) =>
          ((((i.1 + 1) + (j.1 + 1)) ^^^ (i.1 + 1) ^^^ (j.1 + 1)) : ℤ)) =
        (Matrix.of fun i j : Fin (place (fun _ => 2) k - 1) =>
          ∑ r ∈ Finset.range k, (carryBit (fun _ => 2) (i.1 + 1) (j.1 + 1) r : ℤ) *
            (2 : ℤ) ^ (r + 1)).submatrix
            (finCongr (by rw [h2k])) (finCongr (by rw [h2k])) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply, finCongr_apply, Fin.val_cast]
      have hi : i.1 + 1 < 2 ^ k := by have := i.2; have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega); omega
      have hj : j.1 + 1 < 2 ^ k := by have := j.2; have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega); omega
      rw [binary_carry_word_eq k (i.1 + 1) (j.1 + 1) hi hj]
      push_cast
      apply Finset.sum_congr rfl
      intro r _; ring
    rw [heq, Matrix.det_submatrix_equiv_self]
  rw [hmat, h1, h2k]
  have hterm : ∀ r : Fin k,
      ∑ j ∈ Finset.Ico r.1 k, (suffixProd (fun _ => 2) k j : ℤ) * (2 : ℤ) ^ (j + 1) =
        (2 : ℤ) ^ k * (k - r.1 : ℤ) := by
    intro r
    have hconst : ∀ j ∈ Finset.Ico r.1 k,
        (suffixProd (fun _ => 2) k j : ℤ) * (2 : ℤ) ^ (j + 1) = (2 : ℤ) ^ k := by
      intro j hj
      have hj_lt : j < k := (Finset.mem_Ico.mp hj).2
      rw [suffixProd_const 2 k j (by omega) hj_lt]
      push_cast
      rw [← pow_add]
      congr 1; omega
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      Nat.cast_sub (le_of_lt r.2), mul_comm]
  simp_rw [hterm, place_const, show 2 - 1 = 1 from rfl, one_mul, mul_pow,
    Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  have hsum2 : ∑ r : Fin k, k * 2 ^ r.1 = k * (2 ^ k - 1) := by
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun r => 2 ^ r) k]
    congr 1
    have hgs := sum_max_digits (fun _ => 2) hb k
    simp [place_const] at hgs
    exact hgs
  rw [hsum2, mul_assoc]

/-- **Corollary 2.4 (Thue–Morse Power-of-Two Exact Hankel Determinant)**:
    For every `k ≥ 2`, `det ((-1)^{s_2(i+j)})_{0 ≤ i, j < 2^k} = 2^{2^k - 1}`. -/
theorem det_thueMorse_pow_two (k : ℕ) (hk : 2 ≤ k) :
    (Matrix.of fun i j : Fin (2 ^ k) =>
      (-1 : ℤ) ^ mdigitSum (fun _ => 2) (k + 1) (i.1 + j.1)).det = (2 : ℤ) ^ (2 ^ k - 1) := by
  have hb : ∀ _r : ℕ, 1 ≤ 2 := fun _ => by omega
  have h2k : place (fun _ => 2) k = 2 ^ k := place_const 2 k
  have h1 := det_mixedHankelMatrix (R := ℤ) (fun _ => 2) hb k (fun _ => (-1 : ℤ))
  have hmat : (Matrix.of fun i j : Fin (2 ^ k) =>
        (-1 : ℤ) ^ mdigitSum (fun _ => 2) (k + 1) (i.1 + j.1)).det =
      (mixedHankelMatrix (fun _ => 2) k (fun _ => (-1 : ℤ))).det := by
    have heq : Matrix.of (fun i j : Fin (2 ^ k) =>
          (-1 : ℤ) ^ mdigitSum (fun _ => 2) (k + 1) (i.1 + j.1)) =
        (mixedHankelMatrix (fun _ => 2) k (fun _ => (-1 : ℤ))).submatrix
          (finCongr h2k.symm) (finCongr h2k.symm) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply, finCongr_apply, Fin.val_cast,
        mixedHankelMatrix, hankelDigitVal, Finset.prod_pow_eq_pow_sum]
      rw [h2k]
      have hdk : mdigit (fun _ => 2) (i.1 + j.1) k = (i.1 + j.1) / 2 ^ k := by
        unfold mdigit; rw [place_const]; dsimp
        exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by omega))
      unfold mdigitSum
      rw [Finset.sum_range_succ, hdk, pow_add,
        Fin.sum_univ_eq_sum_range (fun r => mdigit (fun _ => 2) (i.1 + j.1) r) k]
    rw [heq, Matrix.det_submatrix_equiv_self]
  rw [hmat, h1, h2k]
  have hfactor : ∀ r : Fin k,
      ((-1 : ℤ) - (-1 : ℤ) ^ (2 ^ k / place (fun _ => 2) r.1)) ^ ((2 - 1) * place (fun _ => 2) r.1) =
        (-2 : ℤ) ^ (2 ^ r.1) := by
    intro r
    rw [place_const, show 2 - 1 = 1 from rfl, one_mul]
    have hdiv : 2 ^ k / 2 ^ r.1 = 2 ^ (k - r.1) := by
      have : 2 ^ k = 2 ^ r.1 * 2 ^ (k - r.1) := by rw [← pow_add]; congr 1; omega
      rw [this, Nat.mul_div_right _ (by positivity)]
    have heven : Even (2 ^ (k - r.1)) := by
      have hpos : 1 ≤ k - r.1 := by omega
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hpos
      rw [hm, pow_succ]
      exact ⟨2 ^ m, by ring⟩
    rw [hdiv, heven.neg_one_pow]
    norm_num
  simp_rw [hfactor]
  have hprod : ∏ r : Fin k, (-2 : ℤ) ^ (2 ^ r.1) = (-2 : ℤ) ^ (2 ^ k - 1) := by
    rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun r => 2 ^ r) k]
    have hgs := sum_max_digits (fun _ => 2) hb k
    simp [place_const] at hgs
    rw [hgs]
  rw [hprod]
  have h4dvd : 4 ∣ 2 ^ k := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hk
    rw [hm, pow_add]; norm_num
  obtain ⟨q, hq⟩ := h4dvd
  have hqpos : 1 ≤ q := by
    have : 4 ≤ 2 ^ k := by
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk
      norm_num at this; exact this
    omega
  have hodd1 : (2 ^ k - 1) % 2 = 1 := by omega
  have hodd2 : (2 ^ k - 1).choose 2 % 2 = 1 := by
    rw [choose_two_mod_two]; omega
  have hpow1 : (-1 : ℤ) ^ ((2 ^ k - 1).choose 2) = -1 := by
    set C := (2 ^ k - 1).choose 2
    have hC : C % 2 = 1 := hodd2
    rw [← Nat.div_add_mod C 2, hC, pow_add, pow_mul]; norm_num
  have hpow_neg1 : (-1 : ℤ) ^ (2 ^ k - 1) = -1 := by
    set E := 2 ^ k - 1
    have hE : E % 2 = 1 := hodd1
    rw [← Nat.div_add_mod E 2, hE, pow_add, pow_mul]; norm_num
  have hpow2 : (-2 : ℤ) ^ (2 ^ k - 1) = -((2 : ℤ) ^ (2 ^ k - 1)) := by
    rw [show (-2 : ℤ) = (-1 : ℤ) * 2 by ring, mul_pow, hpow_neg1]; ring
  rw [hpow1, hpow2]
  ring

end NovelCarry
