import ConwayNimberArtinSchreierTower.Defs

namespace ConwaySilicon
namespace Nim
/-- Simultaneous proof of field invertibility `x ≠ 0 → x ⊗ inv x = 1` for all `k`. -/
theorem mul_inv : ∀ {k : Nat} (x : Nim k), x ≠ zero → mul x (inv x) = one
  | 0, .bit false, h => absurd rfl h
  | 0, .bit true, _  => rfl
  | k + 1, .pair a b, hne => by
    have hnorm : norm (.pair a b) ≠ zero := by
      intro h0
      by_cases ha : a = zero
      · subst ha
        simp only [norm, sq_zero, scaleH_zero, zero_mul, zero_xor] at h0
        -- b^2 = 0 ⇒ b = 0 using inv at level k
        have hb : b = zero := by
          by_cases hb0 : b = zero
          · exact hb0
          · have h1 := mul_inv b hb0
            have h2 : mul (sq b) (inv b) = zero := by rw [h0, zero_mul]
            rw [sq_eq_mul_self, mul_assoc, h1, mul_one] at h2
            exact absurd h2 hb0
        subst hb
        exact hne rfl
      · -- Multiply norm = 0 by (inv a)^2 to get wp (b ⊗ inv a) = halfFermat, contradicting trace!
        have hainv := mul_inv a ha
        have hsqa : mul (sq a) (sq (inv a)) = one := by
          rw [← sq_mul, hainv, sq_one]
        let t := mul b (inv a)
        have hwp : wp t = halfFermat := by
          have hmul0 : mul (norm (.pair a b)) (sq (inv a)) = zero := by rw [h0, zero_mul]
          simp only [norm, mul_xor_l] at hmul0
          have hterm1 : mul (scaleH (sq a)) (sq (inv a)) = halfFermat := by
            rw [scaleH_eq, mul_comm (sq a) halfFermat, mul_assoc, hsqa, mul_one]
          have hterm2 : mul (mul a b) (sq (inv a)) = t := by
            rw [sq_eq_mul_self]
            have hr : mul (mul a b) (mul (inv a) (inv a)) = mul (mul a (inv a)) (mul b (inv a)) := by ac_rfl
            rw [hr, hainv, one_mul]
          have hterm3 : mul (sq b) (sq (inv a)) = sq t := by
            rw [← sq_mul]
          rw [hterm1, hterm2, hterm3] at hmul0
          -- halfFermat ⊕ t ⊕ sq t = 0 ⇒ sq t ⊕ t = halfFermat
          have hEq : xor halfFermat (wp t) = zero := by
            rw [wp]; rw [← hmul0]; ac_rfl
          exact (xor_eq_zero_iff.mp hEq).symm
        have htr : trace (wp t) = trace (halfFermat (k := k)) := congrArg trace hwp
        rw [trace_wp, trace_halfFermat] at htr
        cases htr
    have hd := mul_inv (norm (.pair a b)) hnorm
    have hinv_eq : inv (.pair a b) = mul (.pair a (xor a b)) (embed (inv (norm (.pair a b)))) := by
      simp [inv, embed, mul_pair, mul_zero, xor_zero, zero_xor, scaleH_zero]
    rw [hinv_eq, ← mul_assoc, mul_norm_conj, ← embed_mul, hd, embed_one]

theorem inv_mul {k : Nat} (x : Nim k) (h : x ≠ zero) : mul (inv x) x = one := by
  rw [mul_comm, mul_inv x h]

theorem mul_eq_zero_iff {k : Nat} {x y : Nim k} : mul x y = zero ↔ x = zero ∨ y = zero := by
  constructor
  · intro h
    by_cases hx : x = zero
    · exact Or.inl hx
    · right
      have h1 : mul (inv x) (mul x y) = zero := by rw [h, mul_zero]
      rw [← mul_assoc, inv_mul x hx, one_mul] at h1
      exact h1
  · rintro (rfl | rfl)
    · exact zero_mul y
    · exact mul_zero x

theorem inv_one {k : Nat} : inv (one : Nim k) = one := by
  have h := mul_inv (one : Nim k) one_ne_zero
  rwa [one_mul] at h

theorem inv_ne_zero {k : Nat} {x : Nim k} (h : x ≠ zero) : inv x ≠ zero := by
  intro hi
  have h1 := mul_inv x h
  rw [hi, mul_zero] at h1
  exact one_ne_zero h1.symm

theorem inv_unique {k : Nat} {x y : Nim k} (h : mul x y = one) : y = inv x := by
  have hx : x ≠ zero := by
    intro h0; rw [h0, zero_mul] at h; exact one_ne_zero h.symm
  calc y = mul one y := (one_mul y).symm
    _ = mul (mul (inv x) x) y := by rw [inv_mul x hx]
    _ = mul (inv x) (mul x y) := mul_assoc _ _ _
    _ = inv x := by rw [h, mul_one]

/-- Pure-silicon partial fraction identity in char 2:
    `1/u ⊕ 1/(u ⊕ 1) = 1/(u^2 ⊕ u)` whenever `u ≠ 0` and `u ≠ 1`. -/
theorem inv_xor_inv_xor_one {k : Nat} (u : Nim k) (hu0 : u ≠ zero) (hu1 : u ≠ one) :
    xor (inv u) (inv (xor u one)) = inv (wp u) := by
  have hu1' : xor u one ≠ zero := fun h => hu1 (xor_eq_zero_iff.mp h)
  have hwp : wp u = mul u (xor u one) := by
    rw [wp, sq_eq_mul_self, mul_xor_r, mul_one]
  apply inv_unique
  rw [hwp, mul_xor_r]
  have h1 : mul (mul u (xor u one)) (inv u) = xor u one := by
    have : mul (mul u (xor u one)) (inv u) = mul (mul u (inv u)) (xor u one) := by ac_rfl
    rw [this, mul_inv u hu0, one_mul]
  have h2 : mul (mul u (xor u one)) (inv (xor u one)) = u := by
    rw [mul_assoc, mul_inv (xor u one) hu1', mul_one]
  rw [h1, h2]
  have : xor (xor u one) u = xor (xor u u) one := by ac_rfl
  rw [this, xor_self, zero_xor]

/-! ### Frobenius Periodicity `Φ_k^(2^k) = id` & Trace-Sum Identity -/

/-- **Theorem B (Exact Artin-Schreier Bit-Length Contraction):**
    For every Fermat block `k` and every nonzero nimber `x ∈ Nim k`,
    applying `℘_k(x) = x^2 ⊕ x` drops `bitLen` by **exactly 1**. -/
theorem wp_bitLen_contraction : ∀ {k : Nat} (x : Nim k), x ≠ zero → bitLen (wp x) = bitLen x - 1
  | 0, .bit false, h => absurd rfl h
  | 0, .bit true, _  => rfl
  | k + 1, .pair a b, h => by
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have hwp : wp (.pair a b) = .pair (wp a) (xor (wp b) (scaleH (sq a))) := by
      simp only [wp, sq, xor]; congr 1; ac_rfl
    rw [hwp]
    by_cases ha : a = zero
    · subst ha
      have hb : b ≠ zero := fun hb0 => h (by rw [hb0]; rfl)
      simp only [wp_zero, sq_zero, scaleH_zero, xor_zero, bitLen, ↓reduceIte]
      exact wp_bitLen_contraction b hb
    · have ih_a := wp_bitLen_contraction a ha
      have hba : 1 ≤ bitLen a := Nat.pos_of_ne_zero (fun h0 => ha (bitLen_eq_zero_iff.mp h0))
      by_cases hwpa : wp a = zero
      · have hbl1 : bitLen a = 1 := by rw [hwpa, bitLen_zero] at ih_a; omega
        have ha1 : a = one := bitLen_eq_one_iff.mp hbl1
        subst ha1
        simp only [wp_one, sq_one, scaleH_eq, one_mul, bitLen, ↓reduceIte, one_ne_zero, bitLen_one]
        have htr : trace (xor (wp b) halfFermat) = true := by
          rw [trace_xor, trace_wp, trace_halfFermat]; rfl
        rw [bitLen_trace_true htr]
        omega
      · simp only [bitLen, ha, hwpa, ↓reduceIte, ih_a]
        omega

/-- Iterated bit-length contraction: `bitLen (℘^m x) = bitLen x - m`. -/
theorem wpIter_bitLen {k : Nat} (m : Nat) (x : Nim k) :
    bitLen (wpIter m x) = bitLen x - m := by
  induction m with
  | zero => simp [wpIter]
  | succ m ih =>
    rw [wpIter]
    by_cases h0 : wpIter m x = zero
    · rw [h0, wp_zero, bitLen_zero]
      rw [h0, bitLen_zero] at ih
      omega
    · rw [wp_bitLen_contraction _ h0, ih]; omega

/-- Exact kernel characterization: `℘^m(x) = 0 ↔ x < 2^m`. -/
theorem wpIter_eq_zero_iff {k : Nat} (m : Nat) (x : Nim k) :
    wpIter m x = zero ↔ x.toNat < 2 ^ m := by
  rw [← bitLen_eq_zero_iff, wpIter_bitLen, Nat.sub_eq_zero_iff_le, bitLen_le_iff]

/-- Exact unit evaluation on every dyadic boundary: `℘^m(2^m) = 1`. -/
theorem wpIter_pow2_eq_one {k : Nat} (m : Nat) (hm : m < 2 ^ k) :
    wpIter m (pow2 k m) = one := by
  rw [← bitLen_eq_one_iff, wpIter_bitLen, bitLen_pow2 k m hm]
  omega

/-! ## Section 4: Subspace Polynomials, Dyadic Wilson, Nim-Harmonic & Binary Power-Sum Collapse -/

/-- **Theorem C1 (Universal Dyadic Subspace-Polynomial Identity):**
    For ALL `k`, ALL `m ≤ 2^k` (not only powers of 2!), and ALL `X ∈ Nim k`:
    `⨂_{a < 2^m} (X ⊕ a) = ℘^m(X)`. -/
theorem dyadicProd_eq_wpIter (k m : Nat) (hm : m ≤ 2 ^ k) :
    ∀ X : Nim k, dyadicProd k m X = wpIter m X := by
  induction m with
  | zero =>
    intro X
    simp only [dyadicProd, Nat.pow_zero, prodRange, one_mul, wpIter]
    have h0 : ofNat k 0 = zero := by apply toNat_inj; rw [toNat_ofNat k 0 (Nat.pow_pos (by decide)), toNat_zero]
    rw [h0, xor_zero]
  | succ m ih =>
    intro X
    have hm_lt : m < 2 ^ k := hm
    have hm_le : m ≤ 2 ^ k := Nat.le_of_lt hm_lt
    unfold dyadicProd
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ, Nat.mul_two]
    rw [h2, prodRange_add]
    have hright : prodRange (2 ^ m) (fun i => xor X (ofNat k (2 ^ m + i))) =
                  dyadicProd k m (xor X (pow2 k m)) := by
      unfold dyadicProd
      apply prodRange_congr
      intro i hi
      rw [ofNat_pow2_add k m i hm_lt hi, ← xor_assoc]
    change mul (dyadicProd k m X) (prodRange (2 ^ m) (fun i => xor X (ofNat k (2 ^ m + i)))) = wpIter (m + 1) X
    rw [hright, ih hm_le X, ih hm_le (xor X (pow2 k m)),
        wpIter_xor, wpIter_pow2_eq_one m hm_lt]
    rw [wpIter, wp, sq_eq_mul_self, mul_xor_r, mul_one]

/-- **Theorem D1 (Dyadic-Shell Wilson's Theorem):**
    For ALL `k` and ALL `m < 2^k`, the nim-product of the entire dyadic shell
    `[2^m, 2^(m+1))` is identically `1`. -/
theorem dyadicShell_wilson (k m : Nat) (hm : m < 2 ^ k) :
    prodRange (2 ^ m) (fun a => ofNat k (2 ^ m + a)) = one := by
  have heq : prodRange (2 ^ m) (fun a => ofNat k (2 ^ m + a)) = dyadicProd k m (pow2 k m) := by
    unfold dyadicProd
    apply prodRange_congr
    intro a ha
    exact ofNat_pow2_add k m a hm ha
  rw [heq, dyadicProd_eq_wpIter k m (Nat.le_of_lt hm), wpIter_pow2_eq_one m hm]

/-- **Theorem D2 (Universal Coset Nim-Harmonic Law):**
    For ALL `k`, ALL `m ≤ 2^k`, and ALL `X ∈ Nim k` with `X.toNat ≥ 2^m`:
    `⨁_{a < 2^m} (X ⊕ a)^{-1} = (℘^m(X))^{-1}`. -/
theorem cosetHarmonic_eq_inv_wpIter (k m : Nat) (hm : m ≤ 2 ^ k) :
    ∀ X : Nim k, 2 ^ m ≤ X.toNat → cosetHarmonic k m X = inv (wpIter m X) := by
  induction m with
  | zero =>
    intro X _
    simp only [cosetHarmonic, Nat.pow_zero, xorSumRange, zero_xor, wpIter]
    have h0 : ofNat k 0 = zero := by
      apply toNat_inj; rw [toNat_ofNat k 0 (Nat.pow_pos (by decide)), toNat_zero]
    rw [h0, xor_zero]
  | succ m ih =>
    intro X hX
    have hm_lt : m < 2 ^ k := hm
    have hm_le : m ≤ 2 ^ k := Nat.le_of_lt hm_lt
    have hX_bl : m + 2 ≤ bitLen X := by
      by_cases hlt : bitLen X ≤ m + 1
      · have := (bitLen_le_iff X (m + 1)).mp hlt; omega
      · omega
    have hX_ge_m : 2 ^ m ≤ X.toNat := by
      have : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ m)
      omega
    have hXp_ge_m : 2 ^ m ≤ (xor X (pow2 k m)).toNat := by
      by_cases hlt : (xor X (pow2 k m)).toNat < 2 ^ m
      · have hbl : bitLen (xor X (pow2 k m)) ≤ m := (bitLen_le_iff _ m).mpr hlt
        have hX_eq : X = xor (xor X (pow2 k m)) (pow2 k m) := (xor_cancel_right X (pow2 k m)).symm
        have hle := bitLen_xor_le (xor X (pow2 k m)) (pow2 k m)
        rw [← hX_eq, bitLen_pow2 k m hm_lt] at hle
        omega
      · omega
    unfold cosetHarmonic
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ, Nat.mul_two]
    rw [h2, xorSumRange_add]
    have hright : xorSumRange (2 ^ m) (fun i => inv (xor X (ofNat k (2 ^ m + i)))) =
                  cosetHarmonic k m (xor X (pow2 k m)) := by
      unfold cosetHarmonic
      apply xorSumRange_congr
      intro i hi
      rw [ofNat_pow2_add k m i hm_lt hi, ← xor_assoc]
    change xor (cosetHarmonic k m X) (xorSumRange (2 ^ m) (fun i => inv (xor X (ofNat k (2 ^ m + i))))) =
           inv (wpIter (m + 1) X)
    rw [hright, ih hm_le X hX_ge_m, ih hm_le (xor X (pow2 k m)) hXp_ge_m,
        wpIter_xor, wpIter_pow2_eq_one m hm_lt]
    have hu_bl : 2 ≤ bitLen (wpIter m X) := by rw [wpIter_bitLen]; omega
    have hu0 : wpIter m X ≠ zero := by intro h0; rw [h0, bitLen_zero] at hu_bl; omega
    have hu1 : wpIter m X ≠ one := by intro h1; rw [h1, bitLen_one] at hu_bl; omega
    rw [inv_xor_inv_xor_one _ hu0 hu1, wpIter]

/-- **Theorem D3 (Dyadic-Shell Nim-Harmonic Invariance):**
    For ALL `k` and ALL `m < 2^k`, the nim-harmonic sum over the entire dyadic shell
    `[2^m, 2^(m+1))` is identically `1`. -/
theorem dyadicShell_harmonic (k m : Nat) (hm : m < 2 ^ k) :
    xorSumRange (2 ^ m) (fun a => inv (ofNat k (2 ^ m + a))) = one := by
  have heq : xorSumRange (2 ^ m) (fun a => inv (ofNat k (2 ^ m + a))) =
             cosetHarmonic k m (pow2 k m) := by
    unfold cosetHarmonic
    apply xorSumRange_congr
    intro a ha
    rw [ofNat_pow2_add k m a hm ha]
  have hge : 2 ^ m ≤ (pow2 k m).toNat := by rw [toNat_pow2 k m hm]; exact Nat.le_refl _
  rw [heq, cosetHarmonic_eq_inv_wpIter k m (Nat.le_of_lt hm) (pow2 k m) hge,
      wpIter_pow2_eq_one m hm, inv_one]

/-! ### Bit-Submask Pascal-Lucas Law & Sierpiński Frobenius Expansion -/

/-- **Theorem E1 (Sierpiński LFSR Recurrence for Power Sums):**
    For ALL `k`, ALL `m ≤ 2^k`, and ALL `d : Nat`:
    `⨁_{j ≤ m, j ⊆ m} S(m, d + 2^j) = 0`. -/
theorem powerSum_sierpinski_recurrence (k m d : Nat) (hm : m ≤ 2 ^ k) :
    xorSumRange (m + 1) (fun j => if submask j m then powerSum k m (d + 2 ^ j) else zero) = zero := by
  have h1 :
      xorSumRange (m + 1) (fun j => if submask j m then powerSum k m (d + 2 ^ j) else zero) =
      xorSumRange (m + 1) (fun j => xorSumRange (2 ^ m) (fun a => if submask j m then pow (ofNat k a) (d + 2 ^ j) else zero)) := by
    apply xorSumRange_congr; intro j _
    cases submask j m
    · simp [xorSumRange_zero]
    · rfl
  rw [h1, xorSumRange_swap]
  have hinner : ∀ a < 2 ^ m,
      xorSumRange (m + 1) (fun j => if submask j m then pow (ofNat k a) (d + 2 ^ j) else zero) = zero := by
    intro a ha
    have ha_lt : a < 2 ^ (2 ^ k) :=
      Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hm)
    have hfactor :
        xorSumRange (m + 1) (fun j => if submask j m then pow (ofNat k a) (d + 2 ^ j) else zero) =
        mul (pow (ofNat k a) d) (wpIter m (ofNat k a)) := by
      rw [wpIter_eq_sierpinski, xorSumRange_mul_left]
      apply xorSumRange_congr; intro j _
      cases submask j m
      · simp [mul_zero]
      · simp [pow_add, sqIter_eq_pow]
    rw [hfactor]
    have hker : wpIter m (ofNat k a) = zero := by
      rw [wpIter_eq_zero_iff, toNat_ofNat k a ha_lt]; exact ha
    rw [hker, mul_zero]
  rw [xorSumRange_congr (2 ^ m) hinner, xorSumRange_zero]

/-- **Theorem E3 (Exact Dyadic Boundary Power Sum):**
    For ALL `k` and ALL `m ≤ 2^k`: `S(m, 2^m - 1) = 1`. -/
theorem powerSum_boundary_one (k m : Nat) (hm : m ≤ 2 ^ k) :
    powerSum k m (2 ^ m - 1) = one := by
  induction m with
  | zero =>
    simp only [powerSum, Nat.pow_zero, Nat.sub_self, xorSumRange, pow_zero_val, zero_xor]
  | succ m ih =>
    have hm_lt : m < 2 ^ k := hm
    have hm_le : m ≤ 2 ^ k := Nat.le_of_lt hm_lt
    have hih := ih hm_le
    -- First evaluate S(m, 2^(m+1) - 1 - 2^j) for all j ≤ m using Sierpinski recurrence!
    have hval_j : ∀ j ≤ m, powerSum k m (2 ^ (m + 1) - 1 - 2 ^ j) = if submask j m then one else zero := by
      intro j hj
      by_cases hjm : j = m
      · rw [hjm]
        have hsub : 2 ^ (m + 1) - 1 - 2 ^ m = 2 ^ m - 1 := by rw [Nat.pow_succ, Nat.mul_two]; omega
        rw [hsub, hih, submask_self]; rfl
      · have hjlt : j < m := by omega
        have hrec := powerSum_sierpinski_recurrence k m (2 ^ m - 1 - 2 ^ j) hm_le
        simp only [xorSumRange, submask_self, ↓reduceIte] at hrec
        have hj1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
        have hjltm : 2 ^ j < 2 ^ m := Nat.pow_lt_pow_right (by decide) hjlt
        have hadd_eq : 2 ^ m - 1 - 2 ^ j + 2 ^ m = 2 ^ (m + 1) - 1 - 2 ^ j := by
          rw [Nat.pow_succ, Nat.mul_two]; omega
        rw [hadd_eq] at hrec
        have heq := xor_eq_zero_iff.mp hrec
        rw [← heq]
        rw [xorSumRange_single m j hjlt _ (fun t ht hne => by
          cases submask t m
          · rfl
          · simp only [↓reduceIte]
            exact powerSum_popcount_vanish k m hm_le _ (popcount_missing_bit_add_lt m j t hjlt ht hne))]
        have hback : 2 ^ m - 1 - 2 ^ j + 2 ^ j = 2 ^ m - 1 := by omega
        rw [hback, hih]
    -- Now expand S(m+1, 2^(m+1) - 1) via powerSum_succ:
    -- only r = 2^(m+1) - 1 - 2^j (with popcount r = m) survive!
    rw [powerSum_succ k m (2 ^ (m + 1) - 1) hm_lt]
    -- Rewrite sum over r < 2^(m+1) - 1 as sum over j ≤ m of r = (2^(m+1) - 1) - 2^j!
    -- Even cleaner: prove that for any r < 2^(m+1) - 1, either popcount r < m (so S(m, r) = 0),
    -- OR r = 2^(m+1) - 1 - 2^j for a unique j ≤ m!
    have hsplit :
        xorSumRange (2 ^ (m + 1) - 1) (fun r => if submask r (2 ^ (m + 1) - 1) then mul (pow (pow2 k m) (2 ^ (m + 1) - 1 - r)) (powerSum k m r) else zero) =
        xorSumRange (m + 1) (fun j => mul (pow (pow2 k m) (2 ^ j)) (powerSum k m (2 ^ (m + 1) - 1 - 2 ^ j))) := by
      -- Induct on n to peel off each j ∈ [0, m]:
      -- Actually, easier: show LHS ⊕ RHS = 0? No, just prove a general lemma on xorSumRange
      -- over `2^(m+1) - 1` when only elements `2^(m+1) - 1 - 2^j` (j ≤ m) are nonzero!
      -- Every r < 2^(m+1) - 1 with popcount r ≥ m has popcount r = m and is 2^(m+1) - 1 - 2^j!
      have hex_j : ∀ r < 2 ^ (m + 1) - 1, m ≤ popcount r → ∃ j ≤ m, r = 2 ^ (m + 1) - 1 - 2 ^ j := by
        intro r hr hpc
        -- Count how many bits in 0..m are 0 in r: since r < 2^(m+1) - 1, at least one bit j ≤ m is 0.
        -- Since popcount r ≥ m and all bits > m are 0, AT MOST one bit j ≤ m is 0!
        -- Prove by induction on m!
        have hgen : ∀ (n x : Nat), x < 2 ^ n - 1 → n - 1 ≤ popcount x → ∃ j < n, x = 2 ^ n - 1 - 2 ^ j := by
          intro n
          induction n with
          | zero => intro x hx; omega
          | succ n ihn =>
            intro x hx hpcx
            by_cases hx0 : x = 0
            · subst hx0
              rw [popcount_zero] at hpcx
              have hn0 : n = 0 := by omega
              subst hn0
              exact ⟨0, by decide, by decide⟩
            · rw [popcount_eq x hx0] at hpcx
              have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
              by_cases hmod : x % 2 = 0
              · -- Bit 0 is 0! So x / 2 must be 2^n - 1 (all other bits 1)!
                have hdle : x / 2 ≤ 2 ^ n - 1 := by omega
                by_cases hdeq : x / 2 = 2 ^ n - 1
                · refine ⟨0, Nat.succ_pos n, ?_⟩; omega
                · have := popcount_lt_of_lt_two_pow_sub_one n (x / 2) (by omega)
                  omega
              · -- Bit 0 is 1! So x / 2 < 2^n - 1 and popcount(x / 2) ≥ n - 1!
                have hmod1 : x % 2 = 1 := by omega
                have hdlt : x / 2 < 2 ^ n - 1 := by omega
                obtain ⟨j, hj, hjeq⟩ := ihn (x / 2) hdlt (by omega)
                refine ⟨j + 1, Nat.succ_lt_succ hj, ?_⟩
                have hpowj : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
                have hjlt : 2 ^ j < 2 ^ n := Nat.pow_lt_pow_right (by decide) hj
                omega
        obtain ⟨j, hj, hjeq⟩ := hgen (m + 1) r hr (by omega)
        exact ⟨j, by omega, hjeq⟩
      -- Now use a clean finite-subset extraction lemma:
      -- Define g(r) := if submask r (2^(m+1)-1) then ... else zero.
      -- For every j ≤ m, 2^(m+1) - 1 - 2^j < 2^(m+1) - 1 is strictly decreasing in j!
      let g : Nat → Nim k := fun r =>
        if submask r (2 ^ (m + 1) - 1) then mul (pow (pow2 k m) (2 ^ (m + 1) - 1 - r)) (powerSum k m r) else zero
      -- Note: for every r < 2^(m+1) - 1, submask r (2^(m+1) - 1) = true!
      have hsub_all : ∀ r < 2 ^ (m + 1) - 1, submask r (2 ^ (m + 1) - 1) = true := by
        intro r hr
        simp only [submask, beq_iff_eq]
        apply Nat.eq_of_testBit_eq; intro t
        rw [Nat.testBit_and]
        by_cases ht : t < m + 1
        · have h1 : (2 ^ (m + 1) - 1).testBit t = true := by
            rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true ht
          simp [h1]
        · have hr0 : r.testBit t = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega : r < 2 ^ (m + 1)) (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp ht)))
          simp [hr0]
      -- Extract the m+1 points `p j = 2^(m+1) - 1 - 2^j` from `xorSumRange (2^(m+1)-1) g` by induction on `n ≤ m + 1`:
      -- Let `mask n r := (∀ j < n, r ≠ 2^(m+1) - 1 - 2^j)`.
      have hextract : ∀ n ≤ m + 1,
          xorSumRange (2 ^ (m + 1) - 1) g =
          xor (xorSumRange n (fun j => g (2 ^ (m + 1) - 1 - 2 ^ j)))
              (xorSumRange (2 ^ (m + 1) - 1) (fun r => if ∀ j < n, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j then g r else zero)) := by
        intro n hn
        induction n with
        | zero => simp [xorSumRange, zero_xor]
        | succ n ihn =>
          rw [ihn (Nat.le_of_lt hn), xorSumRange, xor_assoc]
          congr 1
          -- Need: xorSumRange N (if ∀ j < n, ...) = xor (g (p n)) (xorSumRange N (if ∀ j < n+1, ...))
          have hpn_lt : 2 ^ (m + 1) - 1 - 2 ^ n < 2 ^ (m + 1) - 1 := by
            have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
            have : 2 ^ n < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) hn
            omega
          have hpn_fresh : ∀ j < n, 2 ^ (m + 1) - 1 - 2 ^ n ≠ 2 ^ (m + 1) - 1 - 2 ^ j := by
            intro j hj heq
            have h1 : 2 ^ j < 2 ^ n := Nat.pow_lt_pow_right (by decide) hj
            have h2 : 2 ^ n < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) hn
            omega
          have hdiff :
              xor (xorSumRange (2 ^ (m + 1) - 1) (fun r => if ∀ j < n, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j then g r else zero))
                  (xorSumRange (2 ^ (m + 1) - 1) (fun r => if ∀ j < n + 1, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j then g r else zero)) =
              g (2 ^ (m + 1) - 1 - 2 ^ n) := by
            rw [← xorSumRange_xor]
            rw [xorSumRange_single (2 ^ (m + 1) - 1) (2 ^ (m + 1) - 1 - 2 ^ n) hpn_lt]
            · have hnot : ¬ (∀ j < n + 1, 2 ^ (m + 1) - 1 - 2 ^ n ≠ 2 ^ (m + 1) - 1 - 2 ^ j) :=
                fun h => h n (Nat.lt_succ_self n) rfl
              split
              · exact xor_zero _
              · rename_i h1; exact absurd hpn_fresh h1
            · intro r _ hrne
              by_cases hprev : ∀ j < n, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j
              · have hnext : ∀ j < n + 1, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j := by
                  intro j hj
                  by_cases hjn : j = n
                  · subst hjn; exact hrne
                  · exact hprev j (by omega)
                split
                · exact xor_self _
                · rename_i h1; exact absurd hprev h1
              · have hnext : ¬ (∀ j < n + 1, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j) :=
                  fun h => hprev (fun j hj => h j (Nat.lt_succ_of_lt hj))
                split
                · rename_i h1; exact absurd h1 hprev
                · exact xor_zero _
          calc xorSumRange (2 ^ (m + 1) - 1) (fun r => if ∀ j < n, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j then g r else zero)
              = xor (xor (xorSumRange (2 ^ (m + 1) - 1) (fun r => if ∀ j < n, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j then g r else zero))
                         (xorSumRange (2 ^ (m + 1) - 1) (fun r => if ∀ j < n + 1, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j then g r else zero)))
                    (xorSumRange (2 ^ (m + 1) - 1) (fun r => if ∀ j < n + 1, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j then g r else zero)) :=
                (xor_cancel_right _ _).symm
            _ = xor (g (2 ^ (m + 1) - 1 - 2 ^ n))
                    (xorSumRange (2 ^ (m + 1) - 1) (fun r => if ∀ j < n + 1, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j then g r else zero)) := by
                rw [hdiff]
      have hres := hextract (m + 1) (Nat.le_refl _)
      have hrem : xorSumRange (2 ^ (m + 1) - 1) (fun r => if ∀ j < m + 1, r ≠ 2 ^ (m + 1) - 1 - 2 ^ j then g r else zero) = zero := by
        rw [xorSumRange_congr (2 ^ (m + 1) - 1) (g := fun _ => zero) (fun r hr => by
          split
          · rename_i hcond
            have hpc : popcount r < m := by
              by_cases hge : m ≤ popcount r
              · obtain ⟨j, hj, hjeq⟩ := hex_j r hr hge
                exact absurd hjeq (hcond j (by omega))
              · omega
            simp only [g, powerSum_popcount_vanish k m hm_le r hpc, mul_zero]
            split <;> rfl
          · rfl)]
        exact xorSumRange_zero _
      rw [hrem, xor_zero] at hres
      rw [hres]
      apply xorSumRange_congr; intro j hj
      have hlt : 2 ^ (m + 1) - 1 - 2 ^ j < 2 ^ (m + 1) - 1 := by
        have : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
        have : 2 ^ j < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) hj
        omega
      have hsub_back : 2 ^ (m + 1) - 1 - (2 ^ (m + 1) - 1 - 2 ^ j) = 2 ^ j := by
        have : 2 ^ j < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) hj
        omega
      simp only [g, hsub_all _ hlt, ↓reduceIte, hsub_back]
    rw [hsplit]
    have hwp_sum :
        xorSumRange (m + 1) (fun j => mul (pow (pow2 k m) (2 ^ j)) (powerSum k m (2 ^ (m + 1) - 1 - 2 ^ j))) =
        wpIter m (pow2 k m) := by
      rw [wpIter_eq_sierpinski]
      apply xorSumRange_congr; intro j hj
      rw [hval_j j (by omega), sqIter_eq_pow]
      cases submask j m <;> simp [mul_zero, mul_one]
    rw [hwp_sum, wpIter_pow2_eq_one m hm_lt]

/-- **Theorem E4 (Binary Power-Sum Collapse):**
    For ALL `k`, ALL `m ≤ 2^k` (even when `m` is NOT a power of 2, so `[0, 2^m)` is NOT a field!),
    and ALL exponents `d : Nat`:
    `⨁_{x < 2^m} x^d ∈ {0, 1}`. -/
theorem powerSum_binary_collapse (k m : Nat) (hm : m ≤ 2 ^ k) :
    ∀ d : Nat, powerSum k m d = zero ∨ powerSum k m d = one := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hlt : d < 2 ^ m - 1
    · exact Or.inl (powerSum_popcount_vanish k m hm d (popcount_lt_of_lt_two_pow_sub_one m d hlt))
    · by_cases heq : d = 2 ^ m - 1
      · subst heq; exact Or.inr (powerSum_boundary_one k m hm)
      · have hge : 2 ^ m ≤ d := by
          have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
          omega
        let d' := d - 2 ^ m
        have hrec := powerSum_sierpinski_recurrence k m d' hm
        simp only [xorSumRange, submask_self, ↓reduceIte] at hrec
        have hd_eq : d' + 2 ^ m = d := by omega
        rw [hd_eq] at hrec
        have hsum := xor_eq_zero_iff.mp hrec
        rw [← hsum]
        -- Any XOR-sum of elements in {zero, one} lies in {zero, one}!
        have hbin : ∀ n : Nat, (∀ j < n, (if submask j m then powerSum k m (d' + 2 ^ j) else zero) = zero ∨
                                          (if submask j m then powerSum k m (d' + 2 ^ j) else zero) = one) →
            xorSumRange n (fun j => if submask j m then powerSum k m (d' + 2 ^ j) else zero) = zero ∨
            xorSumRange n (fun j => if submask j m then powerSum k m (d' + 2 ^ j) else zero) = one := by
          intro n hn
          induction n with
          | zero => exact Or.inl rfl
          | succ n ihn =>
            have h1 := ihn (fun j hj => hn j (Nat.lt_succ_of_lt hj))
            have h2 := hn n (Nat.lt_succ_self n)
            simp only [xorSumRange]
            rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
            · rw [h1, h2, xor_zero]; exact Or.inl rfl
            · rw [h1, h2, zero_xor]; exact Or.inr rfl
            · rw [h1, h2, xor_zero]; exact Or.inr rfl
            · rw [h1, h2, xor_self]; exact Or.inl rfl
        apply hbin m
        intro j hj
        cases submask j m
        · exact Or.inl rfl
        · simp only [↓reduceIte]
          have hlt' : d' + 2 ^ j < d := by
            have : 2 ^ j < 2 ^ m := Nat.pow_lt_pow_right (by decide) hj
            omega
          exact ih (d' + 2 ^ j) hlt'

/-! ## Section 5: Universal Fermat-Block Shift-Defect Bound & Block-Periodicity Compiler -/

/-- Key Fermat-generator shift-defect lemma across all levels `n > k`:
    `bitLen (℘^(2^k)(F_n) ⊕ 2^(2^n - 2^k)) ≤ 2^n + 1 - 2 * 2^k`. -/
theorem wpIter_pow2_fermatGen_defect (k : Nat) :
    ∀ n : Nat, k < n →
      bitLen (xor (wpIter (2 ^ k) (fermatGen n)) (pow2 (n + 1) (2 ^ n - 2 ^ k))) ≤
        2 ^ n + 1 - 2 * 2 ^ k := by
  intro n hkn
  have hinner : ∀ m, k < m →
      bitLen (xor (frobSum (2 ^ k) (halfFermat (k := m))) (pow2 m (2 ^ m - 2 ^ k))) ≤
        2 ^ m + 1 - 2 * 2 ^ k := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro hkm
      by_cases hbase : m = k
      · subst hbase
        have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
        have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ, Nat.mul_two]
        have hsub : 2 ^ (m + 1) - 2 ^ m = 2 ^ m := by omega
        have hrhs : 2 ^ (m + 1) + 1 - 2 * 2 ^ m = 1 := by omega
        rw [hsub, hrhs, pow2_fermatGen]
        have hwp0 : wp (xor (frobSum (2 ^ m) (halfFermat (k := m + 1))) (fermatGen m)) = zero := by
          rw [wp_xor, wp_fermatGen]
          have hcomm : wp (wpIter (2 ^ m) (fermatGen (m + 1))) = wpIter (2 ^ m) (wp (fermatGen (m + 1))) := by
            change wpIter 1 (wpIter (2 ^ m) _) = wpIter (2 ^ m) (wpIter 1 _)
            exact wpIter_comm 1 (2 ^ m) _
          have h1 : embed (wp (frobSum (2 ^ m) (halfFermat (k := m + 1)))) =
                    wpIter (2 ^ m) (wp (fermatGen (m + 1))) := by
            rw [embed_wp, ← wpIter_pow2_fermatGen m (m + 1), hcomm]
          rw [wp_fermatGen, ← embed_wpIter] at h1
          have h2' := embed_inj h1
          rw [h2']
          change xor (wpIter (2 ^ m) (.pair (halfFermat (k := m)) zero)) (embed halfFermat) = zero
          rw [wpIter_pow2_pair, xor_self]
        have hbl := wpIter_bitLen 1 (xor (frobSum (2 ^ m) (halfFermat (k := m + 1))) (fermatGen m))
        simp only [wpIter, hwp0, bitLen_zero] at hbl
        omega
      · have hlt : k < m := by omega
        have hih := ih hlt
        have h2m : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ, Nat.mul_two]
        have hge2k : 2 * 2 ^ k ≤ 2 ^ m := by
          have : 2 ^ (k + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hlt
          rw [Nat.pow_succ, Nat.mul_comm] at this; exact this
        have hpow_split : pow2 (m + 1) (2 ^ (m + 1) - 2 ^ k) = .pair (pow2 m (2 ^ m - 2 ^ k)) zero := by
          have hnot : ¬ (2 ^ (m + 1) - 2 ^ k < 2 ^ m) := by omega
          have hsub : 2 ^ (m + 1) - 2 ^ k - 2 ^ m = 2 ^ m - 2 ^ k := by omega
          simp [pow2, hnot, hsub]
        rw [hpow_split]
        cases hf : frobSum (2 ^ k) (halfFermat (k := m + 1)) with
        | pair a b =>
          have ha : a = frobSum (2 ^ k) (halfFermat (k := m)) := by
            have := congrArg hi hf
            rw [hi_frobSum] at this
            exact this.symm
          rw [ha]
          simp only [xor, xor_zero, bitLen]
          split
          · have hb := bitLen_le b
            omega
          · omega
  have hlt : 2 ^ n - 2 ^ k < 2 ^ n := by
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have : 2 ^ k < 2 ^ n := Nat.pow_lt_pow_right (by decide) hkn
    omega
  rw [wpIter_pow2_fermatGen]
  simp only [pow2, hlt, ↓reduceIte]
  change bitLen (xor (embed (frobSum (2 ^ k) (halfFermat (k := n)))) (embed (pow2 n (2 ^ n - 2 ^ k)))) ≤ _
  rw [← embed_xor, bitLen_embed]
  exact hinner n hkn

/-- **Theorem F (Universal Fermat-Block Shift-Defect Bound):**
    For ALL blocks `n`, ALL shift scales `k`, and ALL `i` with `i + 2^k < 2^n`:
    - If `i < 2^k`, then `℘^(2^k)(2^(i + 2^k)) = 2^i` (exact right-shift!).
    - If `i ≥ 2^k`, then `bitLen (℘^(2^k)(2^(i + 2^k)) ⊕ 2^i) ≤ i + 1 - 2^k`
      (the top `2^k` bits match `2^i` identically; all `2^k - 1` bits below `i` vanish!). -/
theorem wpIter_pow2_shift_defect : ∀ (n k i : Nat), i + 2 ^ k < 2 ^ n →
    bitLen (xor (wpIter (2 ^ k) (pow2 n (i + 2 ^ k))) (pow2 n i)) ≤
      if i < 2 ^ k then 0 else i + 1 - 2 ^ k := by
  intro n
  induction n with
  | zero => intro k i h; have := Nat.one_le_pow k 2 (by decide); omega
  | succ n ih =>
    intro k i hlt
    have h2n : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ, Nat.mul_two]
    by_cases hlow : i + 2 ^ k < 2 ^ n
    · have hi_lt : i < 2 ^ n := by have := Nat.pow_pos (a := 2) (n := k) (by decide); omega
      simp only [pow2, hlow, hi_lt, ↓reduceIte]
      change bitLen (xor (wpIter (2 ^ k) (embed (pow2 n (i + 2 ^ k)))) (embed (pow2 n i))) ≤ _
      rw [← embed_wpIter, ← embed_xor, bitLen_embed]
      exact ih k i hlow
    · by_cases hnk : n = k
      · subst hnk
        have hi_lt : i < 2 ^ n := by omega
        have hsub : i + 2 ^ n - 2 ^ n = i := by omega
        simp only [pow2, hlow, hi_lt, ↓reduceIte, hsub]
        rw [wpIter_pow2_pair]
        change bitLen (xor (embed (pow2 n i)) (embed (pow2 n i))) ≤ _
        rw [xor_self, bitLen_zero]; omega
      · -- Here n > k and 2^n ≤ i + 2^k < 2^(n+1)
        have hkn : k < n := by
          by_cases hle : n < k
          · have : 2 ^ (n + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hle
            omega
          · omega
        have h2k_le_n : 2 * 2 ^ k ≤ 2 ^ n := by
          have : 2 ^ (k + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hkn
          rw [Nat.pow_succ, Nat.mul_comm] at this; exact this
        have hpow_nk : 2 ^ (n - k) * 2 ^ k = 2 ^ n := by
          rw [← Nat.pow_add]; congr 1; omega
        have hpow_nk1 : 2 ^ (n - (k + 1)) * 2 ^ (k + 1) = 2 ^ n := by
          rw [← Nat.pow_add]; congr 1; omega
        have hi_ge_2k : ¬ (i < 2 ^ k) := by omega
        simp only [hi_ge_2k, ↓reduceIte]
        let b := i + 2 ^ k - 2 ^ n
        have hb_lt : b < 2 ^ n := by omega
        have hdecomp : pow2 (n + 1) (i + 2 ^ k) = mul (fermatGen n) (embed (pow2 n b)) := by
          rw [mul_fermatGen_embed]
          simp only [pow2, hlow, ↓reduceIte]
          rfl
        rw [hdecomp, wpIter_pow2_mul]
        let eta := xor (wpIter (2 ^ k) (fermatGen n)) (pow2 (n + 1) (2 ^ n - 2 ^ k))
        have heta_bl : bitLen eta ≤ 2 ^ n + 1 - 2 * 2 ^ k := wpIter_pow2_fermatGen_defect k n hkn
        have hFn_eq : wpIter (2 ^ k) (fermatGen n) = xor (pow2 (n + 1) (2 ^ n - 2 ^ k)) eta := by
          simp only [eta]
          rw [xor_comm (wpIter (2 ^ k) (fermatGen n)), xor_cancel_left]
        by_cases hb1 : b < 2 ^ k
        · -- Case 1: b < 2^k
          have hwp_b : wpIter (2 ^ k) (embed (pow2 n b)) = zero := by
            rw [wpIter_eq_zero_iff, toNat_embed, toNat_pow2 n b hb_lt]
            exact Nat.pow_lt_pow_right (by decide) hb1
          have hsq_b : sqIter (2 ^ k) (embed (pow2 n b)) = pow2 (n + 1) b := by
            have : embed (pow2 n b) = pow2 (n + 1) b := by simp [pow2, hb_lt]; rfl
            rw [this]
            exact sqIter_pow2_pow2_of_lt (n + 1) k b hb1 (by omega)
          rw [hwp_b, mul_zero, zero_xor, hsq_b, hFn_eq, mul_xor_l]
          have hdisj_i : ((2 ^ n - 2 ^ k) &&& b) = 0 := by
            have hmult : 2 ^ n - 2 ^ k = (2 ^ (n - k) - 1) * 2 ^ k := by
              rw [Nat.sub_mul, Nat.one_mul, hpow_nk]
            apply Nat.eq_of_testBit_eq; intro t
            rw [Nat.testBit_and, Nat.zero_testBit]
            by_cases htk : t < k
            · rw [hmult, ← Nat.add_zero ((2 ^ (n - k) - 1) * 2 ^ k),
                  testBit_mul_two_pow_add k _ 0 t (Nat.pow_pos (by decide))]
              simp [htk]
            · have hb0 : b.testBit t = false :=
                Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb1 (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp htk)))
              simp [hb0]
          have hprod_i : mul (pow2 (n + 1) (2 ^ n - 2 ^ k)) (pow2 (n + 1) b) = pow2 (n + 1) i := by
            rw [mul_pow2_disjoint (n + 1) (2 ^ n - 2 ^ k) b (by omega) (by omega) hdisj_i]
            congr 1; omega
          rw [hprod_i]
          have hcancel : xor (xor (pow2 (n + 1) i) (mul eta (pow2 (n + 1) b))) (pow2 (n + 1) i) =
                         mul eta (pow2 (n + 1) b) := by
            rw [xor_comm (pow2 (n + 1) i), xor_cancel_right]
          rw [hcancel]
          apply bitLen_mul_pow2_le eta b (i + 1 - 2 ^ k) (by omega)
          intro u hu
          have hmult : 2 ^ n - 2 * 2 ^ k = (2 ^ (n - k) - 2) * 2 ^ k := by
            rw [Nat.sub_mul, hpow_nk]
          have hu_le : u ≤ (2 ^ (n - k) - 2) * 2 ^ k := by omega
          have hor := or_le_of_aligned (2 ^ (n - k) - 2) k b u hb1 hu_le
          omega
        · by_cases hb2 : b < 2 * 2 ^ k
          · -- Case 2: 2^k ≤ b < 2 * 2^k (works uniformly for all n ≥ k + 1!)
            let s := b - 2 ^ k
            have hs_lt : s < 2 ^ k := by omega
            have hb_eq : b = 2 ^ k + s := by omega
            have hwp_b : wpIter (2 ^ k) (embed (pow2 n b)) = embed (pow2 n s) := by
              rw [← embed_wpIter]
              congr 1
              have hdef := ih k s (by omega)
              have hs_if : s < 2 ^ k := hs_lt
              simp only [hs_if, ↓reduceIte] at hdef
              have h0 := bitLen_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hdef)
              have hEq := xor_eq_zero_iff.mp h0
              rwa [show s + 2 ^ k = b by omega] at hEq
            have hterm1 : mul (fermatGen n) (wpIter (2 ^ k) (embed (pow2 n b))) = pow2 (n + 1) i := by
              rw [hwp_b, mul_fermatGen_embed]
              have hnot : ¬ (i < 2 ^ n) := by omega
              have hsub : i - 2 ^ n = s := by omega
              simp [pow2, hnot, hsub]
            rw [hterm1]
            have hcancel : xor (xor (pow2 (n + 1) i) (mul (wpIter (2 ^ k) (fermatGen n)) (sqIter (2 ^ k) (embed (pow2 n b)))))
                               (pow2 (n + 1) i) =
                           mul (wpIter (2 ^ k) (fermatGen n)) (sqIter (2 ^ k) (embed (pow2 n b))) := by
              rw [xor_comm (pow2 (n + 1) i), xor_cancel_right]
            rw [hcancel]
            have hsq_b : sqIter (2 ^ k) (embed (pow2 n b)) =
                         xor (pow2 (n + 1) b) (pow2 (n + 1) s) := by
              have hem : embed (pow2 n b) = pow2 (n + 1) (2 ^ k + s) := by
                simp only [pow2, ← hb_eq, hb_lt, ↓reduceIte]; rfl
              rw [hem, sqIter_pow2_pow2_mid (n + 1) k s hs_lt (by omega), ← hb_eq]
            rw [hsq_b, hFn_eq, mul_xor_l, mul_xor_r, mul_xor_r]
            have h2k1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
            have hbound1 : bitLen (mul (pow2 (n + 1) (2 ^ n - 2 ^ k)) (pow2 (n + 1) b)) ≤ i + 1 - 2 ^ k := by
              rw [bitLen_mul_pow2 (n + 1) (2 ^ n - 2 ^ k) b (by omega) (by omega)]
              have hor_eq : ((2 ^ n - 2 ^ k) ||| b) = (2 ^ n - 2 ^ k) + s := by
                have h2n_eq : 2 ^ n - 2 ^ k = (2 ^ (n - (k + 1)) - 1) * 2 ^ (k + 1) + 2 ^ k := by
                  rw [Nat.sub_mul, Nat.one_mul, hpow_nk1]; omega
                apply Nat.eq_of_testBit_eq; intro t
                rw [Nat.testBit_or, h2n_eq,
                    testBit_mul_two_pow_add (k + 1) _ (2 ^ k) t (by omega),
                    Nat.add_assoc, testBit_mul_two_pow_add (k + 1) _ (2 ^ k + s) t (by omega)]
                split
                · rename_i hlt_t
                  have : ((2 ^ k).testBit t || b.testBit t) = (2 ^ k + s).testBit t := by
                    rw [hb_eq, ← Nat.testBit_or]
                    have hor_s : (2 ^ k ||| (2 ^ k + s)) = 2 ^ k + s := by
                      have := or_both_high k 0 s (Nat.pow_pos (by decide)) hs_lt
                      simpa using this
                    rw [hor_s]
                  exact this
                · rename_i hge_t
                  have hb0 : b.testBit t = false :=
                    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega : b < 2 ^ (k + 1))
                      (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp hge_t)))
                  simp [hb0]
              rw [hor_eq]; omega
            have hbound2 : bitLen (mul (pow2 (n + 1) (2 ^ n - 2 ^ k)) (pow2 (n + 1) s)) ≤ i + 1 - 2 ^ k := by
              rw [bitLen_mul_pow2 (n + 1) (2 ^ n - 2 ^ k) s (by omega) (by omega)]
              have hmult : 2 ^ n - 2 ^ k = (2 ^ (n - k) - 1) * 2 ^ k := by
                rw [Nat.sub_mul, Nat.one_mul, hpow_nk]
              have hor := or_le_of_aligned (2 ^ (n - k) - 1) k s (2 ^ n - 2 ^ k) hs_lt (by omega)
              omega
            have hbound3 : bitLen (mul eta (pow2 (n + 1) b)) ≤ i + 1 - 2 ^ k := by
              apply bitLen_mul_pow2_le eta b (i + 1 - 2 ^ k) (by omega)
              intro u hu
              have hmult : 2 ^ n - 2 * 2 ^ k = (2 ^ (n - (k + 1)) - 1) * 2 ^ (k + 1) := by
                rw [Nat.sub_mul, Nat.one_mul, hpow_nk1]; omega
              have hu_le : u ≤ (2 ^ (n - (k + 1)) - 1) * 2 ^ (k + 1) := by omega
              have hor := or_le_of_aligned (2 ^ (n - (k + 1)) - 1) (k + 1) b u (by omega) hu_le
              omega
            have hbound4 : bitLen (mul eta (pow2 (n + 1) s)) ≤ i + 1 - 2 ^ k := by
              apply bitLen_mul_pow2_le eta s (i + 1 - 2 ^ k) (by omega)
              intro u hu
              have hmult : 2 ^ n - 2 * 2 ^ k = (2 ^ (n - k) - 2) * 2 ^ k := by
                rw [Nat.sub_mul, hpow_nk]
              have hu_le : u ≤ (2 ^ (n - k) - 2) * 2 ^ k := by omega
              have hor := or_le_of_aligned (2 ^ (n - k) - 2) k s u hs_lt hu_le
              omega
            have h12 := bitLen_xor_le (mul (pow2 (n + 1) (2 ^ n - 2 ^ k)) (pow2 (n + 1) b))
                                      (mul (pow2 (n + 1) (2 ^ n - 2 ^ k)) (pow2 (n + 1) s))
            have h34 := bitLen_xor_le (mul eta (pow2 (n + 1) b)) (mul eta (pow2 (n + 1) s))
            exact Nat.le_trans (bitLen_xor_le _ _) (by omega)
          · -- Case 3: 2 * 2^k ≤ b (so i + 1 - 2^k ≥ 2^n!)
            have hb_ge : 2 * 2 ^ k ≤ b := by omega
            -- Term 1: fermatGen n ⊗ wpIter (2^k) (embed (pow2 n b))
            have hih_b := ih k (b - 2 ^ k) (by omega)
            have hnot_lt : ¬ (b - 2 ^ k < 2 ^ k) := by omega
            simp only [hnot_lt, ↓reduceIte, show b - 2 ^ k + 2 ^ k = b by omega] at hih_b
            let delta := xor (wpIter (2 ^ k) (pow2 n b)) (pow2 n (b - 2 ^ k))
            have hdelta_bl : bitLen delta ≤ b + 1 - 2 * 2 ^ k := by
              have : b - 2 ^ k + 1 - 2 ^ k = b + 1 - 2 * 2 ^ k := by omega
              rwa [this] at hih_b
            have hterm1_xor : xor (mul (fermatGen n) (wpIter (2 ^ k) (embed (pow2 n b)))) (pow2 (n + 1) i) =
                              .pair delta zero := by
              have hi_not : ¬ (i < 2 ^ n) := by omega
              have hi_sub : i - 2 ^ n = b - 2 ^ k := by omega
              rw [← embed_wpIter, mul_fermatGen_embed]
              simp only [pow2, hi_not, ↓reduceIte, hi_sub, xor, xor_zero]
              rfl
            have hterm1_bl : bitLen (xor (mul (fermatGen n) (wpIter (2 ^ k) (embed (pow2 n b)))) (pow2 (n + 1) i)) ≤
                             i + 1 - 2 ^ k := by
              rw [hterm1_xor, bitLen]
              split
              · rw [bitLen_zero]; omega
              · omega
            -- Term 2: wpIter (2^k) (fermatGen n) ⊗ sqIter (2^k) (embed (pow2 n b)) lives in embed (Nim n), so bitLen ≤ 2^n ≤ i + 1 - 2^k!
            have hterm2_bl : bitLen (mul (wpIter (2 ^ k) (fermatGen n)) (sqIter (2 ^ k) (embed (pow2 n b)))) ≤
                             i + 1 - 2 ^ k := by
              rw [wpIter_pow2_fermatGen, ← embed_sqIter, ← embed_mul, bitLen_embed]
              have := bitLen_le (mul (frobSum (2 ^ k) (halfFermat (k := n))) (sqIter (2 ^ k) (pow2 n b)))
              omega
            have hrearr :
                xor (xor (mul (fermatGen n) (wpIter (2 ^ k) (embed (pow2 n b))))
                         (mul (wpIter (2 ^ k) (fermatGen n)) (sqIter (2 ^ k) (embed (pow2 n b)))))
                    (pow2 (n + 1) i) =
                xor (xor (mul (fermatGen n) (wpIter (2 ^ k) (embed (pow2 n b)))) (pow2 (n + 1) i))
                    (mul (wpIter (2 ^ k) (fermatGen n)) (sqIter (2 ^ k) (embed (pow2 n b)))) := by ac_rfl
            rw [hrearr]
            exact Nat.le_trans (bitLen_xor_le _ _) (by omega)

/-! ### Theorem G: Universal Block-Periodicity & Finite-to-Infinite Compiler -/

/-- **Theorem G1 (Universal Artin-Schreier Block Periodicity across ALL Fermat Blocks):**
    For ALL `n, k, m, r : Nat` with `r < 2^k` and `m + 2^k + r < 2^n`:
    `℘^(m + 2^k)(2^(m + 2^k + r)) = ℘^m(2^(m + r))`. -/
theorem universal_wpIter_periodicity (n k m r : Nat) (hr : r < 2 ^ k) (hbound : m + 2 ^ k + r < 2 ^ n) :
    wpIter (m + 2 ^ k) (pow2 n (m + 2 ^ k + r)) = wpIter m (pow2 n (m + r)) := by
  have hdef := wpIter_pow2_shift_defect n k (m + r) (by omega)
  have hbl_le_m : bitLen (xor (wpIter (2 ^ k) (pow2 n (m + 2 ^ k + r))) (pow2 n (m + r))) ≤ m := by
    rw [show m + 2 ^ k + r = m + r + 2 ^ k by omega]
    split at hdef <;> omega
  have hkill : wpIter m (xor (wpIter (2 ^ k) (pow2 n (m + 2 ^ k + r))) (pow2 n (m + r))) = zero := by
    rw [← bitLen_eq_zero_iff, wpIter_bitLen]; omega
  rw [wpIter_xor, ← wpIter_add] at hkill
  exact xor_eq_zero_iff.mp hkill

/-- **Theorem G2 (Universal Dyadic-Coset Nim-Product Periodicity across ALL Fermat Blocks):**
    For ALL `n, k, m, r` with `r < 2^k` and `m + 2^k + r < 2^n`:
    `⨂_{a < 2^(m + 2^k)} (2^(m + 2^k + r) ⊕ a) = ⨂_{a < 2^m} (2^(m + r) ⊕ a)`. -/
theorem universal_dyadicProd_periodicity (n k m r : Nat) (hr : r < 2 ^ k) (hbound : m + 2 ^ k + r < 2 ^ n) :
    dyadicProd n (m + 2 ^ k) (pow2 n (m + 2 ^ k + r)) = dyadicProd n m (pow2 n (m + r)) := by
  rw [dyadicProd_eq_wpIter n (m + 2 ^ k) (by omega),
      dyadicProd_eq_wpIter n m (by omega)]
  exact universal_wpIter_periodicity n k m r hr hbound

/-- **Theorem G3 (Universal Coset Nim-Harmonic Periodicity across ALL Fermat Blocks):**
    For ALL `n, k, m, r` with `r < 2^k` and `m + 2^k + r < 2^n`:
    `⨁_{a < 2^(m + 2^k)} (2^(m + 2^k + r) ⊕ a)^{-1} = ⨁_{a < 2^m} (2^(m + r) ⊕ a)^{-1}`. -/
theorem universal_cosetHarmonic_periodicity (n k m r : Nat) (hr : r < 2 ^ k) (hbound : m + 2 ^ k + r < 2 ^ n) :
    cosetHarmonic n (m + 2 ^ k) (pow2 n (m + 2 ^ k + r)) = cosetHarmonic n m (pow2 n (m + r)) := by
  have hge1 : 2 ^ (m + 2 ^ k) ≤ (pow2 n (m + 2 ^ k + r)).toNat := by
    rw [toNat_pow2 n (m + 2 ^ k + r) hbound]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hge2 : 2 ^ m ≤ (pow2 n (m + r)).toNat := by
    rw [toNat_pow2 n (m + r) (by omega)]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  rw [cosetHarmonic_eq_inv_wpIter n (m + 2 ^ k) (by omega) _ hge1,
      cosetHarmonic_eq_inv_wpIter n m (by omega) _ hge2,
      universal_wpIter_periodicity n k m r hr hbound]

/-- **Theorem G4 (Finite-to-Infinite Evaluation Compiler):**
    For ANY `k, m, r, n` with `r < 2^k` and `m + r < 2^n`, the exponentially large
    `2^m`-term dyadic-coset nim-product `⨂_{a < 2^m} (2^(m + r) ⊕ a)` is **identically equal**
    to a single finite-table lookup at `m % 2^k` inside the fixed finite block `Nim (k + 1)`! -/
theorem finite_table_evaluates_all_m (k m r n : Nat) (hr : r < 2 ^ k) (hbound : m + r < 2 ^ n) :
    (dyadicProd n m (pow2 n (m + r))).toNat =
      (wpIter (m % 2 ^ k) (pow2 (k + 1) (m % 2 ^ k + r))).toNat := by
  rw [dyadicProd_eq_wpIter n m (by omega)]
  have hper : ∀ m', m' + r < 2 ^ n →
      (wpIter m' (pow2 n (m' + r))).toNat = (wpIter (m' % 2 ^ k) (pow2 n (m' % 2 ^ k + r))).toNat := by
    intro m'
    induction m' using Nat.strongRecOn with
    | ind m' ih =>
      intro hlt
      by_cases hsmall : m' < 2 ^ k
      · rw [Nat.mod_eq_of_lt hsmall]
      · have hge : 2 ^ k ≤ m' := Nat.not_lt.mp hsmall
        have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
        let m0 := m' - 2 ^ k
        have hm'_eq : m' = m0 + 2 ^ k := by omega
        have hstep := universal_wpIter_periodicity n k m0 r hr (by omega)
        rw [hm'_eq]
        have hmod_eq : (m0 + 2 ^ k) % 2 ^ k = m0 % 2 ^ k := Nat.add_mod_right m0 (2 ^ k)
        rw [hstep, hmod_eq]
        exact ih m0 (by omega) (by omega)
  rw [hper m hbound]
  have hmod_le : m % 2 ^ k ≤ m := Nat.mod_le m (2 ^ k)
  have hmod_lt : m % 2 ^ k < 2 ^ k := Nat.mod_lt m (Nat.pow_pos (by decide))
  have h2k1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
  exact toNat_wpIter_pow2_level_indep n (k + 1) (m % 2 ^ k) (m % 2 ^ k + r) (by omega) (by omega)

/-- **Theorem G5 (Universal Linearized Prefix Periodicity for Arbitrary `2^k`-bit Headers `y`):**
    For ANY `2^k`-bit prefix `y < 2^(2^k)` (not just single powers of 2!),
    `℘^(m + 2^k)(y ≪ (m + 2^k)) = ℘^m(y ≪ m)` across ALL Fermat blocks `2^(2^n)`. -/
theorem universal_prefix_periodicity (n k m y : Nat) (hy : y < 2 ^ (2 ^ k))
    (hbound : m + 2 ^ k + 2 ^ k ≤ 2 ^ n) :
    wpIter (m + 2 ^ k) (ofNat n (y * 2 ^ (m + 2 ^ k))) =
      wpIter m (ofNat n (y * 2 ^ m)) := by
  -- Decompose ofNat n (y * 2^s) as xorSumRange (2^k) (fun r => if y.testBit r then pow2 n (s + r) else zero)!
  have hshift_decomp : ∀ s, s + 2 ^ k ≤ 2 ^ n →
      ofNat n (y * 2 ^ s) = xorSumRange (2 ^ k) (fun r => if y.testBit r then pow2 n (s + r) else zero) := by
    intro s hs
    have hlt_n : y * 2 ^ s < 2 ^ (2 ^ n) := by
      have h1 : y * 2 ^ s < 2 ^ (2 ^ k) * 2 ^ s := Nat.mul_lt_mul_of_pos_right hy (Nat.pow_pos (by decide))
      have h2 : 2 ^ (2 ^ k) * 2 ^ s = 2 ^ (2 ^ k + s) := (Nat.pow_add 2 (2 ^ k) s).symm
      have h3 : 2 ^ (2 ^ k + s) ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    apply toNat_inj
    rw [toNat_ofNat n (y * 2 ^ s) hlt_n]
    apply Nat.eq_of_testBit_eq; intro t
    -- Compute testBit of the shifted xorSumRange by induction on `c ≤ 2^k`
    have htb : ∀ c ≤ 2 ^ k,
        (xorSumRange c (fun r => if y.testBit r then pow2 n (s + r) else zero)).toNat.testBit t =
        (decide (s ≤ t) && decide (t < s + c) && y.testBit (t - s)) := by
      intro c hc
      induction c with
      | zero =>
        simp only [xorSumRange, toNat_zero, Nat.zero_testBit, Nat.add_zero]
        by_cases hst : s ≤ t <;> by_cases hlt : t < s <;> simp [hst, hlt] <;> omega
      | succ c ihc =>
        simp only [xorSumRange, toNat_xor, Nat.testBit_xor, ihc (Nat.le_of_lt hc)]
        by_cases hteq : t = s + c
        · subst hteq
          have h1 : s ≤ s + c := by omega
          have h2 : ¬ (s + c < s + c) := Nat.lt_irrefl _
          have h3 : s + c < s + (c + 1) := by omega
          have h4 : s + c - s = c := by omega
          simp only [h1, h2, h3, h4, decide_true, decide_false, Bool.true_and, Bool.and_false, Bool.false_and, Bool.false_xor]
          cases hbit : y.testBit c
          · simp [toNat_zero]
          · simp only [↓reduceIte]
            rw [toNat_pow2 n (s + c) (by omega), Nat.testBit_two_pow_self]
        · have hright0 : (if y.testBit c then pow2 n (s + c) else zero).toNat.testBit t = false := by
            cases y.testBit c
            · simp [toNat_zero]
            · simp only [↓reduceIte]
              rw [toNat_pow2 n (s + c) (by omega), Nat.testBit_two_pow]
              have hne : s + c ≠ t := fun h => hteq h.symm
              simp [hne]
          rw [hright0, Bool.xor_false]
          have hiff : (t < s + c) ↔ (t < s + (c + 1)) := by omega
          simp [hiff]
    rw [htb (2 ^ k) (Nat.le_refl _)]
    rw [← Nat.add_zero (y * 2 ^ s), testBit_mul_two_pow_add s y 0 t (Nat.pow_pos (by decide))]
    by_cases hts : t < s
    · have hns : ¬ (s ≤ t) := by omega
      simp [hts, hns]
    · have hsle : s ≤ t := by omega
      simp only [hts, ↓reduceIte, hsle, decide_true, Bool.true_and]
      by_cases hlt2 : t < s + 2 ^ k
      · simp [hlt2]
      · simp only [hlt2, decide_false, Bool.false_and]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))
  have hwp_sum : ∀ {p : Nat} (c : Nat) (f : Nat → Nim n),
      wpIter p (xorSumRange c f) = xorSumRange c (fun r => wpIter p (f r)) := by
    intro p c f
    induction c with
    | zero => simp [xorSumRange, wpIter_zero_x]
    | succ c ihc => simp [xorSumRange, wpIter_xor, ihc]
  rw [hshift_decomp (m + 2 ^ k) (by omega), hshift_decomp m (by have := Nat.pow_pos (a := 2) (n := k) (by decide); omega), hwp_sum, hwp_sum]
  apply xorSumRange_congr; intro r hr
  cases y.testBit r
  · simp [wpIter_zero_x]
  · simp only [↓reduceIte]
    exact universal_wpIter_periodicity n k m r hr (by omega)

/-! ### Concrete Infinite Corollaries across ALL `n, m` -/

/-- For ALL blocks `n` and ALL `m` with `m + 1 < 2^n`, the second-shell coset nim-product
    `⨂_{a < 2^m} (2^(m+1) ⊕ a)` is **identically 2** (period 1!). -/
theorem dyadicProd_second_shell_eq_two (n m : Nat) (h : m + 1 < 2 ^ n) :
    (dyadicProd n m (pow2 n (m + 1))).toNat = 2 := by
  have hcomp := finite_table_evaluates_all_m 1 m 1 n (by decide) h
  rw [hcomp]
  have hmod : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hmod with hm | hm <;> rw [hm] <;> decide

/-- For ALL blocks `n` and ALL `m` with `m + 1 < 2^n`, the second-shell coset nim-harmonic sum
    `⨁_{a < 2^m} (2^(m+1) ⊕ a)^{-1}` is **identically 3**! -/
theorem cosetHarmonic_second_shell_eq_three (n m : Nat) (h : m + 1 < 2 ^ n) :
    (cosetHarmonic n m (pow2 n (m + 1))).toNat = 3 := by
  have hge : 2 ^ m ≤ (pow2 n (m + 1)).toNat := by
    rw [toNat_pow2 n (m + 1) h]; exact Nat.pow_le_pow_right (by decide) (Nat.le_succ m)
  rw [cosetHarmonic_eq_inv_wpIter n m (by omega) _ hge]
  have h2 : (wpIter m (pow2 n (m + 1))).toNat = 2 := by
    have := dyadicProd_second_shell_eq_two n m h
    rwa [dyadicProd_eq_wpIter n m (by omega)] at this
  have hn1 : 1 ≤ n := by
    cases n with
    | zero => omega
    | succ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  have hlt3 : 3 < 2 ^ (2 ^ n) := by
    have h2n : 2 ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (n := 2) (by decide) hn1; simpa using this
    have : 2 ^ 2 ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by decide) h2n
    omega
  have hwp_eq : wpIter m (pow2 n (m + 1)) = ofNat n 2 := by
    apply toNat_inj; rw [h2, toNat_ofNat n 2 (by omega)]
  have hmul23 : mul (ofNat n 2) (ofNat n 3) = one := by
    have hstep : ∀ d, mul (ofNat (d + 1) 2) (ofNat (d + 1) 3) = one := by
      intro d
      induction d with
      | zero => decide
      | succ d ihd =>
        have hpow : 4 ≤ 2 ^ (2 ^ (d + 1)) := by
          have h1 : 2 ≤ 2 ^ (d + 1) := by
            have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.succ_le_succ (Nat.zero_le d)); simpa using this
          exact Nat.pow_le_pow_right (n := 2) (by decide) h1
        have hpow2 : 4 ≤ 2 ^ (2 ^ (d + 2)) := by
          have h1 : 2 ≤ 2 ^ (d + 2) := by
            have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.succ_le_succ (Nat.zero_le (d + 1))); simpa using this
          exact Nat.pow_le_pow_right (n := 2) (by decide) h1
        have h2e : ofNat (d + 2) 2 = embed (ofNat (d + 1) 2) := by
          apply toNat_inj
          rw [toNat_embed, toNat_ofNat _ 2 (by omega), toNat_ofNat _ 2 (by omega)]
        have h3e : ofNat (d + 2) 3 = embed (ofNat (d + 1) 3) := by
          apply toNat_inj
          rw [toNat_embed, toNat_ofNat _ 3 (by omega), toNat_ofNat _ 3 (by omega)]
        rw [h2e, h3e, ← embed_mul, ihd, embed_one]
    cases n with
    | zero => omega
    | succ d => exact hstep d
  rw [hwp_eq, ← inv_unique hmul23, toNat_ofNat n 3 hlt3]

/-- For ALL blocks `n` and ALL `m` with `m + 2 < 2^n`, the third-shell coset nim-product
    `⨂_{a < 2^m} (2^(m+2) ⊕ a)` cycles with **exact period 4** through `[4, 5, 5, 4]`. -/
theorem dyadicProd_third_shell_period4 (n m : Nat) (h : m + 2 < 2 ^ n) :
    (dyadicProd n m (pow2 n (m + 2))).toNat =
      match m % 4 with
      | 0 => 4
      | 1 => 5
      | 2 => 5
      | _ => 4 := by
  have hcomp := finite_table_evaluates_all_m 2 m 2 n (by decide) h
  rw [hcomp]
  have hmod : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases hmod with hm | hm | hm | hm <;> rw [hm] <;> decide

/-- For ALL blocks `n` and ALL `m` with `m + 3 < 2^n`, the fourth-shell coset nim-product
    `⨂_{a < 2^m} (2^(m+3) ⊕ a)` cycles with **exact period 4** through `[8, 8, 10, 11]`. -/
theorem dyadicProd_fourth_shell_period4 (n m : Nat) (h : m + 3 < 2 ^ n) :
    (dyadicProd n m (pow2 n (m + 3))).toNat =
      match m % 4 with
      | 0 => 8
      | 1 => 8
      | 2 => 10
      | _ => 11 := by
  have hcomp := finite_table_evaluates_all_m 2 m 3 n (by decide) h
  rw [hcomp]
  have hmod : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases hmod with hm | hm | hm | hm <;> rw [hm] <;> decide

/-! ## Section 6: Conway `mex` Exact Verification, Non-Vacuity Witnesses, Sharpness & Axioms -/

/-- Kernel-checked exact agreement between our pure-silicon Fermat-tower engine `Nim.mul`
    and Conway's recursive `mex` definition on `[0, 8) × [0, 8)` (64 pairs, crossing Fermat
    blocks `F_0 = 2` and `F_1 = 4` into `F_2 = 16`). Full `16 × 16` (256/256) is also
    verified in `explore_and_verify.py`. -/
theorem nim_mul_agrees_with_conway_mex_8x8 :
    let tbl := buildMexTable 8
    (List.range 8).all (fun a =>
      (List.range 8).all (fun b =>
        (mul (ofNat 2 a) (ofNat 2 b)).toNat == (tbl.getD a []).getD b 0)) = true := by
  decide

/-! ### Kernel-Checked Non-Vacuity Witnesses (Every Universal Hypothesis Genuinely Inhabited) -/

/-- Non-vacuity witness for the Fermat-tower field axioms + inverse on `Nim 3` (`F_256`). -/
theorem witness_field_nonvacuous :
    Nonempty { p : Nim 3 × Nim 3 // p.1 ≠ zero ∧ mul p.1 (inv p.1) = one ∧ toNat (mul p.1 p.2) ≠ 0 } :=
  ⟨⟨(ofNat 3 137, ofNat 3 211), by decide, mul_inv (ofNat 3 137) (by decide), by decide⟩⟩

/-- Non-vacuity witness for Theorem G4 (Finite-to-Infinite Compiler) instantiated at
    `k = 2, r = 3, m = 10` (product of `2^10 = 1024` nimbers inside `F_{2^16} = Nim 4`!). -/
theorem witness_compiler_nonvacuous :
    Nonempty { t : Nat × Nat × Nat × Nat //
      t.2.2.1 < 2 ^ t.1 ∧ t.2.1 + t.2.2.1 < 2 ^ t.2.2.2 ∧
      (wpIter t.2.1 (pow2 t.2.2.2 (t.2.1 + t.2.2.1))).toNat = 10 } :=
  ⟨⟨(2, 10, 3, 4), by decide, by decide, by
    have h := finite_table_evaluates_all_m 2 10 3 4 (by decide) (by decide)
    rw [dyadicProd_eq_wpIter 4 10 (by decide)] at h
    rw [h]; decide⟩⟩

/-- Non-vacuity witness for Theorem E4 (Binary Power-Sum Collapse) on a non-field dyadic
    block `m = 3` (`[0, 8)` inside `Nim 2 = F_16`, where `m` is NOT a power of 2!),
    proved purely algebraically via our Sierpiński recurrence at `d = 11`! -/
theorem witness_nonfield_powerSum_nonvacuous :
    Nonempty { d : Nat // powerSum 2 3 d = one ∧ d = 11 } := by
  refine ⟨⟨11, ?_, rfl⟩⟩
  have hrec := powerSum_sierpinski_recurrence 2 3 3 (by decide)
  have h4 : powerSum 2 3 4 = zero :=
    powerSum_popcount_vanish 2 3 (by decide) 4 (popcount_lt_of_lt_two_pow_sub_one 3 4 (by decide))
  have h5 : powerSum 2 3 5 = zero :=
    powerSum_popcount_vanish 2 3 (by decide) 5 (popcount_lt_of_lt_two_pow_sub_one 3 5 (by decide))
  have h7 : powerSum 2 3 7 = one := powerSum_boundary_one 2 3 (by decide)
  have s0 : submask 0 3 = true := rfl
  have s1 : submask 1 3 = true := rfl
  have s2 : submask 2 3 = true := rfl
  have s3 : submask 3 3 = true := rfl
  simp only [xorSumRange, s0, s1, s2, s3, ↓reduceIte, zero_xor] at hrec
  change xor (xor (xor (powerSum 2 3 4) (powerSum 2 3 5)) (powerSum 2 3 7)) (powerSum 2 3 11) = zero at hrec
  rw [h4, h5, h7, zero_xor, zero_xor] at hrec
  exact (xor_eq_zero_iff.mp hrec).symm

/-- Concrete kernel-checked examples across blocks `Nim 2`, `Nim 3`, `Nim 4`. -/
example : (dyadicProd 3 5 (pow2 3 6)).toNat = 2 := dyadicProd_second_shell_eq_two 3 5 (by decide)
example : (cosetHarmonic 3 5 (pow2 3 6)).toNat = 3 := cosetHarmonic_second_shell_eq_three 3 5 (by decide)
example : (dyadicProd 4 10 (pow2 4 12)).toNat = 5 := dyadicProd_third_shell_period4 4 10 (by decide)
example : (dyadicProd 4 11 (pow2 4 14)).toNat = 11 := dyadicProd_fourth_shell_period4 4 11 (by decide)
example : prodRange (2 ^ 3) (fun a => ofNat 2 (2 ^ 3 + a)) = one := dyadicShell_wilson 2 3 (by decide)
example : xorSumRange (2 ^ 3) (fun a => inv (ofNat 2 (2 ^ 3 + a))) = one := dyadicShell_harmonic 2 3 (by decide)

/-! ### Kernel-Checked Sharpness & Falsification Counterexamples -/

/-- **Sharpness 1a:** Period `2^k` in Theorem G1/G2 FAILS at the exact boundary `r = 2^k` for `k = 1`
    (`r = 2`: `f_2(0) = 4 ≠ 5 = f_2(2)`). -/
theorem sharpness_period_fails_at_k1_r2 :
    wpIter (0 + 2 ^ 1) (pow2 3 (0 + 2 ^ 1 + 2)) ≠ wpIter 0 (pow2 3 (0 + 2)) := by
  decide

/-- Helper reducing `wpIter 4 (pow2 4 8)` inside `Nim 4` down to `Nim 3` for fast kernel check. -/
private theorem wpIter_4_pow2_4_8_eq :
    wpIter (2 ^ 2) (pow2 4 8) = embed (frobSum 4 (halfFermat (k := 3))) := by
  have hF : pow2 4 8 = fermatGen 3 := pow2_fermatGen 3
  rw [hF, wpIter_pow2_fermatGen]

/-- **Sharpness 1b:** Period `2^k` in Theorem G1/G2 FAILS at the exact boundary `r = 2^k` for `k = 2`
    (`r = 4`: `f_4(0) = 16 ≠ 17 = f_4(4)`). -/
theorem sharpness_period_fails_at_k2_r4 :
    wpIter (0 + 2 ^ 2) (pow2 4 (0 + 2 ^ 2 + 4)) ≠ wpIter 0 (pow2 4 (0 + 4)) := by
  change wpIter (2 ^ 2) (pow2 4 8) ≠ pow2 4 4
  rw [wpIter_4_pow2_4_8_eq]
  have hp : pow2 4 4 = embed (pow2 3 4) := rfl
  rw [hp]
  intro h
  have h3 := embed_inj h
  have hne : frobSum 4 (halfFermat (k := 3)) ≠ pow2 3 4 := by decide
  exact hne h3

/-- **Sharpness 2:** The shift-defect bound `bitLen ≤ i + 1 - 2^k` in Theorem F is **razor-sharp**
    (zero slack) at both `k = 1, i = 2` and `k = 2, i = 4` (tightening by 1 fails!). -/
theorem sharpness_shift_defect_tight :
    bitLen (xor (wpIter (2 ^ 1) (pow2 3 (2 + 2 ^ 1))) (pow2 3 2)) = 2 + 1 - 2 ^ 1 ∧
    bitLen (xor (wpIter (2 ^ 2) (pow2 4 (4 + 2 ^ 2))) (pow2 4 4)) = 4 + 1 - 2 ^ 2 := by
  constructor
  · decide
  · change bitLen (xor (wpIter (2 ^ 2) (pow2 4 8)) (pow2 4 4)) = 1
    rw [wpIter_4_pow2_4_8_eq]
    have hp : pow2 4 4 = embed (pow2 3 4) := rfl
    rw [hp, ← embed_xor, bitLen_embed]
    decide

/-- **Sharpness 3:** Binary Power-Sum Collapse (Theorem E4) FAILS on non-power-of-2 prefixes:
    for `L = 3, d = 1`, `⨁_{x < 3} x = 3 ∉ {0, 1}`; for `L = 5, d = 3`, `⨁_{x < 5} x^3 = 15 ∉ {0, 1}`. -/
theorem sharpness_powerSum_collapse_fails_non_dyadic :
    let s3 := xorSumRange 3 (fun a => pow (ofNat 2 a) 1)
    let s5 := xorSumRange 5 (fun a => pow (ofNat 2 a) 3)
    s3 ≠ zero ∧ s3 ≠ one ∧ s5 ≠ zero ∧ s5 ≠ one := by
  decide

/-- **Sharpness 4:** Dyadic-Shell Wilson (`= 1`) and Harmonic Invariance (`= 1`) FAIL on the
    very next coset `c = 2` (`[2 * 2^m, 3 * 2^m)`) for EVERY `n, m` with `m + 1 < 2^n`! -/
theorem sharpness_second_shell_ne_one (n m : Nat) (h : m + 1 < 2 ^ n) :
    dyadicProd n m (pow2 n (m + 1)) ≠ one ∧ cosetHarmonic n m (pow2 n (m + 1)) ≠ one := by
  constructor
  · intro h1
    have h2 := dyadicProd_second_shell_eq_two n m h
    rw [h1, toNat_one] at h2; omega
  · intro h1
    have h3 := cosetHarmonic_second_shell_eq_three n m h
    rw [h1, toNat_one] at h3; omega

/-- **Sharpness 5:** Popcount Annihilation (`popcount d < m → S(m, d) = 0`, Theorem E2) FAILS
    at the exact boundary `popcount d = m` (`d = 2^m - 1`) for EVERY `k, m ≤ 2^k`! -/
theorem sharpness_popcount_boundary_nonzero (k m : Nat) (hm : m ≤ 2 ^ k) :
    popcount (2 ^ m - 1) = m ∧ powerSum k m (2 ^ m - 1) ≠ zero := by
  refine ⟨popcount_two_pow_sub_one m, ?_⟩
  rw [powerSum_boundary_one k m hm]
  exact one_ne_zero

end Nim
end ConwaySilicon
