import MinkowskiRaneySingularityEngine.Defs

namespace RaneyMinkowski
namespace RatQ
end RatQ
open RatQ

-- =============================================================================
-- SECTION 2: Exact 2x2 Natural Matrices & Stern-Brocot Tree
-- =============================================================================

namespace Mat2
end Mat2
open Mat2

-- =============================================================================
-- SECTION 3: Exact Binary Stern-Brocot & Minkowski Question-Mark Function
-- =============================================================================

/-- **Theorem 1 (Stern-Brocot / Minkowski Bijection)**:
    For every bitstring `w`, `?(med(sbMat w)) ≈q dyadMid w = (2 · bitsToNat w + 1) / 2^(|w|+1)`. -/
theorem minkowskiQ_sbMat_mediant (w : List Bool) :
    mediantQ (sbMat w) ≈q dyadMid w := by
  unfold mediantQ
  have h := minkowskiQ_left_sbMat w 1 1 (by omega)
  simp only [Nat.mul_one] at h
  have h11 : minkowskiQ 1 1 ≈q dyad 1 1 := by decide
  have hmul : dyad 1 w.length * minkowskiQ 1 1 ≈q dyad 1 (w.length + 1) :=
    eqv_trans (mul_eqv_mul (eqv_refl _) h11) (dyad_mul 1 1 w.length 1)
  have hadd : dyadLo w + dyad 1 (w.length + 1) ≈q dyadMid w := by
    unfold dyadLo dyadMid eqv
    simp only [add_num, add_den, dyad_num, dyad_den, Nat.pow_succ, Int.natCast_mul, Int.one_mul,
               Int.add_mul]
    change ↑(bitsToNat w) * (↑(2 ^ w.length) * (2 : Int)) * (↑(2 ^ w.length) * 2) +
           ↑(2 ^ w.length) * (↑(2 ^ w.length) * 2) =
           2 * ↑(bitsToNat w) * (↑(2 ^ w.length) * (↑(2 ^ w.length) * 2)) +
           ↑(2 ^ w.length) * (↑(2 ^ w.length) * 2)
    have a1 : ↑(bitsToNat w) * (↑(2 ^ w.length) * (2 : Int)) * (↑(2 ^ w.length) * 2) =
              2 * ↑(bitsToNat w) * (↑(2 ^ w.length) * (↑(2 ^ w.length) * 2)) := by ac_rfl
    omega
  exact eqv_trans h (eqv_trans (add_eqv_add (eqv_refl _) hmul) hadd)

namespace RaneyCert
/-- **Meta-Theorem B1 (Infinite Exponential Total-Variation / Hellinger Overlap Decay ∀ k : Nat)** -/
theorem hellinger_tv_singularity {n : Nat} {C : RaneyCert n} (H : HellingerCert C)
    (k : Nat) (s : Fin n) :
    sumWordsQ k (fun w => minQ (dyad 1 k) (colMeasure (C.mat s * sbMat w)))
      ≤q mkPos (H.v s) H.vMin H.vMin_pos * (mkPos H.rNum H.rDen H.rDen_pos).pow k := by
  have hpoint : ∀ w ∈ allWords k,
      ofNat H.vMin * minQ (dyad 1 k) (colMeasure (C.mat s * sbMat w))
      ≤q hWeight H.cNum H.cDen H.cDen_pos (k + (C.runEmit s w).length) *
           ofNat (H.v (C.runState s w)) := by
    intro w _
    have hcm : colMeasure (C.mat s * sbMat w) ≤q dyad 1 (C.runEmit s w).length := by
      refine le_trans (le_of_eqv (C.run_colMeasure s w)) ?_
      have hd_nn : ofNat 0 ≤q dyad 1 (C.runEmit s w).length := dyad_nonneg (by omega) _
      exact le_trans (mul_le_mul_of_nonneg_left hd_nn (colMeasure_le_one _)) (le_of_eqv (mul_one _))
    have hmin1 := minQ_mono (le_refl (dyad 1 k)) hcm
    have hmin2 := le_trans hmin1 (min_dyad_le_hWeight H.cDen_pos H.c_sq k (C.runEmit s w).length)
    have hvmin_nn : ofNat 0 ≤q ofNat H.vMin := by rw [nonneg_iff]; simp
    have hw_nn : ofNat 0 ≤q hWeight H.cNum H.cDen H.cDen_pos (k + (C.runEmit s w).length) :=
      hWeight_nonneg _ _ _ _
    have hvle : ofNat H.vMin ≤q ofNat (H.v (C.runState s w)) := by
      unfold le; simp; exact H.v_ge (C.runState s w)
    calc ofNat H.vMin * minQ (dyad 1 k) (colMeasure (C.mat s * sbMat w))
        ≤q ofNat H.vMin * hWeight H.cNum H.cDen H.cDen_pos (k + (C.runEmit s w).length) :=
          mul_le_mul_of_nonneg_left hvmin_nn hmin2
      _ ≈q hWeight H.cNum H.cDen H.cDen_pos (k + (C.runEmit s w).length) * ofNat H.vMin :=
          mul_comm _ _
      _ ≤q hWeight H.cNum H.cDen H.cDen_pos (k + (C.runEmit s w).length) *
           ofNat (H.v (C.runState s w)) :=
          mul_le_mul_of_nonneg_left hw_nn hvle
  have hsum := le_trans (le_of_eqv (eqv_symm (sumListQ_mul_left (ofNat H.vMin) (allWords k) _)))
    (le_trans (sumListQ_le (allWords k) hpoint) (hellinger_potential_decay H k s))
  unfold le at hsum ⊢
  simp only [mul_num, mul_den, ofNat_num, ofNat_den, mkPos_num, mkPos_den,
             Nat.one_mul, Int.natCast_mul] at hsum ⊢
  have hre : (sumWordsQ k fun w => (dyad 1 k).minQ (colMeasure (C.mat s * sbMat w))).num *
             (↑H.vMin * ↑((mkPos (↑H.rNum) H.rDen H.rDen_pos).pow k).den) =
             ↑H.vMin * (sumWordsQ k fun w => (dyad 1 k).minQ (colMeasure (C.mat s * sbMat w))).num *
             ↑((mkPos (↑H.rNum) H.rDen H.rDen_pos).pow k).den := by ac_rfl
  rw [hre]; exact hsum

/-- **Meta-Theorem B2 (Constructive Separating Cylinder-Set Singularity ∀ k : Nat)** -/
theorem constructive_separating_sets {n : Nat} {C : RaneyCert n} (H : HellingerCert C)
    (k : Nat) (s : Fin n) :
    let bound := mkPos (H.v s) H.vMin H.vMin_pos * (mkPos H.rNum H.rDen H.rDen_pos).pow k
    let muG := sumWordsQ k (fun w =>
      if dyad 1 k ≤q colMeasure (C.mat s * sbMat w) then dyad 1 k else ofNat 0)
    let pushGc := sumWordsQ k (fun w =>
      if dyad 1 k ≤q colMeasure (C.mat s * sbMat w) then ofNat 0 else colMeasure (C.mat s * sbMat w))
    muG ≤q bound ∧ pushGc ≤q bound := by
  intro bound muG pushGc
  have htv := hellinger_tv_singularity H k s
  constructor
  · refine le_trans (sumListQ_le (allWords k) ?_) htv
    intro w _
    split
    · rename_i h; unfold minQ; simp [h]; exact le_refl _
    · rename_i h; unfold minQ; simp [h]; exact C.run_colMeasure_nonneg s w
  · refine le_trans (sumListQ_le (allWords k) ?_) htv
    intro w _
    split
    · rename_i h; unfold minQ; simp [h]; exact dyad_nonneg (by omega) k
    · rename_i h; unfold minQ; simp [h]; exact le_refl _

-- -----------------------------------------------------------------------------
-- Meta-Theorem C: Finite Stationary-Weight Certificate →
--                 Exact Infinite Linear Bit-Expansion Law ∀ k : Nat
-- -----------------------------------------------------------------------------

end RaneyCert
/-- **Theorem 2a (Constructive Mutual Singularity μ_? ⊥ 2_* μ_? ∀ k : Nat)**:
    For every depth `k`, the total-variation overlap between `μ_?` and `2_* μ_?`
    decays as `≤ (65/57) · (63/64)^k`. -/
theorem singularity_D2 (k : Nat) :
    sumWordsQ k (fun w => minQ (dyad 1 k) (colMeasure (⟨1, 0, 0, 2⟩ * sbMat w)))
      ≤q mkPos 65 57 (by decide) * (mkPos 63 64 (by decide)).pow k :=
  RaneyCert.hellinger_tv_singularity hellingerD2 k ⟨0, by omega⟩

theorem separating_sets_D2 (k : Nat) :
    let bound := mkPos 65 57 (by decide) * (mkPos 63 64 (by decide)).pow k
    let muG := sumWordsQ k (fun w =>
      if dyad 1 k ≤q colMeasure (⟨1, 0, 0, 2⟩ * sbMat w) then dyad 1 k else ofNat 0)
    let pushGc := sumWordsQ k (fun w =>
      if dyad 1 k ≤q colMeasure (⟨1, 0, 0, 2⟩ * sbMat w) then ofNat 0 else colMeasure (⟨1, 0, 0, 2⟩ * sbMat w))
    muG ≤q bound ∧ pushGc ≤q bound :=
  RaneyCert.constructive_separating_sets hellingerD2 k ⟨0, by omega⟩

/-- **Theorem 3a (Exact Infinite Bit-Expansion Law for D = 2, rate α(2) = 7/6, ∀ k : Nat)** -/
theorem bit_expansion_D2 (k : Nat) :
    2 * RaneyCert.sumFinList 4 (fun s => stationaryD2.pi s * sumWordsNat k (fun w => (certD2.runEmit s w).length)) =
    k * 2 ^ k * 14 :=
  RaneyCert.stationary_bit_expansion stationaryD2 k

/-- **Theorem 4a (Exact Rational Integral ∫ ?(2x) dμ_?(x) = 9/13, ∀ k : Nat)** -/
theorem integral_convergence_D2 (k : Nat) :
    abs (RaneyCert.avgMediantQ ⟨1, 0, 0, 2⟩ k - mkPos 9 13 (by decide))
      ≤q mkPos 65 48 (by decide) * (mkPos 9 16 (by decide)).pow k :=
  RaneyCert.integral_convergence integralD2 k ⟨0, by omega⟩

-- -----------------------------------------------------------------------------
-- Exact Closed-Form Depth-k Stern-Brocot Recurrence for D = 2 (Theorem 5)
-- -----------------------------------------------------------------------------

/-- **Corollary (Theorem 5 specialized to x ↦ 2x)**:
    `∀ k : Nat, (1 / 2^k) ∑_{|w|=k} ?(2 · q(w)) ≈q 9/13 + a_k / (52 · 8^k)`. -/
theorem exact_closed_form_D2 (k : Nat) :
    RaneyCert.avgMediantQ ⟨1, 0, 0, 2⟩ k ≈q
      mkPos 9 13 (by decide) + mkPos (d2Seq k).1 (52 * 8 ^ k) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) :=
  exact_closed_form_D2_all k ⟨0, by omega⟩

-- -----------------------------------------------------------------------------
-- 6.2: Determinant D = 3 (7-state primitive Raney transducer; state 0 = x ↦ 3x)
-- -----------------------------------------------------------------------------

/-- **Theorem 2b (Constructive Mutual Singularity μ_? ⊥ 3_* μ_? ∀ k : Nat)** -/
theorem singularity_D3 (k : Nat) :
    sumWordsQ k (fun w => minQ (dyad 1 k) (colMeasure (⟨1, 0, 0, 3⟩ * sbMat w)))
      ≤q mkPos 65 48 (by decide) * (mkPos 31 32 (by decide)).pow k :=
  RaneyCert.hellinger_tv_singularity hellingerD3 k ⟨0, by omega⟩

/-- **Theorem 2c (Constructive Mutual Singularity μ_? ⊥ 4_* μ_? ∀ k : Nat)** -/
theorem singularity_D4Prim (k : Nat) :
    sumWordsQ k (fun w => minQ (dyad 1 k) (colMeasure (⟨1, 0, 0, 4⟩ * sbMat w)))
      ≤q mkPos 60 38 (by decide) * (mkPos 123 128 (by decide)).pow k :=
  RaneyCert.hellinger_tv_singularity hellingerD4Prim k ⟨0, by omega⟩

/-- **Theorem 2d (Constructive Mutual Singularity μ_? ⊥ 5_* μ_? ∀ k : Nat)** -/
theorem singularity_D5 (k : Nat) :
    sumWordsQ k (fun w => minQ (dyad 1 k) (colMeasure (⟨1, 0, 0, 5⟩ * sbMat w)))
      ≤q mkPos 57 31 (by decide) * (mkPos 15 16 (by decide)).pow k :=
  RaneyCert.hellinger_tv_singularity hellingerD5 k ⟨0, by omega⟩

/-- On `Q_D^prim` (`D = 2, 3, 4, 5`), the stationary weights `π(B)` coincide with
    `rowMeasure(B)` (cleared of powers of 2), sum to Dedekind's `ψ(D) ∈ {3, 4, 6, 6}`,
    and satisfy the Row-Column Bit-Expansion Duality
    `∑_B rowMeasure(B) · (|λ(B,0)| + |λ(B,1)|)/2 = ∑_B colMeasure(B)`. -/
theorem row_col_duality_D2 :
    (∀ s : Fin 4, rowMeasure (certD2.mat s) ≈q mkPos (stationaryD2.pi s) 2 (by decide)) ∧
    sumFinQ 4 (fun s => rowMeasure (certD2.mat s)) ≈q ofNat 3 ∧
    sumFinQ 4 (fun s => rowMeasure (certD2.mat s) * dyad ((certD2.emit s false).length + (certD2.emit s true).length) 1)
      ≈q sumFinQ 4 (fun s => colMeasure (certD2.mat s)) := by decide

theorem row_col_duality_D3 :
    (∀ s : Fin 7, rowMeasure (certD3.mat s) ≈q mkPos (stationaryD3.pi s) 4 (by decide)) ∧
    sumFinQ 7 (fun s => rowMeasure (certD3.mat s)) ≈q ofNat 4 ∧
    sumFinQ 7 (fun s => rowMeasure (certD3.mat s) * dyad ((certD3.emit s false).length + (certD3.emit s true).length) 1)
      ≈q sumFinQ 7 (fun s => colMeasure (certD3.mat s)) := by decide

theorem row_col_duality_D4Prim :
    (∀ s : Fin 12, rowMeasure (certD4Prim.mat s) ≈q mkPos (stationaryD4Prim.pi s) 8 (by decide)) ∧
    sumFinQ 12 (fun s => rowMeasure (certD4Prim.mat s)) ≈q ofNat 6 ∧
    sumFinQ 12 (fun s => rowMeasure (certD4Prim.mat s) * dyad ((certD4Prim.emit s false).length + (certD4Prim.emit s true).length) 1)
      ≈q sumFinQ 12 (fun s => colMeasure (certD4Prim.mat s)) := by decide

theorem row_col_duality_D5 :
    (∀ s : Fin 15, rowMeasure (certD5.mat s) ≈q mkPos (stationaryD5.pi s) 16 (by decide)) ∧
    sumFinQ 15 (fun s => rowMeasure (certD5.mat s)) ≈q ofNat 6 ∧
    sumFinQ 15 (fun s => rowMeasure (certD5.mat s) * dyad ((certD5.emit s false).length + (certD5.emit s true).length) 1)
      ≈q sumFinQ 15 (fun s => colMeasure (certD5.mat s)) := by decide

-- =============================================================================
-- SECTION 7: NON-VACUITY WITNESSES & SHARPNESS COUNTEREXAMPLES
-- =============================================================================

/-- Non-vacuity witness: all four reusable engine certificate bundles are inhabited
    on distinct non-trivial state spaces (`n = 4, 7, 12, 15`). -/
theorem nonvacuity_witnesses :
    Nonempty (RaneyCert.HellingerCert certD2) ∧
    Nonempty (RaneyCert.HellingerCert certD3) ∧
    Nonempty (RaneyCert.HellingerCert certD4Prim) ∧
    Nonempty (RaneyCert.HellingerCert certD5) ∧
    Nonempty (RaneyCert.IntegralCert certD2) ∧
    Nonempty (RaneyCert.IntegralCert certD5) :=
  ⟨⟨hellingerD2⟩, ⟨hellingerD3⟩, ⟨hellingerD4Prim⟩, ⟨hellingerD5⟩, ⟨integralD2⟩, ⟨integralD5⟩⟩

/-- Concrete kernel-checked evaluations confirming exact values at `k = 0, 1, 2`. -/
example : RaneyCert.avgMediantQ ⟨1, 0, 0, 2⟩ 0 ≈q mkPos 3 4 (by decide) := by decide
example : RaneyCert.avgMediantQ ⟨1, 0, 0, 2⟩ 1 ≈q mkPos 23 32 (by decide) := by decide
example : RaneyCert.avgMediantQ ⟨1, 0, 0, 2⟩ 2 ≈q mkPos 179 256 (by decide) := by decide
example : RaneyCert.avgMediantQ ⟨1, 0, 0, 3⟩ 1 ≈q mkPos 103 128 (by decide) := by decide

/-- Helper lemma: scaling a matrix by `2` leaves `minkowskiQ` and `colMeasure` invariant! -/
theorem sbBits_double (p q : Nat) : sbBits (2 * p) (2 * q) = sbBits p q := by
  suffices ∀ (fuel p q : Nat), p + q ≤ fuel → sbBitsFuel (2 * fuel) (2 * p) (2 * q) = sbBitsFuel fuel p q by
    unfold sbBits
    have h2 : 2 * p + 2 * q = 2 * (p + q) := by omega
    rw [h2]; exact this (p + q) p q (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro p q h
    simp [sbBitsFuel]
  | succ f ih =>
    intro p q h
    have hf : 2 * (f + 1) = (2 * f + 1) + 1 := by omega
    rw [hf]
    unfold sbBitsFuel
    by_cases hstop : p = 0 ∨ q = 0 ∨ p = q
    · have hstop2 : 2 * p = 0 ∨ 2 * q = 0 ∨ 2 * p = 2 * q := by omega
      simp [hstop, hstop2]
    · have hstop2 : ¬ (2 * p = 0 ∨ 2 * q = 0 ∨ 2 * p = 2 * q) := by omega
      simp only [hstop, hstop2, ↓reduceIte]
      by_cases hlt : p < q
      · have hlt2 : 2 * p < 2 * q := by omega
        have hsub : 2 * q - 2 * p = 2 * (q - p) := by omega
        simp only [hlt, hlt2, ↓reduceIte, hsub]
        congr 1
        rw [sbBitsFuel_eq_of_ge (2 * f + 1) (2 * f) (2 * p) (2 * (q - p)) (by omega) (by omega)]
        exact ih p (q - p) (by omega)
      · have hlt2 : ¬ (2 * p < 2 * q) := by omega
        have hsub : 2 * p - 2 * q = 2 * (p - q) := by omega
        simp only [hlt, hlt2, ↓reduceIte, hsub]
        congr 1
        rw [sbBitsFuel_eq_of_ge (2 * f + 1) (2 * f) (2 * (p - q)) (2 * q) (by omega) (by omega)]
        exact ih (p - q) q (by omega)

theorem minkowskiQ_double (p q : Nat) : minkowskiQ (2 * p) (2 * q) = minkowskiQ p q := by
  unfold minkowskiQ
  by_cases hp : p = 0
  · subst hp; simp
  · have hp2 : 2 * p ≠ 0 := by omega
    by_cases hq : q = 0
    · subst hq; simp [hp, hp2]
    · have hq2 : 2 * q ≠ 0 := by omega
      simp [hp, hp2, hq, hq2, sbBits_double]

theorem colMeasure_two_mul_I (w : List Bool) :
    colMeasure (⟨2, 0, 0, 2⟩ * sbMat w) ≈q dyad 1 w.length := by
  have heq : colMeasure (⟨2, 0, 0, 2⟩ * sbMat w) = colMeasure (sbMat w) := by
    unfold colMeasure
    dsimp only [mul_a, mul_b, mul_c, mul_d]
    simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, minkowskiQ_double]
  rw [heq]; exact colMeasure_sbMat w

theorem allWords_length_mem : ∀ (k : Nat) (w : List Bool), w ∈ allWords k → w.length = k := by
  intro k
  induction k with
  | zero =>
    intro w hw; simp [allWords] at hw; subst hw; rfl
  | succ k ih =>
    intro w hw
    simp only [allWords, List.mem_append, List.mem_map] at hw
    rcases hw with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;> simp [ih u hu]

/-- **Sharpness Counterexample 1 (Unimodular `D = 1`, `A = I_2`)**:
    When `D = 1`, the TV overlap is identically `1` for ALL `k : Nat` — mutual singularity FAILS! -/
theorem sharpness_D1_no_singularity (k : Nat) :
    sumWordsQ k (fun w => minQ (dyad 1 k) (colMeasure (matI * sbMat w))) ≈q ofNat 1 := by
  have hpt : ∀ w ∈ allWords k, minQ (dyad 1 k) (colMeasure (matI * sbMat w)) ≈q dyad 1 k := by
    intro w hw
    rw [matMul_one_left]
    have hcm := colMeasure_sbMat w
    rw [allWords_length_mem k w hw] at hcm
    unfold minQ
    split
    · exact eqv_refl _
    · exact hcm
  have h1 := sumListQ_eqv (allWords k) hpt
  have h2 := sumListQ_const (allWords k) (dyad 1 k)
  rw [allWords_length] at h2
  have h3 : ofNat (2 ^ k) * dyad 1 k ≈q ofNat 1 := by unfold eqv; simp
  exact eqv_trans h1 (eqv_trans h2 h3)

/-- **Sharpness Counterexample 2 (Non-Primitive `D = 4`, `A = 2 · I_2`)**:
    Even though `det(2 · I_2) = 4 > 1`, because `gcd(2, 0, 0, 2) = 2 > 1` (non-primitive),
    the TV overlap is STILL identically `1` for ALL `k : Nat`!
    Contrasted with `singularity_D4Prim` (`det = 4, gcd = 1`, decay `(123/128)^k`), this proves
    that **primitivity is strictly necessary** — `det A > 1` alone does NOT imply singularity. -/
theorem sharpness_D4_nonprim_no_singularity (k : Nat) :
    (2 * 2 - 0 * 0 = 4) ∧
    sumWordsQ k (fun w => minQ (dyad 1 k) (colMeasure (⟨2, 0, 0, 2⟩ * sbMat w))) ≈q ofNat 1 := by
  refine ⟨rfl, ?_⟩
  have hpt : ∀ w ∈ allWords k, minQ (dyad 1 k) (colMeasure (⟨2, 0, 0, 2⟩ * sbMat w)) ≈q dyad 1 k := by
    intro w hw
    have hcm := colMeasure_two_mul_I w
    rw [allWords_length_mem k w hw] at hcm
    unfold minQ
    split
    · exact eqv_refl _
    · exact hcm
  have h1 := sumListQ_eqv (allWords k) hpt
  have h2 := sumListQ_const (allWords k) (dyad 1 k)
  rw [allWords_length] at h2
  have h3 : ofNat (2 ^ k) * dyad 1 k ≈q ofNat 1 := by unfold eqv; simp
  exact eqv_trans h1 (eqv_trans h2 h3)

/-- **Sharpness Counterexample 3 (Dyadic Hellinger Threshold `2 * c^2 ≥ 1`)**:
    Relaxing `c = 91/128` (`2*91^2 = 16562 ≥ 16384`) to `c = 181/256` (`2*181^2 = 65522 < 65536`)
    falsifies sub-multiplicativity `hWeight(c, 1 + 1) ≤ hWeight(c, 1) * hWeight(c, 1)`! -/
theorem sharpness_hellinger_const_counterexample :
    2 * 181 * 181 < 256 * 256 ∧
    ¬ (RaneyCert.hWeight 181 256 (by decide) (1 + 1) ≤q
       RaneyCert.hWeight 181 256 (by decide) 1 * RaneyCert.hWeight 181 256 (by decide) 1) := by
  decide

end RaneyMinkowski
