import CarryAutomatonKrylovL4Energy.Defs

namespace PureSiliconAuto
/-- **THEOREM 1a (Universal Even-Shift Subdivision Law):**
    Exact bit-pair lifting at even shift `s = 2t` for every `BinAuto d`. -/
theorem apCorr_even {d : Nat} (A : BinAuto d) (p q : Fin d) (k t : Nat) :
    apCorr A p q (k + 1) (2 * t) =
      A.sig0 p * A.sig0 q * apCorr A (A.del0 p) (A.del0 q) k t +
      A.sig1 p * A.sig1 q * apCorr A (A.del1 p) (A.del1 q) k t := by
  unfold apCorr
  have hlen : 2 ^ (k + 1) - 2 * t = 2 * (2 ^ k - t) := by
    rw [Nat.pow_succ]; omega
  rw [hlen, sumRange_even_odd]
  have he : sumRange (2 ^ k - t) (fun n => A.eval p (2 * n) * A.eval q (2 * n + 2 * t)) =
      A.sig0 p * A.sig0 q * sumRange (2 ^ k - t) (fun n => A.eval (A.del0 p) n * A.eval (A.del0 q) (n + t)) := by
    rw [← sumRange_mul_left]
    apply sumRange_congr; intro n _
    have hadd : 2 * n + 2 * t = 2 * (n + t) := by omega
    rw [hadd, BinAuto.eval_even, BinAuto.eval_even, mul_four]
  have ho : sumRange (2 ^ k - t) (fun n => A.eval p (2 * n + 1) * A.eval q (2 * n + 1 + 2 * t)) =
      A.sig1 p * A.sig1 q * sumRange (2 ^ k - t) (fun n => A.eval (A.del1 p) n * A.eval (A.del1 q) (n + t)) := by
    rw [← sumRange_mul_left]
    apply sumRange_congr; intro n _
    have hadd : 2 * n + 1 + 2 * t = 2 * (n + t) + 1 := by omega
    rw [hadd, BinAuto.eval_odd, BinAuto.eval_odd, mul_four]
  rw [he, ho]

/-- **REUSABLE MECHANISM A — Finite Left-Annihilator Soundness Theorem:**
    Any finite weight table `w` satisfying `w · E = λ · w`, `w · O0 = 0`, `w · O1 = 0`
    annihilates `weightedCorr A w k s` for ALL `k : Nat` and ALL `s ≥ 1`, and scales
    the zero-shift value by `λ^k`. -/
theorem annihilator_sound {d : Nat} (A : BinAuto d) (w : Fin d → Fin d → Int) (lam : Int)
    (hE : ∀ p' q', leftActE A w p' q' = lam * w p' q')
    (hO0 : ∀ p' q', leftActO0 A w p' q' = 0)
    (hO1 : ∀ p' q', leftActO1 A w p' q' = 0) :
    (∀ k s, s ≥ 1 → weightedCorr A w k s = 0) ∧
    (∀ k, weightedCorr A w k 0 = lam ^ k * weightedCorr A w 0 0) := by
  have heven : ∀ k t, weightedCorr A w (k + 1) (2 * t) = lam * weightedCorr A w k t := by
    intro k t
    unfold weightedCorr
    have hsplit : sumFin d (fun p => sumFin d (fun q => w p q * apCorr A p q (k + 1) (2 * t))) =
        sumFin d (fun p => sumFin d (fun q => w p q * (A.sig0 p * A.sig0 q * apCorr A (A.del0 p) (A.del0 q) k t))) +
        sumFin d (fun p => sumFin d (fun q => w p q * (A.sig1 p * A.sig1 q * apCorr A (A.del1 p) (A.del1 q) k t))) := by
      rw [← sumFin_add]
      apply sumFin_congr; intro p
      rw [← sumFin_add]
      apply sumFin_congr; intro q
      rw [apCorr_even, Int.mul_add]
    rw [hsplit]
    have hp0 := pull_to_push_pair A.del0 A.del0 (fun p q => A.sig0 p * A.sig0 q) w (fun p' q' => apCorr A p' q' k t)
    have hp1 := pull_to_push_pair A.del1 A.del1 (fun p q => A.sig1 p * A.sig1 q) w (fun p' q' => apCorr A p' q' k t)
    rw [hp0, hp1, ← sumFin_add]
    have hcomb : ∀ p' : Fin d,
        sumFin d (fun q' => (sumFin d (fun p => sumFin d (fun q => w p q * (if A.del0 p = p' ∧ A.del0 q = q' then A.sig0 p * A.sig0 q else 0)))) * apCorr A p' q' k t) +
        sumFin d (fun q' => (sumFin d (fun p => sumFin d (fun q => w p q * (if A.del1 p = p' ∧ A.del1 q = q' then A.sig1 p * A.sig1 q else 0)))) * apCorr A p' q' k t) =
        sumFin d (fun q' => leftActE A w p' q' * apCorr A p' q' k t) := by
      intro p'
      rw [← sumFin_add]
      apply sumFin_congr; intro q'
      rw [← Int.add_mul]
      congr 1
      unfold leftActE
      rw [← sumFin_add]
      apply sumFin_congr; intro p
      rw [← sumFin_add]
      apply sumFin_congr; intro q
      rw [Int.mul_add]
    simp only [hcomb, hE]
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro p'
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro q'
    rw [Int.mul_assoc]
  have hodd : ∀ k t, weightedCorr A w (k + 1) (2 * t + 1) = 0 := by
    intro k t
    unfold weightedCorr
    have hsplit : sumFin d (fun p => sumFin d (fun q => w p q * apCorr A p q (k + 1) (2 * t + 1))) =
        sumFin d (fun p => sumFin d (fun q => w p q * (A.sig0 p * A.sig1 q * apCorr A (A.del0 p) (A.del1 q) k t))) +
        sumFin d (fun p => sumFin d (fun q => w p q * (A.sig1 p * A.sig0 q * apCorr A (A.del1 p) (A.del0 q) k (t + 1)))) := by
      rw [← sumFin_add]
      apply sumFin_congr; intro p
      rw [← sumFin_add]
      apply sumFin_congr; intro q
      rw [apCorr_odd, Int.mul_add]
    rw [hsplit]
    have hp0 := pull_to_push_pair A.del0 A.del1 (fun p q => A.sig0 p * A.sig1 q) w (fun p' q' => apCorr A p' q' k t)
    have hp1 := pull_to_push_pair A.del1 A.del0 (fun p q => A.sig1 p * A.sig0 q) w (fun p' q' => apCorr A p' q' k (t + 1))
    rw [hp0, hp1]
    have h1 : sumFin d (fun p' => sumFin d (fun q' => leftActO0 A w p' q' * apCorr A p' q' k t)) = 0 := by
      simp [hO0, sumFin_zero]
    have h2 : sumFin d (fun p' => sumFin d (fun q' => leftActO1 A w p' q' * apCorr A p' q' k (t + 1))) = 0 := by
      simp [hO1, sumFin_zero]
    change sumFin d (fun p' => sumFin d (fun q' => leftActO0 A w p' q' * apCorr A p' q' k t)) +
           sumFin d (fun p' => sumFin d (fun q' => leftActO1 A w p' q' * apCorr A p' q' k (t + 1))) = 0
    rw [h1, h2]; rfl
  constructor
  · intro k
    induction k with
    | zero =>
      intro s hs
      cases s with
      | zero => omega
      | succ s =>
        unfold weightedCorr
        simp [apCorr_zero_succ, sumFin_zero]
    | succ k ih =>
      intro s hs
      by_cases hp : s % 2 = 0
      · have hs2 : s = 2 * (s / 2) := by omega
        rw [hs2, heven, ih (s / 2) (by omega), Int.mul_zero]
      · have hs2 : s = 2 * (s / 2) + 1 := by omega
        rw [hs2, hodd]
  · intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h0 : (0 : Nat) = 2 * 0 := rfl
      rw [h0, heven, ih, Int.pow_succ, Int.mul_comm (lam ^ k) lam, Int.mul_assoc]

-- ----------------------------------------------------------------------------
-- Pure-Silicon Polynomial Flatness & Partial-Sum Pythagorean Lifter
-- ----------------------------------------------------------------------------

/-- **THEOREM 1 (Universal Infinite Flat-Spectrum & Pythagorean Theorem for ALL `m` and ALL `ψ`):**
    For EVERY width `m : Nat`, EVERY nonlinear feedback function `ψ : Fin (2^m) → Bool`,
    and EVERY block length `k : Nat`:
    1. Exact zero total autocorrelation for ALL shifts `s ≥ 1`: `∑_q apCorr q q k s = 0`.
    2. Exact pure-integer polynomial flatness for ALL `X : Int`:
       `∑_q P_{q, k}(X) * P^{rev}_{q, k}(X) = 2^(k + m + 1) * X^(2^k - 1)`.
    3. Exact partial-sum Pythagorean law (`X = 1`):
       `∑_q (∑_{n < 2^k} f_q(n))^2 = 2^(k + m + 1)`. -/
theorem bijTail_infinite_flat_spectrum (m : Nat) (ψ : Fin (2 ^ m) → Bool) :
    (∀ k s, s ≥ 1 → sumFin (2 ^ (m + 1)) (fun q => apCorr (bijTailAuto m ψ) q q k s) = 0) ∧
    (∀ k (X : Int),
      sumFin (2 ^ (m + 1)) (fun q => polyEval (bijTailAuto m ψ) q k X * polyRevEval (bijTailAuto m ψ) q k X) =
      (2 : Int) ^ (k + m + 1) * X ^ (2 ^ k - 1)) ∧
    (∀ k,
      sumFin (2 ^ (m + 1)) (fun q =>
        sumRange (2 ^ k) (fun n => (bijTailAuto m ψ).eval q n) *
        sumRange (2 ^ k) (fun n => (bijTailAuto m ψ).eval q n)) =
      (2 : Int) ^ (k + m + 1)) := by
  have hsq : ∀ q, bijTailSig1 m ψ q * bijTailSig1 m ψ q = 1 := by
    intro q; dsimp only [bijTailSig1]
    cases xor (ψ ⟨q.1 / 2, by have hpow := pow2_succ m; have hq := q.2; omega⟩) (q.1 % 2 == 1) <;> rfl
  have hbij : ∀ r : Fin (2 ^ m),
      bijTailSig1 m ψ ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ +
      bijTailSig1 m ψ ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = 0 := by
    intro r
    unfold bijTailSig1
    have hdiv0 : (2 * r.1) / 2 = r.1 := by omega
    have hdiv1 : (2 * r.1 + 1) / 2 = r.1 := by omega
    have hmod0 : (2 * r.1) % 2 = 0 := by omega
    have hmod1 : (2 * r.1 + 1) % 2 = 1 := by omega
    have hr0 : (⟨(2 * r.1) / 2, by omega⟩ : Fin (2 ^ m)) = r := Fin.ext hdiv0
    have hr1 : (⟨(2 * r.1 + 1) / 2, by omega⟩ : Fin (2 ^ m)) = r := Fin.ext hdiv1
    simp only [hmod0, hmod1, hr0, hr1]
    cases ψ r <;> decide
  have ⟨hE, hO0, hO1⟩ := (debruijn_trace_annihilator_iff m (bijTailSig1 m ψ) hsq).mpr hbij
  have ⟨hann, hzero0⟩ := annihilator_sound (bijTailAuto m ψ) (traceW _) 2 hE hO0 hO1
  have hwc_eq : ∀ k s, weightedCorr (bijTailAuto m ψ) (traceW _) k s =
      sumFin (2 ^ (m + 1)) (fun q => apCorr (bijTailAuto m ψ) q q k s) := by
    intro k s
    unfold weightedCorr
    apply sumFin_congr; intro p
    have h : (fun q => traceW _ p q * apCorr (bijTailAuto m ψ) p q k s) =
        (fun q => if p = q then apCorr (bijTailAuto m ψ) p q k s else 0) := by
      funext q; unfold traceW; by_cases heq : p = q <;> simp [heq]
    rw [h, sumFin_ite_eq]
  have hdiag0 : ∀ k, sumFin (2 ^ (m + 1)) (fun q => apCorr (bijTailAuto m ψ) q q k 0) =
      (2 : Int) ^ (k + m + 1) := by
    intro k
    rw [← hwc_eq, hzero0, hwc_eq]
    have hbase : sumFin (2 ^ (m + 1)) (fun q => apCorr (bijTailAuto m ψ) q q 0 0) = (2 : Int) ^ (m + 1) := by
      have h1 : ∀ q, apCorr (bijTailAuto m ψ) q q 0 0 = 1 := fun q => by
        rw [apCorr_zero_zero]; rfl
      simp only [h1]
      have hsum1 : ∀ n : Nat, sumFin n (fun _ => (1 : Int)) = (n : Int) := by
        intro n; unfold sumFin
        have haux : ∀ j (_hj : j ≤ n), sumRange j (fun i => if i < n then (1 : Int) else 0) = (j : Int) := by
          intro j hj; induction j with
          | zero => rfl
          | succ j ihj =>
            rw [sumRange, ihj (by omega)]
            have : j < n := by omega
            simp [this]
        exact haux n (Nat.le_refl n)
      rw [hsum1]
      clear h1 hsum1
      induction (m + 1) with
      | zero => rfl
      | succ n ihn =>
        rw [Nat.pow_succ, Int.natCast_mul, ihn, Int.pow_succ]; rfl
    rw [hbase, ← Int.pow_add, ← Nat.add_assoc]
  have hflat : ∀ k s, s ≥ 1 → sumFin (2 ^ (m + 1)) (fun q => apCorr (bijTailAuto m ψ) q q k s) = 0 := by
    intro k s hs; rw [← hwc_eq]; exact hann k s hs
  have hpoly : ∀ k (X : Int),
      sumFin (2 ^ (m + 1)) (fun q => polyEval (bijTailAuto m ψ) q k X * polyRevEval (bijTailAuto m ψ) q k X) =
      (2 : Int) ^ (k + m + 1) * X ^ (2 ^ k - 1) := by
    intro k X
    have h := poly_flat_of_diag_zero (bijTailAuto m ψ) (fun _ => 1) k
      (fun s hs => by simpa using hflat k s hs) X
    simpa [hdiag0 k] using h
  refine ⟨hflat, hpoly, ?_⟩
  intro k
  have h1 := hpoly k 1
  have hone : ∀ n : Nat, (1 : Int) ^ n = 1 := by
    intro n; induction n with | zero => rfl | succ n ih => rw [Int.pow_succ, ih]; rfl
  simp only [polyEval, polyRevEval, hone, Int.mul_one] at h1
  exact h1

-- ----------------------------------------------------------------------------
-- Concrete Non-Classical Cubic Witness (m = 2, L = 4: 111 XOR 1**1) & Sharpness
-- ----------------------------------------------------------------------------

theorem apCorrU_even {d : Nat} (A : BinAuto d) (u : Fin (d * d)) (k t : Nat) :
    apCorrU A u (k + 1) (2 * t) =
      pairWeight A 0 u * apCorrU A (pairStep A 0 u) k t +
      pairWeight A 1 u * apCorrU A (pairStep A 1 u) k t := by
  have h0s : pairStep A 0 u = pairIdx (A.del0 ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩)
      (A.del0 ⟨u.1 % d, Nat.mod_lt u.1 (pos_of_fin_sq u)⟩) := rfl
  have h1s : pairStep A 1 u = pairIdx (A.del1 ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩)
      (A.del1 ⟨u.1 % d, Nat.mod_lt u.1 (pos_of_fin_sq u)⟩) := rfl
  have h0w : pairWeight A 0 u = A.sig0 ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩ *
      A.sig0 ⟨u.1 % d, Nat.mod_lt u.1 (pos_of_fin_sq u)⟩ := rfl
  have h1w : pairWeight A 1 u = A.sig1 ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩ *
      A.sig1 ⟨u.1 % d, Nat.mod_lt u.1 (pos_of_fin_sq u)⟩ := rfl
  rw [h0s, h1s, h0w, h1w, apCorrU_pairIdx, apCorrU_pairIdx]
  exact apCorr_even A _ _ k t

/-- **REUSABLE MECHANISM B — Universal Exact Finite-Dimensional `L^4`-Energy Closure Law:**
    For EVERY `BinAuto d` and EVERY `k : Nat`, the infinite-shift quadratic tensors
    `(Q(k+1), R(k+1), Z(k+1))` equal `primalStep A (Q(k), R(k), Z(k))` entrywise! -/
theorem qrz_step {d : Nat} (A : BinAuto d) (k : Nat) :
    (∀ u v, (qrzAt A (k + 1)).Q u v = (primalStep A (qrzAt A k)).Q u v) ∧
    (∀ u v, (qrzAt A (k + 1)).R u v = (primalStep A (qrzAt A k)).R u v) ∧
    (∀ u v, (qrzAt A (k + 1)).Z u v = (primalStep A (qrzAt A k)).Z u v) := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    dsimp only [qrzAt, primalStep, pull]
    unfold qTensor
    rw [hpow, sumRange_even_odd]
    have heven :
        sumRange (2 ^ k) (fun t => apCorrU A u (k + 1) (2 * t) * apCorrU A v (k + 1) (2 * t)) =
        pairWeight A 0 u * pairWeight A 0 v * qTensor A k (pairStep A 0 u) (pairStep A 0 v) +
        pairWeight A 0 u * pairWeight A 1 v * qTensor A k (pairStep A 0 u) (pairStep A 1 v) +
        pairWeight A 1 u * pairWeight A 0 v * qTensor A k (pairStep A 1 u) (pairStep A 0 v) +
        pairWeight A 1 u * pairWeight A 1 v * qTensor A k (pairStep A 1 u) (pairStep A 1 v) := by
      unfold qTensor
      simp only [← sumRange_mul_left, ← sumRange_add]
      apply sumRange_congr; intro t _
      rw [apCorrU_even, apCorrU_even, prod_two_add]
    have hodd :
        sumRange (2 ^ k) (fun t => apCorrU A u (k + 1) (2 * t + 1) * apCorrU A v (k + 1) (2 * t + 1)) =
        pairWeight A 2 u * pairWeight A 2 v * qTensor A k (pairStep A 2 u) (pairStep A 2 v) +
        pairWeight A 3 u * pairWeight A 3 v * (qTensor A k (pairStep A 3 u) (pairStep A 3 v) - zTensor A k (pairStep A 3 u) (pairStep A 3 v)) +
        pairWeight A 2 u * pairWeight A 3 v * rTensor A k (pairStep A 2 u) (pairStep A 3 v) +
        pairWeight A 3 u * pairWeight A 2 v * rTensor A k (pairStep A 2 v) (pairStep A 3 u) := by
      rw [← sumRange_shift_tail A k (pairStep A 3 u) (pairStep A 3 v)]
      unfold qTensor rTensor
      simp only [← sumRange_mul_left, ← sumRange_add]
      apply sumRange_congr; intro t _
      rw [apCorrU_odd, apCorrU_odd, prod_two_add,
          Int.mul_comm (apCorrU A (pairStep A 2 v) k t) (apCorrU A (pairStep A 3 u) k (t + 1))]
      omega
    rw [heven, hodd]
    unfold qTensor rTensor
    omega
  · intro u v
    dsimp only [qrzAt, primalStep, pull]
    unfold rTensor
    rw [hpow, sumRange_even_odd]
    have heven :
        sumRange (2 ^ k) (fun t => apCorrU A u (k + 1) (2 * t) * apCorrU A v (k + 1) (2 * t + 1)) =
        pairWeight A 0 u * pairWeight A 2 v * qTensor A k (pairStep A 0 u) (pairStep A 2 v) +
        pairWeight A 1 u * pairWeight A 2 v * qTensor A k (pairStep A 1 u) (pairStep A 2 v) +
        pairWeight A 0 u * pairWeight A 3 v * rTensor A k (pairStep A 0 u) (pairStep A 3 v) +
        pairWeight A 1 u * pairWeight A 3 v * rTensor A k (pairStep A 1 u) (pairStep A 3 v) := by
      unfold qTensor rTensor
      simp only [← sumRange_mul_left, ← sumRange_add]
      apply sumRange_congr; intro t _
      rw [apCorrU_even, apCorrU_odd, prod_two_add]
      omega
    have hodd :
        sumRange (2 ^ k) (fun t => apCorrU A u (k + 1) (2 * t + 1) * apCorrU A v (k + 1) (2 * t + 1 + 1)) =
        pairWeight A 3 u * pairWeight A 0 v * (qTensor A k (pairStep A 3 u) (pairStep A 0 v) - zTensor A k (pairStep A 3 u) (pairStep A 0 v)) +
        pairWeight A 3 u * pairWeight A 1 v * (qTensor A k (pairStep A 3 u) (pairStep A 1 v) - zTensor A k (pairStep A 3 u) (pairStep A 1 v)) +
        pairWeight A 2 u * pairWeight A 0 v * rTensor A k (pairStep A 2 u) (pairStep A 0 v) +
        pairWeight A 2 u * pairWeight A 1 v * rTensor A k (pairStep A 2 u) (pairStep A 1 v) := by
      rw [← sumRange_shift_tail A k (pairStep A 3 u) (pairStep A 0 v),
          ← sumRange_shift_tail A k (pairStep A 3 u) (pairStep A 1 v)]
      unfold rTensor
      simp only [← sumRange_mul_left, ← sumRange_add]
      apply sumRange_congr; intro t _
      have h2t2 : 2 * t + 1 + 1 = 2 * (t + 1) := by omega
      rw [h2t2, apCorrU_odd, apCorrU_even, prod_two_add]
      omega
    rw [heven, hodd]
    unfold qTensor rTensor
    omega
  · intro u v
    dsimp only [qrzAt, primalStep, pull, zTensor]
    have h0 : apCorrU A u (k + 1) 0 =
        pairWeight A 0 u * apCorrU A (pairStep A 0 u) k 0 +
        pairWeight A 1 u * apCorrU A (pairStep A 1 u) k 0 := by
      simpa using apCorrU_even A u k 0
    have h1 : apCorrU A v (k + 1) 0 =
        pairWeight A 0 v * apCorrU A (pairStep A 0 v) k 0 +
        pairWeight A 1 v * apCorrU A (pairStep A 1 v) k 0 := by
      simpa using apCorrU_even A v k 0
    rw [h0, h1, prod_two_add]

-- ----------------------------------------------------------------------------
-- Fast Kernel-Reducible Materialized Grids (`List (List Int)`) & Exact Sparse Adjoint
-- ----------------------------------------------------------------------------

/-- **Exact Adjointness Theorem (`innerQRZ_dualStep`):**
    `⟨dualStep A W, S⟩ = ⟨W, primalStep A S⟩` for EVERY `BinAuto d`, `W`, and `S`. -/
theorem innerQRZ_dualStep {d : Nat} (A : BinAuto d) (W : DualQRZ) (S : QRZFn (d * d)) :
    innerQRZ (d * d) (dualStep A W) S = innerQRZ (d * d) W (primalStep A S) := by
  have hadd2 : ∀ (f g : Fin (d * d) → Fin (d * d) → Int) (X : Fin (d * d) → Fin (d * d) → Int),
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => (f u v + g u v) * X u v)) =
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => f u v * X u v)) +
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => g u v * X u v)) := by
    intro f g X
    rw [← sumFin_add]; apply sumFin_congr; intro u
    rw [← sumFin_add]; apply sumFin_congr; intro v; exact Int.add_mul _ _ _
  have hsub2 : ∀ (f g : Fin (d * d) → Fin (d * d) → Int) (X : Fin (d * d) → Fin (d * d) → Int),
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => (f u v - g u v) * X u v)) =
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => f u v * X u v)) -
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => g u v * X u v)) := by
    intro f g X
    rw [← sumFin_sub]; apply sumFin_congr; intro u
    rw [← sumFin_sub]; apply sumFin_congr; intro v; exact Int.sub_mul _ _ _
  have haddR : ∀ (G : Grid) (X Y : Fin (d * d) → Fin (d * d) → Int),
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG G u.1 v.1 * (X u v + Y u v))) =
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG G u.1 v.1 * X u v)) +
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG G u.1 v.1 * Y u v)) := by
    intro G X Y
    rw [← sumFin_add]; apply sumFin_congr; intro u
    rw [← sumFin_add]; apply sumFin_congr; intro v; exact Int.mul_add _ _ _
  have hpull_sub : ∀ (a b : Fin 4) (G : Grid) (X Y : Fin (d * d) → Fin (d * d) → Int),
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG G u.1 v.1 * pull A a b (fun x y => X x y - Y x y) u v)) =
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG G u.1 v.1 * pull A a b X u v)) -
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG G u.1 v.1 * pull A a b Y u v)) := by
    intro a b G X Y
    rw [← sumFin_sub]; apply sumFin_congr; intro u
    rw [← sumFin_sub]; apply sumFin_congr; intro v
    unfold pull; rw [Int.mul_sub, Int.mul_sub]
  unfold innerQRZ innerGrid dualStep dualStepPre primalStep
  simp only [getG_tabulateG]
  have hpre_fn : getPre (buildPreTable A) = preimages A := by
    funext tag u'; exact getPre_buildPreTable A tag u'
  rw [hpre_fn]
  simp only [hadd2, hsub2, pushEntry_adjoint, pushEntryT_adjoint]
  simp only [haddR, hpull_sub]
  omega

private theorem innerQRZ_dualStepFast {d : Nat} (A : BinAuto d) (W : DualQRZ) (S : QRZFn (d * d)) :
    innerQRZ (d * d) (dualStepFast (packPreTable (buildPreTable A)) W) S =
    innerQRZ (d * d) W (primalStep A S) := by
  rw [← innerQRZ_dualStep A W S]
  unfold innerQRZ innerGrid dualStep
  congr 1; congr 1
  · apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(getG_dualStepFast (buildPreTable A) W u v).1]
  · apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(getG_dualStepFast (buildPreTable A) W u v).2.1]
  · apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(getG_dualStepFast (buildPreTable A) W u v).2.2]

/-- **Key Dual-Orbit Evaluation Identity:**
    For EVERY `k, j : Nat`, `⟨dualIter A W j, qrzAt A k⟩ = ⟨W, qrzAt A (k + j)⟩`. -/
theorem innerQRZ_dualIter {d : Nat} (A : BinAuto d) (W : DualQRZ) (k j : Nat) :
    innerQRZ (d * d) (dualIter A W j) (qrzAt A k) = innerQRZ (d * d) W (qrzAt A (k + j)) := by
  induction j generalizing k with
  | zero => simp [dualIter, dualIterPre]
  | succ j ih =>
    rw [dualIter_succ, innerQRZ_dualStepFast]
    have hstep : innerQRZ (d * d) (dualIter A W j) (primalStep A (qrzAt A k)) =
        innerQRZ (d * d) (dualIter A W j) (qrzAt A (k + 1)) := by
      have ⟨hQ, hR, hZ⟩ := qrz_step A k
      unfold innerQRZ innerGrid
      congr 1; congr 1
      · apply sumFin_congr; intro u; apply sumFin_congr; intro v; rw [hQ]
      · apply sumFin_congr; intro u; apply sumFin_congr; intro v; rw [hR]
      · apply sumFin_congr; intro u; apply sumFin_congr; intro v; rw [hZ]
    rw [hstep, ih (k + 1), show k + 1 + j = k + (j + 1) by omega]

/-- **REUSABLE MECHANISM B — Universal Dual-Krylov Certificate Soundness Theorem:**
    For ANY `BinAuto d`, ANY target energy functional `W0`, and ANY pure-data certificate
    `cert = ⟨k0, coeffs⟩`: if `checkDualCert A W0 cert = true`, then for **EVERY `k : Nat`**,
    the exact scalar sequence `val(n) = ⟨W0, qrzAt A n⟩` satisfies the infinite linear recurrence:
    `val(k + k0 + coeffs.length) = ∑_{j=0}^{r-1} coeffs[j] * val(k + k0 + j)`! -/
theorem dual_krylov_sound {d : Nat} (A : BinAuto d) (W0 : DualQRZ) (cert : DualCert)
    (hok : checkDualCert A W0 cert = true) :
    ∀ k : Nat,
      innerQRZ (d * d) W0 (qrzAt A (k + cert.k0 + cert.coeffs.length)) =
      evalRecurrence cert.coeffs (fun n => innerQRZ (d * d) W0 (qrzAt A n)) (k + cert.k0) := by
  let pp := packPreTable (buildPreTable A)
  let r := cert.coeffs.length
  let orbit := dualOrbitPre (d * d) pp W0 (cert.k0 + r)
  let target := orbit.getD (cert.k0 + r) W0
  let window := (orbit.drop cert.k0).take r
  have horb_len : orbit.length = cert.k0 + r + 1 := dualOrbitPre_len (d * d) pp W0 (cert.k0 + r)
  have hwin_len : window.length = r := by
    simp only [window, List.length_take, List.length_drop, horb_len]
    omega
  have htarget_eq : target = dualIter A W0 (cert.k0 + r) :=
    dualOrbitPre_getD (d * d) pp W0 (cert.k0 + r) (cert.k0 + r) (Nat.le_refl _)
  have hwin_get : ∀ j (hj : j < window.length), window[j] = dualIter A W0 (cert.k0 + j) := by
    intro j hj
    have hjr : j < r := by omega
    have hlt : cert.k0 + j < orbit.length := by rw [horb_len]; omega
    have h1 : window[j] = orbit[cert.k0 + j] := by
      simp [window, List.getElem_take, List.getElem_drop]
    rw [h1]
    have h2 := dualOrbitPre_getD (d * d) pp W0 (cert.k0 + r) (cert.k0 + j) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at h2
    exact h2
  have hentries : ∀ u v : Fin (d * d),
      getG target.WQ u.1 v.1 = linCombGrid cert.coeffs (window.map (·.WQ)) u.1 v.1 ∧
      getG target.WR u.1 v.1 = linCombGrid cert.coeffs (window.map (·.WR)) u.1 v.1 ∧
      getG target.WZ u.1 v.1 = linCombGrid cert.coeffs (window.map (·.WZ)) u.1 v.1 := by
    unfold checkDualCert at hok
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
    intro u v
    have h := hok u (List.mem_finRange u) v (List.mem_finRange v)
    exact ⟨h.1.1, h.1.2, h.2⟩
  intro k
  have hlhs : innerQRZ (d * d) W0 (qrzAt A (k + cert.k0 + r)) = innerQRZ (d * d) target (qrzAt A k) := by
    rw [htarget_eq, innerQRZ_dualIter, show k + (cert.k0 + r) = k + cert.k0 + r by omega]
  change innerQRZ (d * d) W0 (qrzAt A (k + cert.k0 + r)) = _
  rw [hlhs]
  unfold innerQRZ innerGrid
  have hQ : sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG target.WQ u.1 v.1 * (qrzAt A k).Q u v)) =
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WQ (qrzAt A k).Q) cert.coeffs window).sum := by
    rw [← linCombGrid_inner (d * d) cert.coeffs window (·.WQ) (qrzAt A k).Q hwin_len]
    apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(hentries u v).1]
  have hR : sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG target.WR u.1 v.1 * (qrzAt A k).R u v)) =
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WR (qrzAt A k).R) cert.coeffs window).sum := by
    rw [← linCombGrid_inner (d * d) cert.coeffs window (·.WR) (qrzAt A k).R hwin_len]
    apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(hentries u v).2.1]
  have hZ : sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG target.WZ u.1 v.1 * (qrzAt A k).Z u v)) =
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WZ (qrzAt A k).Z) cert.coeffs window).sum := by
    rw [← linCombGrid_inner (d * d) cert.coeffs window (·.WZ) (qrzAt A k).Z hwin_len]
    apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(hentries u v).2.2]
  rw [hQ, hR, hZ]
  have hcomb : ∀ (cs : List Int) (ws : List DualQRZ),
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WQ (qrzAt A k).Q) cs ws).sum +
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WR (qrzAt A k).R) cs ws).sum +
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WZ (qrzAt A k).Z) cs ws).sum =
      (List.zipWith (fun c w => c * innerQRZ (d * d) w (qrzAt A k)) cs ws).sum := by
    intro cs ws
    induction cs generalizing ws with
    | nil => simp
    | cons c cs ih =>
      cases ws with
      | nil => simp
      | cons w ws =>
        simp only [List.zipWith_cons_cons, List.sum_cons]
        have hih := ih ws
        have hw : c * innerQRZ (d * d) w (qrzAt A k) =
            c * innerGrid (d * d) w.WQ (qrzAt A k).Q +
            c * innerGrid (d * d) w.WR (qrzAt A k).R +
            c * innerGrid (d * d) w.WZ (qrzAt A k).Z := by
          unfold innerQRZ; rw [Int.mul_add, Int.mul_add]
        rw [hw]
        omega
  rw [hcomb]
  apply zipWith_evalRec cert.coeffs (k + cert.k0) window
    (fun w => innerQRZ (d * d) w (qrzAt A k))
    (fun n => innerQRZ (d * d) W0 (qrzAt A n))
    hwin_len
  intro j hj
  rw [hwin_get j hj, innerQRZ_dualIter, show k + (cert.k0 + j) = k + cert.k0 + j by omega]

-- ----------------------------------------------------------------------------
-- Depth-1 Linear-Time Step-Witnessed Dual-Krylov Certificate Checker
-- (Eliminates exponential thunk re-evaluation in Lean's non-memoizing kernel!)
-- ----------------------------------------------------------------------------

/-- **Depth-1 Witnessed Orbit Soundness:**
    Every entry `orbit[j]` of a verified orbit equals `(T*)^j W0` against every `qrzAt A k`. -/
theorem checkWitnessedOrbit_sound {d : Nat} (A : BinAuto d) (W0 : DualQRZ) (orbit : List DualQRZ)
    (hok : checkWitnessedOrbit A W0 orbit = true) :
    ∀ j (hj : j < orbit.length) (k : Nat),
      innerQRZ (d * d) orbit[j] (qrzAt A k) = innerQRZ (d * d) W0 (qrzAt A (k + j)) := by
  cases orbit with
  | nil => simp [checkWitnessedOrbit] at hok
  | cons w0 rest =>
    simp only [checkWitnessedOrbit, Bool.and_eq_true] at hok
    intro j hj k
    induction j generalizing k with
    | zero =>
      simpa using eqDualQRZ_inner (d * d) w0 W0 (qrzAt A k) hok.1
    | succ j ih =>
      have hstep_eq := checkOrbitSteps_step (packPreTable (buildPreTable A)) (w0 :: rest) hok.2 j hj
      rw [← eqDualQRZ_inner (d * d) _ _ (qrzAt A k) hstep_eq]
      rw [innerQRZ_dualStepFast]
      have hq : innerQRZ (d * d) (w0 :: rest)[j] (primalStep A (qrzAt A k)) =
          innerQRZ (d * d) (w0 :: rest)[j] (qrzAt A (k + 1)) := by
        have ⟨hQ, hR, hZ⟩ := qrz_step A k
        unfold innerQRZ innerGrid
        congr 1; congr 1
        · apply sumFin_congr; intro u; apply sumFin_congr; intro v; rw [hQ]
        · apply sumFin_congr; intro u; apply sumFin_congr; intro v; rw [hR]
        · apply sumFin_congr; intro u; apply sumFin_congr; intro v; rw [hZ]
      rw [hq, ih (by omega) (k + 1), show k + 1 + j = k + (j + 1) by omega]

/-- **Depth-0 Evaluation from a Verified Witnessed Orbit:** -/
theorem witnessed_orbit_eval_zero {d : Nat} (A : BinAuto d) (W0 : DualQRZ) (orbit : List DualQRZ)
    (hok : checkWitnessedOrbit A W0 orbit = true) (j : Nat) (hj : j < orbit.length) :
    innerQRZ (d * d) W0 (qrzAt A j) = evalDualAtZero A orbit[j] := by
  rw [← innerQRZ_qrzAt_zero, checkWitnessedOrbit_sound A W0 orbit hok j hj 0, Nat.zero_add]

/-- **REUSABLE MECHANISM B (Depth-1 Linear-Time Form) — Witnessed Dual-Krylov Soundness:**
    Identical infinite recurrence conclusion to `dual_krylov_sound`, verified at Depth 1 in
    linear time `O((k0 + r) * D^2)` inside Lean's kernel! -/
theorem witnessed_dual_krylov_sound {d : Nat} (A : BinAuto d) (W0 : DualQRZ) (cert : WitnessedDualCert)
    (hok : checkWitnessedDualCert A W0 cert = true) :
    ∀ k : Nat,
      innerQRZ (d * d) W0 (qrzAt A (k + cert.k0 + cert.coeffs.length)) =
      evalRecurrence cert.coeffs (fun n => innerQRZ (d * d) W0 (qrzAt A n)) (k + cert.k0) := by
  unfold checkWitnessedDualCert at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨horb_len, horb_ok⟩, hlin_ok⟩ := hok
  let r := cert.coeffs.length
  let target := cert.orbit.getD (cert.k0 + r) W0
  let window := (cert.orbit.drop cert.k0).take r
  have hwin_len : window.length = r := by
    simp only [window, List.length_take, List.length_drop, horb_len]; omega
  have htarget_lt : cert.k0 + r < cert.orbit.length := by omega
  have htarget_eq : target = cert.orbit[cert.k0 + r] := by
    simp only [target, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htarget_lt, Option.getD_some]
  have hwin_get : ∀ j (hj : j < window.length), window[j] = cert.orbit[cert.k0 + j]'(by omega) := by
    intro j hj
    simp [window, List.getElem_take, List.getElem_drop]
  have hentries : ∀ u v : Fin (d * d),
      getG target.WQ u.1 v.1 = linCombGrid cert.coeffs (window.map (·.WQ)) u.1 v.1 ∧
      getG target.WR u.1 v.1 = linCombGrid cert.coeffs (window.map (·.WR)) u.1 v.1 ∧
      getG target.WZ u.1 v.1 = linCombGrid cert.coeffs (window.map (·.WZ)) u.1 v.1 := by
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hlin_ok
    intro u v
    have h := hlin_ok u (List.mem_finRange u) v (List.mem_finRange v)
    exact ⟨h.1.1, h.1.2, h.2⟩
  intro k
  have hlhs : innerQRZ (d * d) W0 (qrzAt A (k + cert.k0 + r)) = innerQRZ (d * d) target (qrzAt A k) := by
    rw [htarget_eq, checkWitnessedOrbit_sound A W0 cert.orbit horb_ok (cert.k0 + r) htarget_lt k,
        show k + (cert.k0 + r) = k + cert.k0 + r by omega]
  change innerQRZ (d * d) W0 (qrzAt A (k + cert.k0 + r)) = _
  rw [hlhs]
  unfold innerQRZ innerGrid
  have hQ : sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG target.WQ u.1 v.1 * (qrzAt A k).Q u v)) =
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WQ (qrzAt A k).Q) cert.coeffs window).sum := by
    rw [← linCombGrid_inner (d * d) cert.coeffs window (·.WQ) (qrzAt A k).Q hwin_len]
    apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(hentries u v).1]
  have hR : sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG target.WR u.1 v.1 * (qrzAt A k).R u v)) =
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WR (qrzAt A k).R) cert.coeffs window).sum := by
    rw [← linCombGrid_inner (d * d) cert.coeffs window (·.WR) (qrzAt A k).R hwin_len]
    apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(hentries u v).2.1]
  have hZ : sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG target.WZ u.1 v.1 * (qrzAt A k).Z u v)) =
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WZ (qrzAt A k).Z) cert.coeffs window).sum := by
    rw [← linCombGrid_inner (d * d) cert.coeffs window (·.WZ) (qrzAt A k).Z hwin_len]
    apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(hentries u v).2.2]
  rw [hQ, hR, hZ]
  have hcomb : ∀ (cs : List Int) (ws : List DualQRZ),
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WQ (qrzAt A k).Q) cs ws).sum +
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WR (qrzAt A k).R) cs ws).sum +
      (List.zipWith (fun c w => c * innerGrid (d * d) w.WZ (qrzAt A k).Z) cs ws).sum =
      (List.zipWith (fun c w => c * innerQRZ (d * d) w (qrzAt A k)) cs ws).sum := by
    intro cs ws
    induction cs generalizing ws with
    | nil => simp
    | cons c cs ih =>
      cases ws with
      | nil => simp
      | cons w ws =>
        simp only [List.zipWith_cons_cons, List.sum_cons]
        have hih := ih ws
        have hw : c * innerQRZ (d * d) w (qrzAt A k) =
            c * innerGrid (d * d) w.WQ (qrzAt A k).Q +
            c * innerGrid (d * d) w.WR (qrzAt A k).R +
            c * innerGrid (d * d) w.WZ (qrzAt A k).Z := by
          unfold innerQRZ; rw [Int.mul_add, Int.mul_add]
        rw [hw]
        omega
  rw [hcomb]
  apply zipWith_evalRec cert.coeffs (k + cert.k0) window
    (fun w => innerQRZ (d * d) w (qrzAt A k))
    (fun n => innerQRZ (d * d) W0 (qrzAt A n))
    hwin_len
  intro j hj
  rw [hwin_get j hj, checkWitnessedOrbit_sound A W0 cert.orbit horb_ok (cert.k0 + j) (by omega) k,
      show k + (cert.k0 + j) = k + cert.k0 + j by omega]

-- ----------------------------------------------------------------------------
-- Standard Target Energy Functionals (`dualE4State0` and `dualTotE4`)
-- ----------------------------------------------------------------------------

theorem evalOrbitAtZero_getD {d : Nat} (A : BinAuto d) (W0 : DualQRZ) (N j : Nat) (hj : j ≤ N) :
    (evalOrbitAtZero A W0 N).getD j 0 = innerQRZ (d * d) W0 (qrzAt A j) := by
  unfold evalOrbitAtZero
  have hlen : (dualOrbitPre (d * d) (packPreTable (buildPreTable A)) W0 N).length = N + 1 :=
    dualOrbitPre_len (d * d) (packPreTable (buildPreTable A)) W0 N
  have hlt : j < (dualOrbitPre (d * d) (packPreTable (buildPreTable A)) W0 N).length := by omega
  have hlt_map : j < ((dualOrbitPre (d * d) (packPreTable (buildPreTable A)) W0 N).map (evalDualAtZero A)).length := by
    simp [hlen]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_map, Option.getD_some, List.getElem_map]
  have hget := dualOrbitPre_getD (d * d) (packPreTable (buildPreTable A)) W0 N j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at hget
  rw [hget]
  change evalDualAtZero A (dualIter A W0 j) = _
  rw [← innerQRZ_qrzAt_zero, innerQRZ_dualIter, Nat.zero_add]

/-- Fast kernel-reducible evaluation of `E4State A 0 j` via `evalDualAtZero`. -/
theorem E4State_zero_eval {d : Nat} (A : BinAuto (d + 1)) (j : Nat) :
    E4State A 0 j = evalDualAtZero A (dualIter A (dualE4State0 (d + 1)) j) := by
  rw [← innerQRZ_qrzAt_zero, innerQRZ_dualIter, Nat.zero_add, innerQRZ_dualE4State0]

/-- Fast kernel-reducible evaluation of `totE4 A j` via `evalDualAtZero`. -/
theorem totE4_zero_eval {d : Nat} (A : BinAuto d) (j : Nat) :
    totE4 A j = evalDualAtZero A (dualIter A (dualTotE4 d) j) := by
  rw [← innerQRZ_qrzAt_zero, innerQRZ_dualIter, Nat.zero_add, innerQRZ_dualTotE4]

-- ============================================================================
-- Section 4: Four Concrete Infinite Theorems Discharged Through the Engine
-- ============================================================================

-- ----------------------------------------------------------------------------
-- THEOREM 2: Regular Paperfolding Exact L^4 Closed Form & 2-Adic Divisibility
-- ----------------------------------------------------------------------------

/-- Direct recurrence verification: `g(2n) = (-1)^n` and `g(2n+1) = g(n)` for all `n : Nat`. -/
theorem paperfolding_direct_rec (n : Nat) :
    paperfoldingAuto.eval 0 (2 * n) = (if n % 2 = 0 then 1 else -1) ∧
    paperfoldingAuto.eval 0 (2 * n + 1) = paperfoldingAuto.eval 0 n := by
  have hc : ∀ m, paperfoldingAuto.eval ⟨2, by omega⟩ m = 1 := by
    intro m; induction m using Nat.strongRecOn with
    | ind m ih =>
      by_cases hm : m = 0
      · subst hm; rw [BinAuto.eval_zero]; rfl
      · by_cases h2 : m % 2 = 0
        · rw [show m = 2 * (m / 2) by omega, BinAuto.eval_even]
          change 1 * paperfoldingAuto.eval ⟨2, by omega⟩ (m / 2) = 1
          rw [ih (m / 2) (by omega)]; rfl
        · rw [show m = 2 * (m / 2) + 1 by omega, BinAuto.eval_odd]
          change 1 * paperfoldingAuto.eval ⟨2, by omega⟩ (m / 2) = 1
          rw [ih (m / 2) (by omega)]; rfl
  constructor
  · rw [BinAuto.eval_even]
    change 1 * paperfoldingAuto.eval ⟨1, by omega⟩ n = _
    rw [Int.one_mul]
    by_cases hp : n % 2 = 0
    · have hn : n = 2 * (n / 2) := by omega
      rw [hn, BinAuto.eval_even]
      change 1 * paperfoldingAuto.eval ⟨2, by omega⟩ (n / 2) = _
      rw [hc]
      simp [show 2 * (n / 2) % 2 = 0 by omega]
    · have hn : n = 2 * (n / 2) + 1 := by omega
      rw [hn, BinAuto.eval_odd]
      change (-1) * paperfoldingAuto.eval ⟨2, by omega⟩ (n / 2) = _
      rw [hc]
      simp
  · rw [BinAuto.eval_odd]
    change 1 * paperfoldingAuto.eval 0 n = paperfoldingAuto.eval 0 n
    exact Int.one_mul _

private theorem pf_E4_val (j : Nat) (hj : j ≤ 8) :
    E4State paperfoldingAuto 0 j =
      ([1, 6, 20, 144, 600, 3560, 26056, 202888, 1607432] : List Int).getD j 0 := by
  rw [← innerQRZ_dualE4State0, ← evalOrbitAtZero_getD paperfoldingAuto (dualE4State0 3) 8 j hj, pf_base_orbit]

/-- **THEOREM 2 (Regular Paperfolding Exact `L^4` Energy Closed Form):**
    `∀ k ≥ 2, 21 * E4State paperfoldingAuto 0 k = 2 * 8^k + (63*k^2 - 693*k + 2317) * 2^k - 4440`. -/
theorem paperfolding_E4_closed_form (k : Nat) (hk : k ≥ 2) :
    21 * E4State paperfoldingAuto 0 k = pfFormula k := by
  have hrec := dual_krylov_sound paperfoldingAuto (dualE4State0 3) pfCert pfCert_valid
  simp only [innerQRZ_dualE4State0, pfCert, evalRecurrence, List.length_cons,
    List.length_nil] at hrec
  have hform_rec : ∀ n : Nat,
      pfFormula (n + 6) =
        (-192) * pfFormula n + 568 * pfFormula (n + 1) + (-660) * pfFormula (n + 2) +
        386 * pfFormula (n + 3) + (-119) * pfFormula (n + 4) + 18 * pfFormula (n + 5) := by
    intro n
    unfold pfFormula
    have h8_1 : (8 : Int) ^ (n + 1) = 8 * (8 : Int) ^ n := by rw [Int.pow_succ, Int.mul_comm]
    have h8_2 : (8 : Int) ^ (n + 2) = 64 * (8 : Int) ^ n := by rw [Int.pow_succ, h8_1]; omega
    have h8_3 : (8 : Int) ^ (n + 3) = 512 * (8 : Int) ^ n := by rw [Int.pow_succ, h8_2]; omega
    have h8_4 : (8 : Int) ^ (n + 4) = 4096 * (8 : Int) ^ n := by rw [Int.pow_succ, h8_3]; omega
    have h8_5 : (8 : Int) ^ (n + 5) = 32768 * (8 : Int) ^ n := by rw [Int.pow_succ, h8_4]; omega
    have h8_6 : (8 : Int) ^ (n + 6) = 262144 * (8 : Int) ^ n := by rw [Int.pow_succ, h8_5]; omega
    have h2_1 : (2 : Int) ^ (n + 1) = 2 * (2 : Int) ^ n := by rw [Int.pow_succ, Int.mul_comm]
    have h2_2 : (2 : Int) ^ (n + 2) = 4 * (2 : Int) ^ n := by rw [Int.pow_succ, h2_1]; omega
    have h2_3 : (2 : Int) ^ (n + 3) = 8 * (2 : Int) ^ n := by rw [Int.pow_succ, h2_2]; omega
    have h2_4 : (2 : Int) ^ (n + 4) = 16 * (2 : Int) ^ n := by rw [Int.pow_succ, h2_3]; omega
    have h2_5 : (2 : Int) ^ (n + 5) = 32 * (2 : Int) ^ n := by rw [Int.pow_succ, h2_4]; omega
    have h2_6 : (2 : Int) ^ (n + 6) = 64 * (2 : Int) ^ n := by rw [Int.pow_succ, h2_5]; omega
    rw [h8_6, h8_5, h8_4, h8_3, h8_2, h8_1, h2_6, h2_5, h2_4, h2_3, h2_2, h2_1]
    generalize (8 : Int) ^ n = a
    generalize (2 : Int) ^ n = b
    have hx1 : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
    have hx2 : ((n + 2 : Nat) : Int) = (n : Int) + 2 := by omega
    have hx3 : ((n + 3 : Nat) : Int) = (n : Int) + 3 := by omega
    have hx4 : ((n + 4 : Nat) : Int) = (n : Int) + 4 := by omega
    have hx5 : ((n + 5 : Nat) : Int) = (n : Int) + 5 := by omega
    have hx6 : ((n + 6 : Nat) : Int) = (n : Int) + 6 := by omega
    rw [hx1, hx2, hx3, hx4, hx5, hx6]
    generalize (n : Int) = x
    have hs1 : (x + 1) * (x + 1) = x * x + 2 * x + 1 := by rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
    have hs2 : (x + 2) * (x + 2) = x * x + 4 * x + 4 := by rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
    have hs3 : (x + 3) * (x + 3) = x * x + 6 * x + 9 := by rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
    have hs4 : (x + 4) * (x + 4) = x * x + 8 * x + 16 := by rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
    have hs5 : (x + 5) * (x + 5) = x * x + 10 * x + 25 := by rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
    have hs6 : (x + 6) * (x + 6) = x * x + 12 * x + 36 := by rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
    rw [Int.mul_assoc 63 (x + 1), hs1, Int.mul_assoc 63 (x + 2), hs2,
        Int.mul_assoc 63 (x + 3), hs3, Int.mul_assoc 63 (x + 4), hs4,
        Int.mul_assoc 63 (x + 5), hs5, Int.mul_assoc 63 (x + 6), hs6,
        Int.mul_assoc 63 x x]
    generalize x * x = x2
    have hd : ∀ (p q r c : Int), (p * x2 + q * x + r) * (c * b) =
        (p * c) * (x2 * b) + (q * c) * (x * b) + (r * c) * b := by
      intro p q r c
      rw [Int.add_mul, Int.add_mul]
      have hA : p * x2 * (c * b) = p * c * (x2 * b) := by
        rw [Int.mul_assoc, ← Int.mul_assoc x2 c b, Int.mul_comm x2 c, Int.mul_assoc, ← Int.mul_assoc]
      have hB : q * x * (c * b) = q * c * (x * b) := by
        rw [Int.mul_assoc, ← Int.mul_assoc x c b, Int.mul_comm x c, Int.mul_assoc, ← Int.mul_assoc]
      have hC : r * (c * b) = r * c * b := (Int.mul_assoc _ _ _).symm
      rw [hA, hB, hC]
    have hd1 : ∀ (p q r : Int), (p * x2 + q * x + r) * b = p * (x2 * b) + q * (x * b) + r * b := by
      intro p q r
      rw [Int.add_mul, Int.add_mul, Int.mul_assoc, Int.mul_assoc]
    have hcoeff6 : (63 * (x2 + 12 * x + 36) - 693 * (x + 6) + 2317) = 63 * x2 + 63 * x + 427 := by omega
    have hcoeff5 : (63 * (x2 + 10 * x + 25) - 693 * (x + 5) + 2317) = 63 * x2 + (-63) * x + 427 := by omega
    have hcoeff4 : (63 * (x2 + 8 * x + 16) - 693 * (x + 4) + 2317) = 63 * x2 + (-189) * x + 553 := by omega
    have hcoeff3 : (63 * (x2 + 6 * x + 9) - 693 * (x + 3) + 2317) = 63 * x2 + (-315) * x + 805 := by omega
    have hcoeff2 : (63 * (x2 + 4 * x + 4) - 693 * (x + 2) + 2317) = 63 * x2 + (-441) * x + 1183 := by omega
    have hcoeff1 : (63 * (x2 + 2 * x + 1) - 693 * (x + 1) + 2317) = 63 * x2 + (-567) * x + 1687 := by omega
    have hcoeff0 : (63 * x2 - 693 * x + 2317) = 63 * x2 + (-693) * x + 2317 := by omega
    rw [hcoeff6, hcoeff5, hcoeff4, hcoeff3, hcoeff2, hcoeff1, hcoeff0]
    rw [hd 63 63 427 64, hd 63 (-63) 427 32, hd 63 (-189) 553 16,
        hd 63 (-315) 805 8, hd 63 (-441) 1183 4, hd 63 (-567) 1687 2,
        hd1 63 (-693) 2317]
    omega
  have hb2 : 21 * E4State paperfoldingAuto 0 2 = pfFormula 2 := by rw [pf_E4_val 2 (by omega)]; decide
  have hb3 : 21 * E4State paperfoldingAuto 0 3 = pfFormula 3 := by rw [pf_E4_val 3 (by omega)]; decide
  have hb4 : 21 * E4State paperfoldingAuto 0 4 = pfFormula 4 := by rw [pf_E4_val 4 (by omega)]; decide
  have hb5 : 21 * E4State paperfoldingAuto 0 5 = pfFormula 5 := by rw [pf_E4_val 5 (by omega)]; decide
  have hb6 : 21 * E4State paperfoldingAuto 0 6 = pfFormula 6 := by rw [pf_E4_val 6 (by omega)]; decide
  have hb7 : 21 * E4State paperfoldingAuto 0 7 = pfFormula 7 := by rw [pf_E4_val 7 (by omega)]; decide
  have hb8 : 21 * E4State paperfoldingAuto 0 8 = pfFormula 8 := by rw [pf_E4_val 8 (by omega)]; decide
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 | 1 => omega
    | 2 => exact hb2
    | 3 => exact hb3
    | 4 => exact hb4
    | 5 => exact hb5
    | 6 => exact hb6
    | 7 => exact hb7
    | 8 => exact hb8
    | m + 9 =>
      have hm := hrec m
      have hfr := hform_rec (m + 3)
      have i0 := ih (m + 3) (by omega) (by omega)
      have i1 := ih (m + 4) (by omega) (by omega)
      have i2 := ih (m + 5) (by omega) (by omega)
      have i3 := ih (m + 6) (by omega) (by omega)
      have i4 := ih (m + 7) (by omega) (by omega)
      have i5 := ih (m + 8) (by omega) (by omega)
      have hidx : m + 3 + 6 = m + 9 := by omega
      have hidx1 : m + 3 + 1 = m + 4 := by omega
      have hidx2 : m + 3 + 2 = m + 5 := by omega
      have hidx3 : m + 3 + 3 = m + 6 := by omega
      have hidx4 : m + 3 + 4 = m + 7 := by omega
      have hidx5 : m + 3 + 5 = m + 8 := by omega
      rw [hidx, hidx1, hidx2, hidx3, hidx4, hidx5] at hfr
      have hsum_idx : m + 3 + (0 + 1 + 1 + 1 + 1 + 1 + 1) = m + 9 := by omega
      have h4' : m + 3 + 1 + 1 = m + 5 := by omega
      have h5' : m + 3 + 1 + 1 + 1 = m + 6 := by omega
      have h6' : m + 3 + 1 + 1 + 1 + 1 = m + 7 := by omega
      have h7' : m + 3 + 1 + 1 + 1 + 1 + 1 = m + 8 := by omega
      rw [hsum_idx, hidx1, h4', h5', h6', h7'] at hm
      omega

/-- **Corollary 2b (Exact 2-Adic Divisibility of Paperfolding `L^4` Energy):**
    `∀ k ≥ 3, 8 ∣ E4State paperfoldingAuto 0 k`. -/
theorem paperfolding_E4_div_8 (k : Nat) (hk : k ≥ 3) :
    (8 : Int) ∣ E4State paperfoldingAuto 0 k := by
  have h := paperfolding_E4_closed_form k (by omega)
  unfold pfFormula at h
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have h8 : (8 : Int) ^ (m + 3) = 8 * (8 : Int) ^ (m + 2) := by rw [Int.pow_succ, Int.mul_comm]
  have h2 : (2 : Int) ^ (m + 3) = 8 * (2 : Int) ^ m := by
    rw [Int.pow_succ, Int.pow_succ, Int.pow_succ]; omega
  rw [h8, h2] at h
  have h8dvd : (8 : Int) ∣ 21 * E4State paperfoldingAuto 0 (m + 3) := by
    refine ⟨2 * (8 : Int) ^ (m + 2) +
      (63 * ((m + 3 : Nat) : Int) * ((m + 3 : Nat) : Int) - 693 * ((m + 3 : Nat) : Int) + 2317) * (2 : Int) ^ m - 555, ?_⟩
    rw [h]
    have hmul : ∀ c : Int, c * (8 * (2 : Int) ^ m) = 8 * (c * (2 : Int) ^ m) := by
      intro c; rw [← Int.mul_assoc, Int.mul_comm c 8, Int.mul_assoc]
    rw [hmul]
    omega
  obtain ⟨q, hq⟩ := h8dvd
  refine ⟨5 * q - 13 * E4State paperfoldingAuto 0 (m + 3), ?_⟩
  omega

/-- **Sharpness Witnesses for Theorem 2:**
    Closed form breaks at `k = 0` (`21 ≠ -2121`) and `k = 1` (`126 ≠ -1050`);
    divisibility by `8` breaks at `k = 2` (`E4(2) = 20`, `¬(8 ∣ 20)`). -/
theorem paperfolding_sharpness :
    (21 * E4State paperfoldingAuto 0 0 ≠ pfFormula 0) ∧
    (21 * E4State paperfoldingAuto 0 1 ≠ pfFormula 1) ∧
    E4State paperfoldingAuto 0 2 = 20 ∧
    ¬((8 : Int) ∣ E4State paperfoldingAuto 0 2) := by
  have h0 : E4State paperfoldingAuto 0 0 = 1 := by rw [pf_E4_val 0 (by omega)]; decide
  have h1 : E4State paperfoldingAuto 0 1 = 6 := by rw [pf_E4_val 1 (by omega)]; decide
  have h2 : E4State paperfoldingAuto 0 2 = 20 := by rw [pf_E4_val 2 (by omega)]; decide
  rw [h0, h1, h2]
  refine ⟨by decide, by decide, rfl, ?_⟩
  intro ⟨q, hq⟩; omega

-- ----------------------------------------------------------------------------
-- THEOREM 3: Baum-Sweet Exact Degree-5 L^4 Recurrence & Period-3 Parity Law
-- ----------------------------------------------------------------------------

/-- Direct verification that `baumSweetAuto.eval 0` satisfies the classical Baum-Sweet
    recurrence: `b(0)=1`, `b(2n+1)=b(n)`, `b(4n)=b(n)`, `b(4n+2)=0` for ALL `n : Nat`. -/
theorem baumSweet_classical_rec (n : Nat) :
    baumSweetAuto.eval 0 0 = 1 ∧
    baumSweetAuto.eval 0 (2 * n + 1) = baumSweetAuto.eval 0 n ∧
    baumSweetAuto.eval 0 (4 * n) = baumSweetAuto.eval 0 n ∧
    baumSweetAuto.eval 0 (4 * n + 2) = 0 := by
  refine ⟨by rw [BinAuto.eval_zero]; rfl, ?_, ?_, ?_⟩
  · rw [BinAuto.eval_odd]; change 1 * baumSweetAuto.eval 0 n = _; exact Int.one_mul _
  · rw [show 4 * n = 2 * (2 * n) by omega, BinAuto.eval_even]
    change 1 * baumSweetAuto.eval ⟨1, by omega⟩ (2 * n) = _
    rw [BinAuto.eval_even]
    change 1 * (1 * baumSweetAuto.eval 0 n) = _; omega
  · rw [show 4 * n + 2 = 2 * (2 * n + 1) by omega, BinAuto.eval_even]
    change 1 * baumSweetAuto.eval ⟨1, by omega⟩ (2 * n + 1) = _
    rw [BinAuto.eval_odd]
    change 1 * (0 * baumSweetAuto.eval 0 n) = 0; simp

/-- **THEOREM 3a (Baum-Sweet Exact Degree-5 `L^4` Energy Recurrence, ∀ `k : Nat`):**
    `E4_BS(k+5) = 2*E4_BS(k+4) + 6*E4_BS(k+3) - E4_BS(k+2) - 4*E4_BS(k+1) + 2*E4_BS(k)`. -/
theorem baumSweet_E4_rec (k : Nat) :
    E4State baumSweetAuto 0 (k + 5) =
      2 * E4State baumSweetAuto 0 (k + 4) +
      6 * E4State baumSweetAuto 0 (k + 3) -
      E4State baumSweetAuto 0 (k + 2) -
      4 * E4State baumSweetAuto 0 (k + 1) +
      2 * E4State baumSweetAuto 0 k := by
  have hrec := dual_krylov_sound baumSweetAuto (dualE4State0 2) bsCert bsCert_valid
  simp only [innerQRZ_dualE4State0, bsCert, evalRecurrence, List.length_cons,
    List.length_nil, Nat.add_zero] at hrec
  let D (n : Nat) : Int :=
    E4State baumSweetAuto 0 (n + 5) -
    (2 * E4State baumSweetAuto 0 (n + 4) + 6 * E4State baumSweetAuto 0 (n + 3) -
     E4State baumSweetAuto 0 (n + 2) - 4 * E4State baumSweetAuto 0 (n + 1) +
     2 * E4State baumSweetAuto 0 n)
  have hD_step : ∀ n, D (n + 1) = -D n := by
    intro n
    have hn := hrec n
    dsimp [D]
    have h6 : n + (0 + 1 + 1 + 1 + 1 + 1 + 1) = n + 6 := by omega
    have h5 : n + 1 + 1 + 1 + 1 + 1 = n + 5 := by omega
    have h4 : n + 1 + 1 + 1 + 1 = n + 4 := by omega
    have h3 : n + 1 + 1 + 1 = n + 3 := by omega
    have h2 : n + 1 + 1 = n + 2 := by omega
    rw [h6, h5, h4, h3, h2] at hn
    have s5 : n + 1 + 5 = n + 6 := by omega
    have s4 : n + 1 + 4 = n + 5 := by omega
    have s3 : n + 1 + 3 = n + 4 := by omega
    have s2 : n + 1 + 2 = n + 3 := by omega
    have s1 : n + 1 + 1 = n + 2 := by omega
    rw [s5, s4, s3, s2, s1]
    omega
  have hD0 : D 0 = 0 := by
    dsimp [D]
    simp only [E4State_zero_eval]
    decide
  have hD_zero : ∀ n, D n = 0 := by
    intro n; induction n with
    | zero => exact hD0
    | succ n ih => rw [hD_step, ih]; rfl
  have hk := hD_zero k
  dsimp [D] at hk
  omega

/-- **THEOREM 3b (Baum-Sweet Exact Period-3 `L^4` Parity Law, ∀ `k : Nat`):**
    `E4_BS(k)` is even IF AND ONLY IF `k % 3 = 1`. -/
theorem baumSweet_E4_parity (k : Nat) :
    E4State baumSweetAuto 0 k % 2 = 0 ↔ k % 3 = 1 := by
  have hb0 : E4State baumSweetAuto 0 0 = 1 := by rw [E4State_zero_eval]; decide
  have hb1 : E4State baumSweetAuto 0 1 = 6 := by rw [E4State_zero_eval]; decide
  have hb2 : E4State baumSweetAuto 0 2 = 15 := by rw [E4State_zero_eval]; decide
  have hb3 : E4State baumSweetAuto 0 3 = 65 := by rw [E4State_zero_eval]; decide
  have hb4 : E4State baumSweetAuto 0 4 = 212 := by rw [E4State_zero_eval]; decide
  have hmod : ∀ n, E4State baumSweetAuto 0 (n + 3) % 2 = E4State baumSweetAuto 0 n % 2 := by
    intro n
    match n with
    | 0 => rw [hb0, hb3]; decide
    | 1 => rw [hb1, hb4]; decide
    | m + 2 =>
      have h := baumSweet_E4_rec m
      have h5 : m + 2 + 3 = m + 5 := by omega
      rw [h5, h]
      omega
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 => rw [hb0]; decide
    | 1 => rw [hb1]; decide
    | 2 => rw [hb2]; decide
    | m + 3 =>
      rw [hmod m]
      have ihm := ih m (by omega)
      have hm3 : (m + 3) % 3 = m % 3 := by omega
      rw [hm3]
      exact ihm

-- ----------------------------------------------------------------------------
-- THEOREM 4: Novel L=3 Complementary Quadruplets (`101 ^ 110` & `100 ^ 111`)
-- Sparse Recurrence, 4^(k+6) Law, Exact v2(T(k)) = k + 2, & Isospectrality
-- ----------------------------------------------------------------------------

theorem mask6Cert_valid : checkWitnessedDualCert mask6Auto (dualTotE4 4) mask6Cert = true := by
  decide

private theorem mask6TotOrbit_ok : checkWitnessedOrbit mask6Auto (dualTotE4 4) mask6TotOrbit = true := by
  have h := mask6Cert_valid
  unfold checkWitnessedDualCert at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

private theorem mask6_totE4_val (j : Nat) (hj : j ≤ 5) :
    totE4 mask6Auto j = ([4, 24, 80, 480, 1856, 6016] : List Int).getD j 0 := by
  match j with
  | 0 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask6Auto (dualTotE4 4) mask6TotOrbit mask6TotOrbit_ok 0 (by simp [mask6TotOrbit])]
    decide
  | 1 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask6Auto (dualTotE4 4) mask6TotOrbit mask6TotOrbit_ok 1 (by simp [mask6TotOrbit])]
    decide
  | 2 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask6Auto (dualTotE4 4) mask6TotOrbit mask6TotOrbit_ok 2 (by simp [mask6TotOrbit])]
    decide
  | 3 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask6Auto (dualTotE4 4) mask6TotOrbit mask6TotOrbit_ok 3 (by simp [mask6TotOrbit])]
    decide
  | 4 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask6Auto (dualTotE4 4) mask6TotOrbit mask6TotOrbit_ok 4 (by simp [mask6TotOrbit])]
    decide
  | 5 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask6Auto (dualTotE4 4) mask6TotOrbit mask6TotOrbit_ok 5 (by simp [mask6TotOrbit])]
    decide

private theorem mask9_totE4_val (j : Nat) (hj : j ≤ 5) :
    totE4 mask9Auto j = ([4, 24, 80, 480, 1856, 6016] : List Int).getD j 0 := by
  match j with
  | 0 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask9Auto (dualTotE4 4) mask9TotOrbit mask9TotOrbit_ok 0 (by simp [mask9TotOrbit])]
    decide
  | 1 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask9Auto (dualTotE4 4) mask9TotOrbit mask9TotOrbit_ok 1 (by simp [mask9TotOrbit])]
    decide
  | 2 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask9Auto (dualTotE4 4) mask9TotOrbit mask9TotOrbit_ok 2 (by simp [mask9TotOrbit])]
    decide
  | 3 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask9Auto (dualTotE4 4) mask9TotOrbit mask9TotOrbit_ok 3 (by simp [mask9TotOrbit])]
    decide
  | 4 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask9Auto (dualTotE4 4) mask9TotOrbit mask9TotOrbit_ok 4 (by simp [mask9TotOrbit])]
    decide
  | 5 =>
    rw [← innerQRZ_dualTotE4, witnessed_orbit_eval_zero mask9Auto (dualTotE4 4) mask9TotOrbit mask9TotOrbit_ok 5 (by simp [mask9TotOrbit])]
    decide

/-- **THEOREM 4a (Exact Sparse Degree-5 Recurrence for `totE4 mask6Auto`, ∀ `k : Nat`):**
    `T(k + 5) = 2 * T(k + 4) + 16 * T(k + 2) + 256 * T(k)`. -/
theorem mask6_totE4_rec (k : Nat) :
    totE4 mask6Auto (k + 5) =
      2 * totE4 mask6Auto (k + 4) + 16 * totE4 mask6Auto (k + 2) + 256 * totE4 mask6Auto k := by
  have hrec := witnessed_dual_krylov_sound mask6Auto (dualTotE4 4) mask6Cert mask6Cert_valid
  simp only [innerQRZ_dualTotE4, mask6Cert, evalRecurrence, List.length_cons, List.length_nil] at hrec
  cases k with
  | zero =>
    rw [mask6_totE4_val 5 (by omega), mask6_totE4_val 4 (by omega),
        mask6_totE4_val 2 (by omega), mask6_totE4_val 0 (by omega)]
    decide
  | succ m =>
    have hm := hrec m
    have h5 : m + 1 + (0 + 1 + 1 + 1 + 1 + 1) = m + 1 + 5 := by omega
    have h4 : m + 1 + 1 + 1 + 1 + 1 = m + 1 + 4 := by omega
    have h2 : m + 1 + 1 + 1 = m + 1 + 2 := by omega
    rw [h5, h4, h2] at hm
    omega

/-- **THEOREM 4b (Exact `4^(k+6)` Conservation Law, ∀ `k : Nat`):**
    `T(k+4) + 2*T(k+3) + 8*T(k+2) + 16*T(k+1) + 64*T(k) = 4^(k+6)`. -/
theorem mask6_totE4_conservation (k : Nat) :
    totE4 mask6Auto (k + 4) + 2 * totE4 mask6Auto (k + 3) + 8 * totE4 mask6Auto (k + 2) +
    16 * totE4 mask6Auto (k + 1) + 64 * totE4 mask6Auto k = (4 : Int) ^ (k + 6) := by
  induction k with
  | zero =>
    rw [mask6_totE4_val 4 (by omega), mask6_totE4_val 3 (by omega),
        mask6_totE4_val 2 (by omega), mask6_totE4_val 1 (by omega),
        mask6_totE4_val 0 (by omega)]
    decide
  | succ k ih =>
    have hrec := mask6_totE4_rec k
    have hpow : (4 : Int) ^ (k + 1 + 6) = 4 * (4 : Int) ^ (k + 6) := by
      have : k + 1 + 6 = (k + 6) + 1 := by omega
      rw [this, Int.pow_succ, Int.mul_comm]
    have s4 : k + 1 + 4 = k + 5 := by omega
    have s3 : k + 1 + 3 = k + 4 := by omega
    have s2 : k + 1 + 2 = k + 3 := by omega
    have s1 : k + 1 + 1 = k + 2 := by omega
    rw [s4, s3, s2, s1, hpow, ← ih]
    omega

/-- **THEOREM 4c (Exact 2-Adic Valuation `v_2(T(k)) = k + 2` for ALL `k : Nat`):**
    `2^(k+2) ∣ totE4 mask6Auto k ∧ ¬(2^(k+3) ∣ totE4 mask6Auto k)`. -/
theorem mask6_totE4_exact_v2 (k : Nat) :
    ((2 : Int) ^ (k + 2) ∣ totE4 mask6Auto k) ∧
    ¬((2 : Int) ^ (k + 3) ∣ totE4 mask6Auto k) := by
  have hstrong : ∀ n, ∃ u : Int, totE4 mask6Auto n = u * (2 : Int) ^ (n + 2) ∧ u % 2 = 1 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      match n with
      | 0 => refine ⟨1, ?_, by decide⟩; rw [mask6_totE4_val 0 (by omega)]; decide
      | 1 => refine ⟨3, ?_, by decide⟩; rw [mask6_totE4_val 1 (by omega)]; decide
      | 2 => refine ⟨5, ?_, by decide⟩; rw [mask6_totE4_val 2 (by omega)]; decide
      | 3 => refine ⟨15, ?_, by decide⟩; rw [mask6_totE4_val 3 (by omega)]; decide
      | 4 => refine ⟨29, ?_, by decide⟩; rw [mask6_totE4_val 4 (by omega)]; decide
      | m + 5 =>
        obtain ⟨u4, hu4, ho4⟩ := ih (m + 4) (by omega)
        obtain ⟨u2, hu2, ho2⟩ := ih (m + 2) (by omega)
        obtain ⟨u0, hu0, ho0⟩ := ih m (by omega)
        refine ⟨u4 + 2 * u2 + 8 * u0, ?_, by omega⟩
        rw [mask6_totE4_rec m, hu4, hu2, hu0]
        have p1 : (2 : Int) ^ (m + 5 + 2) = 2 * (2 : Int) ^ (m + 4 + 2) := by
          have : m + 5 + 2 = (m + 4 + 2) + 1 := by omega
          rw [this, Int.pow_succ, Int.mul_comm]
        have p2 : (2 : Int) ^ (m + 5 + 2) = 8 * (2 : Int) ^ (m + 2 + 2) := by
          have : m + 5 + 2 = (m + 2 + 2) + 3 := by omega
          rw [this, Int.pow_add, Int.mul_comm]; rfl
        have p3 : (2 : Int) ^ (m + 5 + 2) = 32 * (2 : Int) ^ (m + 2) := by
          have : m + 5 + 2 = (m + 2) + 5 := by omega
          rw [this, Int.pow_add, Int.mul_comm]; rfl
        rw [Int.add_mul, Int.add_mul]
        have t1 : u4 * (2 : Int) ^ (m + 5 + 2) = 2 * (u4 * (2 : Int) ^ (m + 4 + 2)) := by
          rw [p1, ← Int.mul_assoc, Int.mul_comm u4 2, Int.mul_assoc]
        have t2 : 2 * u2 * (2 : Int) ^ (m + 5 + 2) = 16 * (u2 * (2 : Int) ^ (m + 2 + 2)) := by
          rw [p2, Int.mul_assoc 2 u2, ← Int.mul_assoc u2 8, Int.mul_comm u2 8,
              Int.mul_assoc 8 u2, ← Int.mul_assoc 2 8]; rfl
        have t3 : 8 * u0 * (2 : Int) ^ (m + 5 + 2) = 256 * (u0 * (2 : Int) ^ (m + 2)) := by
          rw [p3, Int.mul_assoc 8 u0, ← Int.mul_assoc u0 32, Int.mul_comm u0 32,
              Int.mul_assoc 32 u0, ← Int.mul_assoc 8 32]; rfl
        rw [t1, t2, t3]
  obtain ⟨u, hu, hodd⟩ := hstrong k
  constructor
  · exact ⟨u, by rw [hu, Int.mul_comm]⟩
  · intro ⟨q, hq⟩
    have hp : (2 : Int) ^ (k + 3) = 2 * (2 : Int) ^ (k + 2) := by
      have : k + 3 = (k + 2) + 1 := by omega
      rw [this, Int.pow_succ, Int.mul_comm]
    have hpos : (2 : Int) ^ (k + 2) > 0 := by
      induction (k + 2) with
      | zero => decide
      | succ n ihn => rw [Int.pow_succ]; omega
    have heq : u * (2 : Int) ^ (k + 2) = (2 * q) * (2 : Int) ^ (k + 2) := by
      rw [← hu, hq, hp, Int.mul_assoc, Int.mul_comm ((2 : Int) ^ (k + 2)) q, ← Int.mul_assoc]
    have hu2q : u = 2 * q := Int.eq_of_mul_eq_mul_right (by omega) heq
    omega

/-- **THEOREM 4d (Non-Trivial Total-Energy Isospectrality + Individual-State Divergence):**
    `∀ k, totE4 mask6Auto k = totE4 mask9Auto k`, EVEN THOUGH `E4State mask6Auto 0 4 = 464 ≠ 528 = E4State mask9Auto 0 4`! -/
theorem mask6_mask9_isospectral_totE4 (k : Nat) :
    totE4 mask6Auto k = totE4 mask9Auto k := by
  have hrec9 := witnessed_dual_krylov_sound mask9Auto (dualTotE4 4) mask9Cert mask9Cert_valid
  simp only [innerQRZ_dualTotE4, mask9Cert, evalRecurrence, List.length_cons, List.length_nil] at hrec9
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 => rw [mask6_totE4_val 0 (by omega), mask9_totE4_val 0 (by omega)]
    | 1 => rw [mask6_totE4_val 1 (by omega), mask9_totE4_val 1 (by omega)]
    | 2 => rw [mask6_totE4_val 2 (by omega), mask9_totE4_val 2 (by omega)]
    | 3 => rw [mask6_totE4_val 3 (by omega), mask9_totE4_val 3 (by omega)]
    | 4 => rw [mask6_totE4_val 4 (by omega), mask9_totE4_val 4 (by omega)]
    | 5 => rw [mask6_totE4_val 5 (by omega), mask9_totE4_val 5 (by omega)]
    | m + 6 =>
      have h6 := mask6_totE4_rec (m + 1)
      have h9 := hrec9 m
      have hi0 := ih (m + 1) (by omega)
      have hi2 := ih (m + 3) (by omega)
      have hi4 := ih (m + 5) (by omega)
      have h5 : m + 1 + (0 + 1 + 1 + 1 + 1 + 1) = m + 6 := by omega
      have h4 : m + 1 + 1 + 1 + 1 + 1 = m + 5 := by omega
      have h2 : m + 1 + 1 + 1 = m + 3 := by omega
      rw [h5, h4, h2] at h9
      have s5 : m + 1 + 5 = m + 6 := by omega
      have s4 : m + 1 + 4 = m + 5 := by omega
      have s2 : m + 1 + 2 = m + 3 := by omega
      rw [s5, s4, s2] at h6
      omega

theorem mask6_mask9_individual_divergence :
    E4State mask6Auto 0 4 = 464 ∧ E4State mask9Auto 0 4 = 528 ∧
    E4State mask6Auto 0 4 ≠ E4State mask9Auto 0 4 := by
  have h6 : E4State mask6Auto 0 4 = 464 := by
    rw [← innerQRZ_dualE4State0, witnessed_orbit_eval_zero mask6Auto (dualE4State0 4) mask6E0Orbit mask6E0Orbit_ok 4 (by simp [mask6E0Orbit])]
    decide
  have h9 : E4State mask9Auto 0 4 = 528 := by
    rw [← innerQRZ_dualE4State0, witnessed_orbit_eval_zero mask9Auto (dualE4State0 4) mask9E0Orbit mask9E0Orbit_ok 4 (by simp [mask9E0Orbit])]
    decide
  rw [h6, h9]
  decide

-- ----------------------------------------------------------------------------
-- BENCHMARK COROLLARY: Rudin-Shapiro Exact Littlewood L^4 Formula in 10 Lines
-- ----------------------------------------------------------------------------

set_option maxRecDepth 4096 in
theorem rsCert_valid : checkDualCert rudinShapiroAuto (dualE4State0 2) rsCert = true := by
  decide

set_option maxRecDepth 4096 in
theorem rudinShapiro_E4_closed_form (k : Nat) (hk : k ≥ 1) :
    3 * E4State rudinShapiroAuto 0 k = (4 : Int) ^ (k + 1) - (-2 : Int) ^ k := by
  have hrec := dual_krylov_sound rudinShapiroAuto (dualE4State0 2) rsCert rsCert_valid
  simp only [innerQRZ_dualE4State0, rsCert, evalRecurrence, List.length_cons,
    List.length_nil] at hrec
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 => omega
    | 1 => rw [E4State_zero_eval]; decide
    | 2 => rw [E4State_zero_eval]; decide
    | 3 => rw [E4State_zero_eval]; decide
    | 4 => rw [E4State_zero_eval]; decide
    | m + 5 =>
      have hm := hrec m
      have h5 : m + 2 + (0 + 1 + 1 + 1) = m + 5 := by omega
      have h4 : m + 2 + 1 + 1 = m + 4 := by omega
      have h3 : m + 2 + 1 = m + 3 := by omega
      rw [h5, h4, h3] at hm
      have i2 := ih (m + 2) (by omega) (by omega)
      have i3 := ih (m + 3) (by omega) (by omega)
      have i4 := ih (m + 4) (by omega) (by omega)
      have p4_1 : (4 : Int) ^ (m + 4) = 4 * (4 : Int) ^ (m + 3) := by rw [Int.pow_succ, Int.mul_comm]
      have p4_2 : (4 : Int) ^ (m + 5) = 16 * (4 : Int) ^ (m + 3) := by rw [Int.pow_succ, p4_1]; omega
      have p4_3 : (4 : Int) ^ (m + 6) = 64 * (4 : Int) ^ (m + 3) := by rw [Int.pow_succ, p4_2]; omega
      have pm_1 : (-2 : Int) ^ (m + 3) = (-2) * (-2 : Int) ^ (m + 2) := by rw [Int.pow_succ, Int.mul_comm]
      have pm_2 : (-2 : Int) ^ (m + 4) = 4 * (-2 : Int) ^ (m + 2) := by rw [Int.pow_succ, pm_1]; omega
      have pm_3 : (-2 : Int) ^ (m + 5) = (-8) * (-2 : Int) ^ (m + 2) := by rw [Int.pow_succ, pm_2]; omega
      rw [show m + 5 + 1 = m + 6 by omega, p4_3, pm_3]
      rw [show m + 4 + 1 = m + 5 by omega, p4_2, pm_2] at i4
      rw [show m + 3 + 1 = m + 4 by omega, p4_1, pm_1] at i3
      rw [show m + 2 + 1 = m + 3 by omega] at i2
      omega

end PureSiliconAuto
