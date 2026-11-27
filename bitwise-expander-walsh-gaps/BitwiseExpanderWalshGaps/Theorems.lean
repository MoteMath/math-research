import BitwiseExpanderWalshGaps.Defs

namespace WalshAutomatonEngine
/-- Exact Integer Plancherel Identity over `BitVec k` (zero division, zero floats). -/
theorem wht_plancherel {k : Nat} (f g : BitVec k → Int) :
    bvSum (fun ξ => wht f ξ * wht g ξ) =
    ((2 ^ k : Nat) : Int) * bvSum (fun x => f x * g x) := by
  induction k with
  | zero =>
    simp [bvSum, wht, chi]
  | succ k ih =>
    simp only [bvSum, wht_cons_false, wht_cons_true]
    let f0 := fun x : BitVec k => f (BitVec.cons false x)
    let f1 := fun x : BitVec k => f (BitVec.cons true x)
    let g0 := fun x : BitVec k => g (BitVec.cons false x)
    let g1 := fun x : BitVec k => g (BitVec.cons true x)
    have hcomb : bvSum (fun ξ => (wht f0 ξ + wht f1 ξ) * (wht g0 ξ + wht g1 ξ)) +
                 bvSum (fun ξ => (wht f0 ξ - wht f1 ξ) * (wht g0 ξ - wht g1 ξ)) =
                 2 * bvSum (fun ξ => wht f0 ξ * wht g0 ξ) +
                 2 * bvSum (fun ξ => wht f1 ξ * wht g1 ξ) := by
      rw [← bvSum_add]
      have hpt : ∀ ξ : BitVec k,
          (wht f0 ξ + wht f1 ξ) * (wht g0 ξ + wht g1 ξ) +
          (wht f0 ξ - wht f1 ξ) * (wht g0 ξ - wht g1 ξ) =
          2 * (wht f0 ξ * wht g0 ξ) + 2 * (wht f1 ξ * wht g1 ξ) := by
        intro ξ
        rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub]
        omega
      rw [bvSum_congr hpt, bvSum_add, bvSum_mul_left, bvSum_mul_left]
    rw [hcomb, ih f0 g0, ih f1 g1]
    simp only [Nat.pow_succ]
    push_cast
    rw [Int.mul_add]
    have h2 : ∀ (n a b : Int), 2 * (n * a) + 2 * (n * b) = n * 2 * a + n * 2 * b := by
      intro n a b
      have t1 : 2 * (n * a) = n * 2 * a := by ac_rfl
      have t2 : 2 * (n * b) = n * 2 * b := by ac_rfl
      omega
    exact h2 _ _ _

/-- Exact Integer Parseval Identity over `BitVec k`. -/
theorem wht_parseval {k : Nat} (f : BitVec k → Int) :
    bvSum (fun ξ => wht f ξ * wht f ξ) =
    ((2 ^ k : Nat) : Int) * bvSum (fun x => f x * f x) :=
  wht_plancherel f f

-- ============================================================================
-- SECTION 3: Bitwise Cayley Graph Operators & Exact Spectral-Gap Lifters
-- ============================================================================

/-- Exact Integer Laplacian-Rayleigh Spectral Decomposition. -/
theorem dirichletForm_eq_wht {k : Nat} (P : BitVec k → Bool) (f : BitVec k → Int) :
    ((2 ^ k : Nat) : Int) * dirichletForm P f =
    bvSum (fun ξ => if ξ = 0 then 0 else (graphDeg P - graphEig P ξ) * (wht f ξ * wht f ξ)) := by
  have hdir : dirichletForm P f =
      graphDeg P * bvSum (fun x => f x * f x) - bvSum (fun x => f x * adjOp P f x) := by
    unfold dirichletForm laplacianOp
    have hpt : ∀ x, f x * (graphDeg P * f x - adjOp P f x) =
                    graphDeg P * (f x * f x) - f x * adjOp P f x := by
      intro x; rw [Int.mul_sub]; have : f x * (graphDeg P * f x) = graphDeg P * (f x * f x) := by ac_rfl
      rw [this]
    rw [bvSum_congr hpt, bvSum_sub, bvSum_mul_left]
  rw [hdir, Int.mul_sub]
  have h1 : ((2 ^ k : Nat) : Int) * (graphDeg P * bvSum (fun x => f x * f x)) =
            graphDeg P * bvSum (fun ξ => wht f ξ * wht f ξ) := by
    rw [wht_parseval]; ac_rfl
  have h2 : ((2 ^ k : Nat) : Int) * bvSum (fun x => f x * adjOp P f x) =
            bvSum (fun ξ => graphEig P ξ * (wht f ξ * wht f ξ)) := by
    rw [← wht_plancherel]
    apply bvSum_congr
    intro ξ
    rw [wht_adjOp]
    ac_rfl
  rw [h1, h2, ← bvSum_mul_left, ← bvSum_sub]
  have hsub : bvSum (fun ξ => graphDeg P * (wht f ξ * wht f ξ) - graphEig P ξ * (wht f ξ * wht f ξ)) =
              bvSum (fun ξ => (graphDeg P - graphEig P ξ) * (wht f ξ * wht f ξ)) := by
    apply bvSum_congr
    intro ξ
    rw [Int.sub_mul]
  rw [hsub, bvSum_split_zero]
  have hz : graphEig P (0 : BitVec k) = graphDeg P := graphEig_zero P
  rw [hz]
  simp

theorem intVariance_eq_wht {k : Nat} (f : BitVec k → Int) :
    intVariance f = bvSum (fun ξ => if ξ = 0 then 0 else wht f ξ * wht f ξ) := by
  unfold intVariance
  rw [← wht_parseval, bvSum_split_zero (fun ξ => wht f ξ * wht f ξ), wht_zero]
  omega

/-- Master Lifting Theorem 1 (Centered Variance-Form Poincaré Inequality — NO zero-sum hypothesis). -/
theorem variance_poincare_of_upper {k : Nat} (P : BitVec k → Bool) (γ : Int)
    (hgap : ∀ ξ : BitVec k, ξ ≠ 0 → γ ≤ graphDeg P - graphEig P ξ)
    (f : BitVec k → Int) :
    γ * intVariance f ≤ ((2 ^ k : Nat) : Int) * dirichletForm P f := by
  rw [intVariance_eq_wht, dirichletForm_eq_wht, ← bvSum_mul_left]
  apply bvSum_le
  intro ξ
  by_cases h0 : ξ = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    exact Int.mul_le_mul_of_nonneg_right (hgap ξ h0) (int_mul_self_nonneg _)

/-- Master Lifting Theorem 2 (Zero-Sum Exact Integer Rayleigh-Quotient Spectral Gap). -/
theorem rayleigh_gap_of_upper {k : Nat} (P : BitVec k → Bool) (γ : Int)
    (hgap : ∀ ξ : BitVec k, ξ ≠ 0 → γ ≤ graphDeg P - graphEig P ξ)
    (f : BitVec k → Int) (hzero : bvSum f = 0) :
    γ * bvSum (fun x => f x * f x) ≤ dirichletForm P f := by
  have hvar := variance_poincare_of_upper P γ hgap f
  unfold intVariance at hvar
  rw [hzero] at hvar
  simp only [Int.mul_zero, Int.sub_zero] at hvar
  have hpos : (0 : Int) < ((2 ^ k : Nat) : Int) := by
    exact_mod_cast Nat.two_pow_pos k
  have hmul : ((2 ^ k : Nat) : Int) * (γ * bvSum (fun x => f x * f x)) ≤
              ((2 ^ k : Nat) : Int) * dirichletForm P f := by
    have : ((2 ^ k : Nat) : Int) * (γ * bvSum (fun x => f x * f x)) =
           γ * (((2 ^ k : Nat) : Int) * bvSum (fun x => f x * f x)) := by ac_rfl
    rw [this]; exact hvar
  exact Int.le_of_mul_le_mul_left hmul hpos

/-- Master Lifting Theorem 3 (Two-Sided Operator-Norm Spectral Radius Bound). -/
theorem two_sided_energy_of_abs_bound {k : Nat} (P : BitVec k → Bool) (μ : Int)
    (hbound : ∀ ξ : BitVec k, ξ ≠ 0 → -μ ≤ graphEig P ξ ∧ graphEig P ξ ≤ μ)
    (f : BitVec k → Int) (hzero : bvSum f = 0) :
    bvSum (fun x => adjOp P f x * adjOp P f x) ≤ (μ * μ) * bvSum (fun x => f x * f x) := by
  have hpos : (0 : Int) < ((2 ^ k : Nat) : Int) := by
    exact_mod_cast Nat.two_pow_pos k
  suffices h : ((2 ^ k : Nat) : Int) * bvSum (fun x => adjOp P f x * adjOp P f x) ≤
               ((2 ^ k : Nat) : Int) * ((μ * μ) * bvSum (fun x => f x * f x)) by
    exact Int.le_of_mul_le_mul_left h hpos
  rw [← wht_parseval]
  have hrhs : ((2 ^ k : Nat) : Int) * ((μ * μ) * bvSum (fun x => f x * f x)) =
              (μ * μ) * bvSum (fun ξ => wht f ξ * wht f ξ) := by
    rw [wht_parseval]; ac_rfl
  rw [hrhs, ← bvSum_mul_left]
  apply bvSum_le
  intro ξ
  rw [wht_adjOp]
  by_cases h0 : ξ = 0
  · subst h0
    rw [wht_zero, hzero]
    simp
  · have ⟨hl, hu⟩ := hbound ξ h0
    have hsq : graphEig P ξ * graphEig P ξ ≤ μ * μ := by
      have h1 : 0 ≤ (μ - graphEig P ξ) * (μ + graphEig P ξ) :=
        Int.mul_nonneg (by omega) (by omega)
      have h2 : (μ - graphEig P ξ) * (μ + graphEig P ξ) =
                μ * μ - graphEig P ξ * graphEig P ξ := by
        rw [Int.sub_mul, Int.mul_add, Int.mul_add]
        have : graphEig P ξ * μ = μ * graphEig P ξ := Int.mul_comm _ _
        omega
      omega
    have hre : (graphEig P ξ * wht f ξ) * (graphEig P ξ * wht f ξ) =
               (graphEig P ξ * graphEig P ξ) * (wht f ξ * wht f ξ) := by ac_rfl
    rw [hre]
    exact Int.mul_le_mul_of_nonneg_right hsq (int_mul_self_nonneg _)

/-- Master Lifting Theorem 4 (Exact Integer Expander Mixing Lemma — zero reals, zero sqrt). -/
theorem expander_mixing_lemma_int {k : Nat} (P : BitVec k → Bool) (μ : Int)
    (hbound : ∀ ξ : BitVec k, ξ ≠ 0 → -μ ≤ graphEig P ξ ∧ graphEig P ξ ≤ μ)
    (S T : BitVec k → Bool) :
    let s := bvSum (indBool S)
    let t := bvSum (indBool T)
    let disc := ((2 ^ k : Nat) : Int) * edgesBetween P S T - graphDeg P * s * t
    disc * disc ≤ (μ * μ) * (s * (((2 ^ k : Nat) : Int) - s)) * (t * (((2 ^ k : Nat) : Int) - t)) := by
  intro s t disc
  have hdisc : disc = bvSum (fun ξ =>
      (if ξ = 0 then 0 else graphEig P ξ * wht (indBool S) ξ) *
      (if ξ = 0 then 0 else wht (indBool T) ξ)) := by
    have he : ((2 ^ k : Nat) : Int) * edgesBetween P S T =
              bvSum (fun ξ => wht (indBool S) ξ * (graphEig P ξ * wht (indBool T) ξ)) := by
      unfold edgesBetween
      rw [← wht_plancherel]
      apply bvSum_congr
      intro ξ
      rw [wht_adjOp]
    have hsplit := bvSum_split_zero (fun ξ => wht (indBool S) ξ * (graphEig P ξ * wht (indBool T) ξ))
    rw [wht_zero, wht_zero, graphEig_zero] at hsplit
    have h0term : s * (graphDeg P * t) = graphDeg P * s * t := by ac_rfl
    have hrem : bvSum (fun ξ => if ξ = 0 then 0 else wht (indBool S) ξ * (graphEig P ξ * wht (indBool T) ξ)) =
                bvSum (fun ξ =>
                  (if ξ = 0 then 0 else graphEig P ξ * wht (indBool S) ξ) *
                  (if ξ = 0 then 0 else wht (indBool T) ξ)) := by
      apply bvSum_congr
      intro ξ
      by_cases h0 : ξ = 0
      · simp [h0]
      · simp only [h0, ↓reduceIte]; ac_rfl
    dsimp only [disc]
    rw [he, hsplit, h0term, hrem]
    omega
  have hcs := bvSum_cauchy_schwarz
    (fun ξ => if ξ = 0 then 0 else graphEig P ξ * wht (indBool S) ξ)
    (fun ξ => if ξ = 0 then 0 else wht (indBool T) ξ)
  rw [← hdisc] at hcs
  have hvarBool : ∀ B : BitVec k → Bool,
      bvSum (fun ξ => (if ξ = 0 then 0 else wht (indBool B) ξ) *
                      (if ξ = 0 then 0 else wht (indBool B) ξ)) =
      bvSum (indBool B) * (((2 ^ k : Nat) : Int) - bvSum (indBool B)) := by
    intro B
    have hsq : ∀ ξ : BitVec k,
        (if ξ = 0 then 0 else wht (indBool B) ξ) * (if ξ = 0 then 0 else wht (indBool B) ξ) =
        if ξ = 0 then 0 else wht (indBool B) ξ * wht (indBool B) ξ := by
      intro ξ; split <;> simp
    rw [bvSum_congr hsq, ← intVariance_eq_wht]
    unfold intVariance
    have hboolsq : ∀ x : BitVec k, indBool B x * indBool B x = indBool B x := by
      intro x; unfold indBool; cases B x <;> rfl
    rw [bvSum_congr hboolsq, Int.mul_sub, Int.mul_comm (((2 ^ k : Nat) : Int))]
  have hT := hvarBool T
  have hS := hvarBool S
  have hboundS :
      bvSum (fun ξ => (if ξ = 0 then 0 else graphEig P ξ * wht (indBool S) ξ) *
                      (if ξ = 0 then 0 else graphEig P ξ * wht (indBool S) ξ)) ≤
      (μ * μ) * (s * (((2 ^ k : Nat) : Int) - s)) := by
    rw [← hS, ← bvSum_mul_left]
    apply bvSum_le
    intro ξ
    by_cases h0 : ξ = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      have ⟨hl, hu⟩ := hbound ξ h0
      have hsq : graphEig P ξ * graphEig P ξ ≤ μ * μ := by
        have h1 : 0 ≤ (μ - graphEig P ξ) * (μ + graphEig P ξ) :=
          Int.mul_nonneg (by omega) (by omega)
        have h2 : (μ - graphEig P ξ) * (μ + graphEig P ξ) =
                  μ * μ - graphEig P ξ * graphEig P ξ := by
          rw [Int.sub_mul, Int.mul_add, Int.mul_add]
          have : graphEig P ξ * μ = μ * graphEig P ξ := Int.mul_comm _ _
          omega
        omega
      have hre : (graphEig P ξ * wht (indBool S) ξ) * (graphEig P ξ * wht (indBool S) ξ) =
                 (graphEig P ξ * graphEig P ξ) * (wht (indBool S) ξ * wht (indBool S) ξ) := by
        ac_rfl
      rw [hre]
      exact Int.mul_le_mul_of_nonneg_right hsq (int_mul_self_nonneg _)
  have hTnn : 0 ≤ t * (((2 ^ k : Nat) : Int) - t) := by
    rw [← hT]
    apply bvSum_nonneg
    intro ξ
    exact int_mul_self_nonneg _
  rw [hT] at hcs
  exact Int.le_trans hcs (Int.mul_le_mul_of_nonneg_right hboundS hTnn)

-- ============================================================================
-- SECTION 4: Layer 2 — Finite Partial-Automaton → Infinite Transfer-Matrix Bridge
-- ============================================================================

/-- Generic Automaton Spectral-Gap Lifter:
    Any uniform upper bound `U` on `A.evalT ξ A.acceptVec A.init` (`ξ ≠ 0`) lifts immediately
    to BOTH the exact centered variance Poincaré inequality AND the zero-sum Rayleigh gap. -/
theorem automaton_rayleigh_gap_lifter {m : Nat} (A : BitAutomaton m) (k : Nat) (U : Int)
    (hU : ∀ ξ : BitVec k, ξ ≠ 0 → A.evalT ξ A.acceptVec A.init ≤ U)
    (f : BitVec k → Int) (hzero : bvSum f = 0) :
    (A.evalT (0 : BitVec k) A.acceptVec A.init - U) * bvSum (fun x => f x * f x) ≤
    dirichletForm A.looplessPred f := by
  apply rayleigh_gap_of_upper
  · intro ξ hne
    rw [graphGap_automaton_loopless]
    have hle := hU ξ hne
    omega
  · exact hzero

theorem automaton_variance_poincare_lifter {m : Nat} (A : BitAutomaton m) (k : Nat) (U : Int)
    (hU : ∀ ξ : BitVec k, ξ ≠ 0 → A.evalT ξ A.acceptVec A.init ≤ U)
    (f : BitVec k → Int) :
    (A.evalT (0 : BitVec k) A.acceptVec A.init - U) * intVariance f ≤
    ((2 ^ k : Nat) : Int) * dirichletForm A.looplessPred f := by
  apply variance_poincare_of_upper
  intro ξ hne
  rw [graphGap_automaton_loopless]
  have hle := hU ξ hne
  omega

-- ============================================================================
-- SECTION 5: Theorem A — Divisibility-by-3 Bitwise Cayley Super-Expander
-- ============================================================================

/-- **THEOREM A (Exact Tight Integer Spectral Gap of `G_mod3` ∀ k ≥ 1):**
    1. Universal Rayleigh spectral gap: `∀ f, ∑ f = 0 → mod3Gap k * ‖f‖² ≤ ⟨f, L f⟩`
    2. Centered variance Poincaré: `∀ f, mod3Gap k * Var(f) ≤ 2^k * ⟨f, L f⟩`
    3. Exact tightness witness: `χ_{allOnes k}` is non-zero, zero-sum, and attains exact equality! -/
theorem mod3_exact_spectral_gap (k : Nat) (hk : 1 ≤ k) :
    (∀ f : BitVec k → Int, mod3Gap k * intVariance f ≤ ((2 ^ k : Nat) : Int) * dirichletForm mod3Pred f) ∧
    (∀ f : BitVec k → Int, bvSum f = 0 → mod3Gap k * bvSum (fun x => f x * f x) ≤ dirichletForm mod3Pred f) ∧
    (bvSum (chi (BitVec.allOnes k)) = 0 ∧
     bvSum (fun x => chi (BitVec.allOnes k) x * chi (BitVec.allOnes k) x) = ((2 ^ k : Nat) : Int) ∧
     dirichletForm mod3Pred (chi (BitVec.allOnes k)) =
       mod3Gap k * bvSum (fun x => chi (BitVec.allOnes k) x * chi (BitVec.allOnes k) x)) := by
  have hcongrP : ∀ f : BitVec k → Int, dirichletForm mod3Pred f = dirichletForm mod3Aut.looplessPred f := by
    intro f
    unfold dirichletForm laplacianOp graphDeg adjOp indBool
    apply bvSum_congr; intro x
    have hd : bvSum (fun y : BitVec k => if mod3Pred y then (1 : Int) else 0) =
              bvSum (fun y : BitVec k => if mod3Aut.looplessPred y then (1 : Int) else 0) :=
      bvSum_congr (fun y => by rw [mod3Aut_looplessPred_eq])
    have ha : bvSum (fun y : BitVec k => (if mod3Pred (x ^^^ y) then (1 : Int) else 0) * f y) =
              bvSum (fun y : BitVec k => (if mod3Aut.looplessPred (x ^^^ y) then (1 : Int) else 0) * f y) :=
      bvSum_congr (fun y => by rw [mod3Aut_looplessPred_eq])
    rw [hd, ha]
  have hU : ∀ ξ : BitVec k, ξ ≠ 0 → mod3Aut.evalT ξ mod3Aut.acceptVec mod3Aut.init ≤ (mod3B k : Int) :=
    fun ξ hne => (mod3Aut_evalT_le_bound hne).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [hcongrP f]
    have h := automaton_variance_poincare_lifter mod3Aut k (mod3B k) hU f
    rw [mod3Aut_evalT_zero] at h
    exact h
  · intro f hz
    rw [hcongrP f]
    have h := automaton_rayleigh_gap_lifter mod3Aut k (mod3B k) hU f hz
    rw [mod3Aut_evalT_zero] at h
    exact h
  · exact character_zero_sum (bv_allOnes_ne_zero hk)
  · exact character_norm_sq (BitVec.allOnes k)
  · rw [hcongrP, character_rayleigh_tight, graphGap_automaton_loopless,
        mod3Aut_evalT_zero, mod3Aut_evalT_allOnes k hk]
    rfl

theorem mod3_expander_mixing_lemma {k : Nat} (hk : 4 ≤ k) (S T : BitVec k → Bool) :
    let s := bvSum (indBool S)
    let t := bvSum (indBool T)
    let μ := (mod3B k : Int) - 1
    let disc := ((2 ^ k : Nat) : Int) * edgesBetween mod3Pred S T - graphDeg (mod3Pred (k := k)) * s * t
    disc * disc ≤ (μ * μ) * (s * (((2 ^ k : Nat) : Int) - s)) * (t * (((2 ^ k : Nat) : Int) - t)) :=
  expander_mixing_lemma_int mod3Pred ((mod3B k : Int) - 1) (mod3_two_sided_bound hk) S T

-- ============================================================================
-- SECTION 6: Theorem B — Fibbinary (No-Adjacent-Ones) Bitwise Cayley Expander
-- ============================================================================

/-- **THEOREM B (Exact Tight Integer Spectral Gap of `G_fib` ∀ k ≥ 2):**
    1. Exact degree `d_k = F_{k+2} - 1` and exact second eigenvalue `λ_2 = L_{k-1} - 1`.
    2. Universal centered variance Poincaré & zero-sum Rayleigh gap `γ_fib(k) = 2 * F_{k-1}`.
    3. Exact tightness witness `χ_{2#k}` (interior bit 1!) attaining exact equality!
    4. Exact minimum eigenvalue `λ_min = -(F_{k-1} + 1)` achieved by `χ_{3#k}`! -/
theorem fib_exact_spectral_gap (k : Nat) (hk : 2 ≤ k) :
    (∀ f : BitVec k → Int, ((2 * fib (k - 1) : Nat) : Int) * intVariance f ≤
      ((2 ^ k : Nat) : Int) * dirichletForm fibPred f) ∧
    (∀ f : BitVec k → Int, bvSum f = 0 →
      ((2 * fib (k - 1) : Nat) : Int) * bvSum (fun x => f x * f x) ≤ dirichletForm fibPred f) ∧
    (bvSum (chi (fibWitnessMax k)) = 0 ∧
     bvSum (fun x => chi (fibWitnessMax k) x * chi (fibWitnessMax k) x) = ((2 ^ k : Nat) : Int) ∧
     dirichletForm fibPred (chi (fibWitnessMax k)) =
       ((2 * fib (k - 1) : Nat) : Int) *
         bvSum (fun x => chi (fibWitnessMax k) x * chi (fibWitnessMax k) x)) ∧
    (∀ ξ : BitVec k, -(fib (k - 1) : Int) - 1 ≤ graphEig fibPred ξ) ∧
    (graphEig fibPred (fibWitnessMin k) = -(fib (k - 1) : Int) - 1) := by
  have hcongrP : ∀ f : BitVec k → Int, dirichletForm fibPred f = dirichletForm fibAut.looplessPred f := by
    intro f
    unfold dirichletForm laplacianOp graphDeg adjOp indBool
    apply bvSum_congr; intro x
    have hd : bvSum (fun y : BitVec k => if fibPred y then (1 : Int) else 0) =
              bvSum (fun y : BitVec k => if fibAut.looplessPred y then (1 : Int) else 0) :=
      bvSum_congr (fun y => by rw [fibAut_looplessPred_eq])
    have ha : bvSum (fun y : BitVec k => (if fibPred (x ^^^ y) then (1 : Int) else 0) * f y) =
              bvSum (fun y : BitVec k => (if fibAut.looplessPred (x ^^^ y) then (1 : Int) else 0) * f y) :=
      bvSum_congr (fun y => by rw [fibAut_looplessPred_eq])
    rw [hd, ha]
  have hcongrEig : ∀ ξ : BitVec k, graphEig fibPred ξ = graphEig fibAut.looplessPred ξ := by
    intro ξ
    unfold graphEig wht indBool
    apply bvSum_congr; intro x; rw [fibAut_looplessPred_eq]
  cases k with
  | zero => omega
  | succ k1 =>
    cases k1 with
    | zero => omega
    | succ m =>
      have hU : ∀ ξ : BitVec (m + 2), ξ ≠ 0 →
          fibAut.evalT ξ fibAut.acceptVec fibAut.init ≤ (lucas (m + 1) : Int) :=
        fun ξ hne => (fibAut_lucas_cone m ξ hne).2.1
      have hgapEq : fibAut.evalT (0 : BitVec (m + 2)) fibAut.acceptVec fibAut.init - (lucas (m + 1) : Int) =
                    ((2 * fib (m + 1) : Nat) : Int) := by
        change fibAut.evalT (0 : BitVec (m + 2)) fibAut.acceptVec ⟨0, by decide⟩ - (lucas (m + 1) : Int) = _
        rw [(fibAut_evalT_zero (m + 2)).1]
        have hfl := fib_sub_lucas (m + 2) (by omega)
        have hs : m + 2 - 1 = m + 1 := by omega
        rw [hs] at hfl
        omega
      have hs : m + 1 + 1 - 1 = m + 1 := by omega
      rw [hs]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro f
        rw [hcongrP f]
        have h := automaton_variance_poincare_lifter fibAut (m + 2) (lucas (m + 1)) hU f
        rw [hgapEq] at h
        exact h
      · intro f hz
        rw [hcongrP f]
        have h := automaton_rayleigh_gap_lifter fibAut (m + 2) (lucas (m + 1)) hU f hz
        rw [hgapEq] at h
        exact h
      · refine ⟨character_zero_sum (fibWitnessMax_ne_zero (m + 2) (by omega)),
                character_norm_sq (fibWitnessMax (m + 2)), ?_⟩
        rw [hcongrP, character_rayleigh_tight, graphGap_automaton_loopless]
        have hw := (fibAut_evalT_witnessMax (m + 2) (by omega)).1
        have hs2 : m + 2 - 1 = m + 1 := by omega
        rw [hs2] at hw
        change (fibAut.evalT (0 : BitVec (m + 2)) fibAut.acceptVec fibAut.init -
                fibAut.evalT (fibWitnessMax (m + 2)) fibAut.acceptVec ⟨0, by decide⟩) * _ = _
        rw [hw, hgapEq]
      · intro ξ
        rw [hcongrEig ξ, graphEig_automaton_loopless, fibAut_accepts_eq]
        have h0 : ((0 : BitVec (m + 2)) &&& ((0 : BitVec (m + 2)) >>> 1) == 0) = true := by simp
        rw [h0]
        simp only [↓reduceIte]
        have hlo : -(fib (m + 1) : Int) ≤ fibAut.evalT ξ fibAut.acceptVec fibAut.init :=
          (fibAut_lower_polytope m ξ).2.2.1
        omega
      · rw [hcongrEig, graphEig_automaton_loopless, fibAut_accepts_eq]
        have h0 : ((0 : BitVec (m + 2)) &&& ((0 : BitVec (m + 2)) >>> 1) == 0) = true := by simp
        rw [h0]
        simp only [↓reduceIte]
        have hmin : fibAut.evalT (fibWitnessMin (m + 2)) fibAut.acceptVec fibAut.init =
                    -(fib (m + 1) : Int) := by
          have h := (fibAut_evalT_witnessMin (m + 2) (by omega)).1
          have hs2 : m + 2 - 1 = m + 1 := by omega
          rw [hs2] at h; exact h
        rw [hmin]

theorem fib_expander_mixing_lemma {k : Nat} (hk : 3 ≤ k) (S T : BitVec k → Bool) :
    let s := bvSum (indBool S)
    let t := bvSum (indBool T)
    let μ := (lucas (k - 1) : Int) - 1
    let disc := ((2 ^ k : Nat) : Int) * edgesBetween fibPred S T - graphDeg (fibPred (k := k)) * s * t
    disc * disc ≤ (μ * μ) * (s * (((2 ^ k : Nat) : Int) - s)) * (t * (((2 ^ k : Nat) : Int) - t)) :=
  expander_mixing_lemma_int fibPred ((lucas (k - 1) : Int) - 1) (fib_two_sided_bound hk) S T

-- ============================================================================
-- SECTION 7: Theorem C — Circular Fibbinary Edge-Sparse Dominance (`G_cfib`)
-- ============================================================================

/-- **THEOREM C (Circular Fibbinary Edge-Sparse Dominance & Fibonacci–Lucas Spectral Duality, ∀ k ≥ 3):**
    1. Strictly sparser spanning subgraph of `G_fib`: `deg(G_cfib) + F_{k-2} = deg(G_fib)` (strictly fewer edges!).
    2. Exact degree `L_k - 1` and exact second eigenvalue `F_k - 1`.
    3. IDENTICAL exact tight integer spectral gap `2 * F_{k-1}` to `G_fib`!
    4. Exact tightness witness `χ_{cfibWitness k}` attaining exact equality! -/
theorem cfib_exact_spectral_gap_and_dominance (k : Nat) (hk : 3 ≤ k) :
    (graphDeg (cfibPred (k := k)) + (fib (k - 2) : Int) = graphDeg (fibPred (k := k))) ∧
    (∀ x : BitVec k, cfibPred x = true → fibPred x = true) ∧
    (∀ f : BitVec k → Int, ((2 * fib (k - 1) : Nat) : Int) * intVariance f ≤
      ((2 ^ k : Nat) : Int) * dirichletForm cfibPred f) ∧
    (∀ f : BitVec k → Int, bvSum f = 0 →
      ((2 * fib (k - 1) : Nat) : Int) * bvSum (fun x => f x * f x) ≤ dirichletForm cfibPred f) ∧
    (bvSum (chi (cfibWitness k (by omega))) = 0 ∧
     bvSum (fun x => chi (cfibWitness k (by omega)) x * chi (cfibWitness k (by omega)) x) = ((2 ^ k : Nat) : Int) ∧
     dirichletForm cfibPred (chi (cfibWitness k (by omega))) =
       ((2 * fib (k - 1) : Nat) : Int) *
         bvSum (fun x => chi (cfibWitness k (by omega)) x * chi (cfibWitness k (by omega)) x)) := by
  have hgapVal : (lucas k : Int) - (fib k : Int) = ((2 * fib (k - 1) : Nat) : Int) := by
    cases k with
    | zero => omega
    | succ k1 =>
      cases k1 with
      | zero => omega
      | succ k2 =>
        have hl2 : lucas (k2 + 1 + 1) = fib (k2 + 1) + fib (k2 + 3) := rfl
        have hf3 : fib (k2 + 3) = fib (k2 + 2) + fib (k2 + 1) := rfl
        have hf2 : fib (k2 + 1 + 1) = fib (k2 + 2) := rfl
        have hs : k2 + 1 + 1 - 1 = k2 + 1 := by omega
        rw [hl2, hf3, hf2, hs]
        omega
  have hgapBound : ∀ ξ : BitVec k, ξ ≠ 0 →
      ((2 * fib (k - 1) : Nat) : Int) ≤ graphDeg (cfibPred (k := k)) - graphEig cfibPred ξ := by
    intro ξ hne
    rw [cfibPred_deg k (by omega), graphEig_cfibPred]
    have hup := cfibAccepts_wht_upper hk ξ hne
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [cfibPred_deg k (by omega), fibPred_deg k]
    cases k with
    | zero => omega
    | succ k1 =>
      cases k1 with
      | zero => omega
      | succ m =>
        have hl2 : lucas (m + 1 + 1) = fib (m + 1) + fib (m + 3) := rfl
        have hf4 : fib (m + 1 + 1 + 2) = fib (m + 3) + fib (m + 2) := rfl
        have hf2 : fib (m + 2) = fib (m + 1) + fib m := rfl
        have hs : m + 1 + 1 - 2 = m := by omega
        rw [hl2, hf4, hf2, hs]
        omega
  · intro x hx
    unfold cfibPred cfibAccepts at hx
    unfold fibPred
    have h1 : (x != 0) = true ∧ ((x &&& rotl1 x) == 0) = true := Bool.and_eq_true_iff.mp hx
    have h2 : (x &&& rotl1 x) = 0 := beq_iff_eq.mp h1.2
    cases k with
    | zero => omega
    | succ k1 =>
      rw [bv_eq_cons_msb_truncate x] at h2 ⊢
      have hlin := ((cfibAccepts_eq_fib_and_ends (by omega) x.msb (x.truncate k1)).mp h2).1
      rw [← bv_eq_cons_msb_truncate x] at hlin ⊢
      rw [h1.1, beq_iff_eq.mpr hlin]
      rfl
  · exact variance_poincare_of_upper cfibPred ((2 * fib (k - 1) : Nat) : Int) hgapBound
  · exact rayleigh_gap_of_upper cfibPred ((2 * fib (k - 1) : Nat) : Int) hgapBound
  · refine ⟨character_zero_sum (cfibWitness_ne_zero k (by omega)),
            character_norm_sq (cfibWitness k (by omega)), ?_⟩
    rw [character_rayleigh_tight, cfibPred_deg k (by omega), graphEig_cfibPred,
        cfibAccepts_wht_witness k (by omega)]
    have : ((lucas k : Int) - 1) - ((fib k : Int) - 1) = (lucas k : Int) - (fib k : Int) := by omega
    rw [this, hgapVal]

-- ============================================================================
-- SECTION 8: Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples
-- ============================================================================

-- Non-Vacuity Witness 1: `G_mod3` at `k = 5` (first connected width: 32 vertices, deg 10, exact gap 2)
theorem witness_mod3_k5 :
    graphDeg (mod3Pred (k := 5)) = 10 ∧
    mod3Gap 5 = 2 ∧
    0 < mod3Gap 5 ∧
    dirichletForm (mod3Pred (k := 5)) (chi (BitVec.allOnes 5)) = 64 := by
  have h1 : graphDeg (mod3Pred (k := 5)) = 10 := by rw [mod3Pred_deg]; rfl
  have h2 : mod3Gap 5 = 2 := by decide
  have h3 : 0 < mod3Gap 5 := mod3_strict_gap_pos 5 (by decide)
  have h4 := (mod3_exact_spectral_gap 5 (by decide)).2.2.2.2
  rw [character_norm_sq, h2] at h4
  exact ⟨h1, h2, h3, h4⟩

-- Non-Vacuity Witness 2: `G_fib` at `k = 4` (16 vertices, deg 7, gap 4, l2 = 3, lmin = -3)
theorem witness_fib_k4 :
    graphDeg (fibPred (k := 4)) = 7 ∧
    graphEig (fibPred (k := 4)) (fibWitnessMax 4) = 3 ∧
    graphEig (fibPred (k := 4)) (fibWitnessMin 4) = -3 ∧
    dirichletForm (fibPred (k := 4)) (chi (fibWitnessMax 4)) = 64 := by
  have h1 : graphDeg (fibPred (k := 4)) = 7 := by rw [fibPred_deg]; rfl
  have h3 : graphEig (fibPred (k := 4)) (fibWitnessMin 4) = -3 := by
    have := (fib_exact_spectral_gap 4 (by decide)).2.2.2.2
    exact this
  have h4 := (fib_exact_spectral_gap 4 (by decide)).2.2.1.2.2
  rw [character_norm_sq] at h4
  have h2 : graphEig (fibPred (k := 4)) (fibWitnessMax 4) = 3 := by
    have hrt := character_rayleigh_tight (fibPred (k := 4)) (fibWitnessMax 4)
    rw [character_norm_sq, h1, h4] at hrt
    have : ((2 * fib (4 - 1) : Nat) : Int) * ((2 ^ 4 : Nat) : Int) = 64 := by decide
    have : ((2 ^ 4 : Nat) : Int) = 16 := by decide
    omega
  exact ⟨h1, h2, h3, h4⟩

-- Non-Vacuity Witness 3: `G_cfib` vs `G_fib` at `k = 5` (strictly fewer edges: deg 10 < 12, SAME exact gap 6!)
theorem witness_cfib_dominance_k5 :
    graphDeg (cfibPred (k := 5)) = 10 ∧
    graphDeg (fibPred (k := 5)) = 12 ∧
    dirichletForm (cfibPred (k := 5)) (chi (cfibWitness 5 (by decide))) = 192 ∧
    dirichletForm (fibPred (k := 5)) (chi (fibWitnessMax 5)) = 192 := by
  have h1 : graphDeg (cfibPred (k := 5)) = 10 := by rw [cfibPred_deg 5 (by decide)]; rfl
  have h2 : graphDeg (fibPred (k := 5)) = 12 := by rw [fibPred_deg 5]; rfl
  have h3 := (cfib_exact_spectral_gap_and_dominance 5 (by decide)).2.2.2.2.2.2
  have h4 := (fib_exact_spectral_gap 5 (by decide)).2.2.1.2.2
  rw [character_norm_sq] at h3 h4
  exact ⟨h1, h2, h3, h4⟩

-- Sharpness Counterexample 1: `G_mod3` at `k = 4` has spectral gap 0 (disconnected!),
-- proving `k ≥ 5` in `mod3_strict_gap_pos` is SHARP!
theorem sharpness_mod3_k4_disconnected :
    mod3Gap 4 = 0 ∧
    bvSum (chi (BitVec.allOnes 4)) = 0 ∧
    bvSum (fun x => chi (BitVec.allOnes 4) x * chi (BitVec.allOnes 4) x) = 16 ∧
    dirichletForm (mod3Pred (k := 4)) (chi (BitVec.allOnes 4)) = 0 := by
  have hgap : mod3Gap 4 = 0 := by decide
  have ⟨_, _, hz, hn, hd⟩ := mod3_exact_spectral_gap 4 (by decide)
  rw [hgap] at hd
  simp only [Int.zero_mul] at hd
  exact ⟨hgap, hz, hn, hd⟩

-- Sharpness Counterexample 2: Even modulus (`mod2Pred`: `x ≠ 0 ∧ x.toNat % 2 = 0`)
-- is ALWAYS disconnected (`gap = 0`) for ALL `k ≥ 1`, proving odd modulus is essential!
theorem sharpness_mod2_always_disconnected (k : Nat) (hk : 1 ≤ k) :
    let ξ : BitVec k := BitVec.ofNat k 1
    bvSum (chi ξ) = 0 ∧
    bvSum (fun x => chi ξ x * chi ξ x) = ((2 ^ k : Nat) : Int) ∧
    dirichletForm mod2Pred (chi ξ) = 0 := by
  intro ξ
  have hne : ξ ≠ 0 := by
    intro hc
    have hnat := congrArg BitVec.toNat hc
    simp only [ξ, BitVec.toNat_ofNat] at hnat
    have h0 : (0 : BitVec k).toNat = 0 := by simp
    rw [h0] at hnat
    have h1lt : 1 < 2 ^ k := by
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      omega
    rw [Nat.mod_eq_of_lt h1lt] at hnat
    omega
  have hchi_one : ∀ x : BitVec k, chi ξ x = if x.toNat % 2 = 1 then -1 else 1 := by
    intro x
    -- Prove by induction on `k` that `chi (BitVec.ofNat k 1) x = sgn (x[0])`!
    have aux : ∀ {n : Nat} (hn : 1 ≤ n) (y : BitVec n),
        chi (BitVec.ofNat n 1) y = if y.toNat % 2 = 1 then -1 else 1 := by
      intro n
      induction n with
      | zero => intro hn; omega
      | succ n ih =>
        intro _ y
        cases n with
        | zero =>
          rw [bv_eq_cons_msb_truncate y]
          have h0 : y.truncate 0 = 0 := bv_zero_width_eq _
          rw [h0]
          cases y.msb <;> decide
        | succ m =>
          conv => lhs; unfold chi
          have hmsb : (BitVec.ofNat (m + 2) 1).msb = false := by
            apply bv_ofNat_msb_lt
            have : 2 ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
            omega
          rw [hmsb, Bool.false_and, sgn_false, Int.one_mul, bv_ofNat_truncate, ih (by omega)]
          have htoNat : y.toNat % 2 = (y.truncate (m + 1)).toNat % 2 := by
            rw [bv_eq_cons_msb_truncate y, bv_cons_toNat]
            have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
            cases y.msb <;> simp <;> omega
          rw [htoNat]
    exact aux hk x
  have heig : graphEig mod2Pred ξ = graphDeg (mod2Pred (k := k)) := by
    unfold graphEig graphDeg wht
    apply bvSum_congr
    intro x
    unfold indBool mod2Pred
    cases hx : (x != 0 && x.toNat % 2 == 0)
    · simp
    · have hpair := Bool.and_eq_true_iff.mp hx
      have heven : x.toNat % 2 = 0 := beq_iff_eq.mp hpair.2
      rw [hchi_one x]
      simp [heven]
  refine ⟨character_zero_sum hne, character_norm_sq ξ, ?_⟩
  rw [character_rayleigh_tight, heig]
  simp

-- Sharpness Counterexample 3: For `G_fib` at `k = 3`, the naive boundary LSB character `1#3`
-- is STRICTLY suboptimal (`graphEig 1#3 = 0 < 2 = graphEig 2#3`), proving interior bit 1 is needed!
theorem sharpness_fib_lsb_suboptimal_k3 :
    graphEig (fibPred (k := 3)) (BitVec.ofNat 3 1) = 0 ∧
    graphEig (fibPred (k := 3)) (fibWitnessMax 3) = 2 ∧
    graphEig (fibPred (k := 3)) (BitVec.ofNat 3 1) < graphEig (fibPred (k := 3)) (fibWitnessMax 3) := by
  decide

-- Sharpness Counterexample 4: For `G_fib` at `k = 2`, `|λ_min| = 2 > 0 = λ_2`,
-- proving `k ≥ 3` in `fib_two_sided_bound` and `fib_expander_mixing_lemma` is SHARP!
theorem sharpness_fib_k2_twosided :
    graphEig (fibPred (k := 2)) (fibWitnessMax 2) = 0 ∧
    graphEig (fibPred (k := 2)) (fibWitnessMin 2) = -2 ∧
    graphEig (fibPred (k := 2)) (fibWitnessMin 2) < -graphEig (fibPred (k := 2)) (fibWitnessMax 2) := by
  decide

-- Sharpness Counterexample 5: Concrete integer Expander Mixing Lemma witness on `G_mod3` (`k = 5`)
-- verifying non-vacuity of `mod3_expander_mixing_lemma` on concrete nontrivial subsets `S, T`.
theorem witness_mod3_eml_k5 :
    let S : BitVec 5 → Bool := fun x => x.toNat < 11
    let T : BitVec 5 → Bool := fun x => x.toNat % 2 == 1
    let s := bvSum (indBool S)
    let t := bvSum (indBool T)
    let disc := ((2 ^ 5 : Nat) : Int) * edgesBetween mod3Pred S T - graphDeg (mod3Pred (k := 5)) * s * t
    s = 11 ∧ t = 16 ∧
    disc * disc ≤ (8 * 8) * (s * (32 - s)) * (t * (32 - t)) := by
  refine ⟨by decide, by decide, ?_⟩
  exact mod3_expander_mixing_lemma (k := 5) (by decide) (fun x => x.toNat < 11) (fun x => x.toNat % 2 == 1)

end WalshAutomatonEngine
