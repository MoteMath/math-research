/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSerialLutDag.FinSum

/-!
# Binary Sign-Folded LUT DAG Lower Bound & Optimal `g = 4` Circuits (`BitSerialLutDag.BinaryDag`)

Proves:
1. `binary_lut_dag_lower_bound_exact`:
   - Universal linearity `evalWireVal dag x m = dotInt (evalWireCoeff dag m) x`.
   - Universal support-doubling depth bound `supportSize (evalWireCoeff dag m) ≤ 2 ^ wireDepth dag m`,
     implying `ceilLog2 g ≤ wireDepth dag m` for any full-support target wire.
   - Universal connected-component coloring gate-count lower bound
     `2^(g-1) + g - 2 ≤ dag.gates.length` for every `g ≥ 2` and every 2-input linear DAG
     computing all `2^(g-1)` sign-canonical binary targets (even with arbitrary `Int` scalars).
   - Exact specializations for `g = 2, 3, 4, 5` (`2, 5, 10, 19` ops; `1, 2, 2, 3` depth).
2. `tmac_depth2_optimal_12_vs_14_circuit`:
   - Exact validity, gate-class membership, op count, critical-path depth, and symbolic
     soundness/completeness (for all `x : Fin 4 → Int`) of:
     * `balancedTreeG4Dag` (`12 ops, depth 2`, pure `{+, -}`),
     * `naiveTmacG4Dag` (`14 ops, depth 3`, pure `{+, -}`),
     * `rdna3MidG4Dag` (`11 ops, depth 3`, RDNA 3 `V_ADD_LSHL`),
     * `rdna3MinOpsG4Dag` (`10 ops, depth 4`, RDNA 3 `V_ADD_LSHL`, meets `binaryLowerBound 4 = 10`).
   - Strict dominance of `balancedTreeG4Dag` over `naiveTmacG4Dag` (`-1/7` ops, `-1/3` depth).
-/

namespace BitSerialLutDag

/-! ## Structural-Fuel Unfolding Lemmas -/

theorem evalWireCoeffAux_fuel_indep {g : Nat} (dag : LinearDag g) :
    ∀ (f1 f2 m : Nat), m ≤ f1 → m ≤ f2 →
      evalWireCoeffAux dag f1 m = evalWireCoeffAux dag f2 m
  | 0, 0, _, _, _ => rfl
  | 0, f2 + 1, m, h1, _ => by
    have hm0 : m = 0 := by omega
    subst hm0
    unfold evalWireCoeffAux
    by_cases h0g : 0 < g
    · simp [h0g]
    · simp only [h0g, ↓reduceIte]
      cases dag.gates[0 - g]? with
      | none => rfl
      | some gate =>
        simp
  | f1 + 1, 0, m, _, h2 => by
    have hm0 : m = 0 := by omega
    subst hm0
    unfold evalWireCoeffAux
    by_cases h0g : 0 < g
    · simp [h0g]
    · simp only [h0g, ↓reduceIte]
      cases dag.gates[0 - g]? with
      | none => rfl
      | some gate =>
        simp
  | f1 + 1, f2 + 1, m, h1, h2 => by
    unfold evalWireCoeffAux
    by_cases hmg : m < g
    · simp [hmg]
    · simp only [hmg, ↓reduceIte]
      cases dag.gates[m - g]? with
      | none => rfl
      | some gate =>
        by_cases huv : gate.u < m ∧ gate.v < m
        · simp only [huv, and_self, ↓reduceIte]
          rw [evalWireCoeffAux_fuel_indep dag f1 f2 gate.u (by omega) (by omega),
              evalWireCoeffAux_fuel_indep dag f1 f2 gate.v (by omega) (by omega)]
        · simp [huv]

theorem evalWireCoeff_unfold {g : Nat} (dag : LinearDag g) (m : Nat) :
    evalWireCoeff dag m =
      if m < g then unitVec g m
      else match dag.gates[m - g]? with
        | none => fun _ => 0
        | some gate =>
          if gate.u < m ∧ gate.v < m then
            fun j => gate.c1 * evalWireCoeff dag gate.u j + gate.c2 * evalWireCoeff dag gate.v j
          else fun _ => 0 := by
  change evalWireCoeffAux dag m m = _
  rw [evalWireCoeffAux_fuel_indep dag m (m + 1) m (Nat.le_refl m) (Nat.le_succ m)]
  rw [evalWireCoeffAux]
  by_cases hmg : m < g
  · simp [hmg]
  · simp only [hmg, ↓reduceIte]
    cases dag.gates[m - g]? with
    | none => rfl
    | some gate =>
      by_cases huv : gate.u < m ∧ gate.v < m
      · simp only [huv, and_self, ↓reduceIte]
        funext j
        rw [evalWireCoeffAux_fuel_indep dag m gate.u gate.u (by omega) (Nat.le_refl _),
            evalWireCoeffAux_fuel_indep dag m gate.v gate.v (by omega) (Nat.le_refl _)]
        rfl
      · simp [huv]

theorem evalWireValAux_fuel_indep {g : Nat} (dag : LinearDag g) (x : Fin g → Int) :
    ∀ (f1 f2 m : Nat), m ≤ f1 → m ≤ f2 →
      evalWireValAux dag x f1 m = evalWireValAux dag x f2 m
  | 0, 0, _, _, _ => rfl
  | 0, f2 + 1, m, h1, _ => by
    have hm0 : m = 0 := by omega
    subst hm0
    unfold evalWireValAux
    by_cases h0g : 0 < g
    · simp [h0g]
    · simp only [h0g, ↓reduceDIte]
      cases dag.gates[0 - g]? with
      | none => rfl
      | some gate =>
        simp
  | f1 + 1, 0, m, _, h2 => by
    have hm0 : m = 0 := by omega
    subst hm0
    unfold evalWireValAux
    by_cases h0g : 0 < g
    · simp [h0g]
    · simp only [h0g, ↓reduceDIte]
      cases dag.gates[0 - g]? with
      | none => rfl
      | some gate =>
        simp
  | f1 + 1, f2 + 1, m, h1, h2 => by
    unfold evalWireValAux
    by_cases hmg : m < g
    · simp [hmg]
    · simp only [hmg, ↓reduceDIte]
      cases dag.gates[m - g]? with
      | none => rfl
      | some gate =>
        by_cases huv : gate.u < m ∧ gate.v < m
        · simp only [huv, and_self, ↓reduceIte]
          rw [evalWireValAux_fuel_indep dag x f1 f2 gate.u (by omega) (by omega),
              evalWireValAux_fuel_indep dag x f1 f2 gate.v (by omega) (by omega)]
        · simp [huv]

theorem evalWireVal_unfold {g : Nat} (dag : LinearDag g) (x : Fin g → Int) (m : Nat) :
    evalWireVal dag x m =
      if h : m < g then x ⟨m, h⟩
      else match dag.gates[m - g]? with
        | none => 0
        | some gate =>
          if gate.u < m ∧ gate.v < m then
            gate.c1 * evalWireVal dag x gate.u + gate.c2 * evalWireVal dag x gate.v
          else 0 := by
  change evalWireValAux dag x m m = _
  rw [evalWireValAux_fuel_indep dag x m (m + 1) m (Nat.le_refl m) (Nat.le_succ m)]
  rw [evalWireValAux]
  by_cases hmg : m < g
  · simp [hmg]
  · simp only [hmg, ↓reduceDIte]
    cases dag.gates[m - g]? with
    | none => rfl
    | some gate =>
      by_cases huv : gate.u < m ∧ gate.v < m
      · simp only [huv, and_self, ↓reduceIte]
        rw [evalWireValAux_fuel_indep dag x m gate.u gate.u (by omega) (Nat.le_refl _),
            evalWireValAux_fuel_indep dag x m gate.v gate.v (by omega) (Nat.le_refl _)]
        rfl
      · simp [huv]

theorem wireDepthAux_fuel_indep {g : Nat} (dag : LinearDag g) :
    ∀ (f1 f2 m : Nat), m ≤ f1 → m ≤ f2 →
      wireDepthAux dag f1 m = wireDepthAux dag f2 m
  | 0, 0, _, _, _ => rfl
  | 0, f2 + 1, m, h1, _ => by
    have hm0 : m = 0 := by omega
    subst hm0
    unfold wireDepthAux
    by_cases h0g : 0 < g
    · simp [h0g]
    · simp only [h0g, ↓reduceIte]
      cases dag.gates[0 - g]? with
      | none => rfl
      | some gate =>
        simp
  | f1 + 1, 0, m, _, h2 => by
    have hm0 : m = 0 := by omega
    subst hm0
    unfold wireDepthAux
    by_cases h0g : 0 < g
    · simp [h0g]
    · simp only [h0g, ↓reduceIte]
      cases dag.gates[0 - g]? with
      | none => rfl
      | some gate =>
        simp
  | f1 + 1, f2 + 1, m, h1, h2 => by
    unfold wireDepthAux
    by_cases hmg : m < g
    · simp [hmg]
    · simp only [hmg, ↓reduceIte]
      cases dag.gates[m - g]? with
      | none => rfl
      | some gate =>
        by_cases huv : gate.u < m ∧ gate.v < m
        · simp only [huv, and_self, ↓reduceIte]
          rw [wireDepthAux_fuel_indep dag f1 f2 gate.u (by omega) (by omega),
              wireDepthAux_fuel_indep dag f1 f2 gate.v (by omega) (by omega)]
        · simp [huv]

theorem wireDepth_unfold {g : Nat} (dag : LinearDag g) (m : Nat) :
    wireDepth dag m =
      if m < g then 0
      else match dag.gates[m - g]? with
        | none => 0
        | some gate =>
          if gate.u < m ∧ gate.v < m then
            1 + max (wireDepth dag gate.u) (wireDepth dag gate.v)
          else 0 := by
  change wireDepthAux dag m m = _
  rw [wireDepthAux_fuel_indep dag m (m + 1) m (Nat.le_refl m) (Nat.le_succ m)]
  rw [wireDepthAux]
  by_cases hmg : m < g
  · simp [hmg]
  · simp only [hmg, ↓reduceIte]
    cases dag.gates[m - g]? with
    | none => rfl
    | some gate =>
      by_cases huv : gate.u < m ∧ gate.v < m
      · simp only [huv, and_self, ↓reduceIte]
        rw [wireDepthAux_fuel_indep dag m gate.u gate.u (by omega) (Nat.le_refl _),
            wireDepthAux_fuel_indep dag m gate.v gate.v (by omega) (Nat.le_refl _)]
        rfl
      · simp [huv]

/-! ## Universal Linearity & Depth Lower Bound -/

theorem evalWireVal_eq_dotInt {g : Nat} (dag : LinearDag g) (x : Fin g → Int) :
    ∀ m : Nat, evalWireVal dag x m = dotInt (evalWireCoeff dag m) x := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [evalWireVal_unfold, evalWireCoeff_unfold]
    by_cases hm : m < g
    · simp only [hm, ↓reduceDIte, ↓reduceIte]
      exact (dotInt_unitVec x m hm).symm
    · simp only [hm, ↓reduceDIte, ↓reduceIte]
      cases hgate : dag.gates[m - g]? with
      | none =>
        unfold dotInt
        have hzero : finSumInt (fun i : Fin g => (0 : Int) * x i) =
            finSumInt (fun _ : Fin g => (0 : Int)) := by
          apply finSumInt_congr; intro i; exact Int.zero_mul (x i)
        rw [hzero, finSumInt_zero]
      | some gate =>
        by_cases huv : gate.u < m ∧ gate.v < m
        · simp only [huv, and_self, ↓reduceIte]
          rw [ih gate.u huv.1, ih gate.v huv.2]
          unfold dotInt
          rw [← finSumInt_mul_left, ← finSumInt_mul_left, ← finSumInt_add]
          apply finSumInt_congr
          intro j
          rw [Int.add_mul, Int.mul_assoc, Int.mul_assoc]
        · simp only [huv, ↓reduceIte]
          unfold dotInt
          have hzero : finSumInt (fun i : Fin g => (0 : Int) * x i) =
              finSumInt (fun _ : Fin g => (0 : Int)) := by
            apply finSumInt_congr; intro i; exact Int.zero_mul (x i)
          rw [hzero, finSumInt_zero]

theorem supportSize_evalWireCoeff_le_pow_depth {g : Nat} (dag : LinearDag g) :
    ∀ m : Nat, supportSize (evalWireCoeff dag m) ≤ 2 ^ wireDepth dag m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [evalWireCoeff_unfold, wireDepth_unfold]
    by_cases hm : m < g
    · simp only [hm, ↓reduceIte, Nat.pow_zero]
      rw [supportSize_unitVec m hm]
      exact Nat.le_refl 1
    · simp only [hm, ↓reduceIte]
      cases hgate : dag.gates[m - g]? with
      | none =>
        unfold supportSize
        have hzero : finSumNat (fun _ : Fin g => if (0 : Int) ≠ 0 then 1 else 0) =
            finSumNat (fun _ : Fin g => 0) := by
          apply finSumNat_congr; intro _; simp
        rw [hzero, finSumNat_const, Nat.mul_zero]
        exact Nat.zero_le _
      | some gate =>
        by_cases huv : gate.u < m ∧ gate.v < m
        · simp only [huv, and_self, ↓reduceIte]
          have h1 := supportSize_lincomb_le gate.c1 gate.c2
            (evalWireCoeff dag gate.u) (evalWireCoeff dag gate.v)
          have ihu := ih gate.u huv.1
          have ihv := ih gate.v huv.2
          have hpow_u : 2 ^ wireDepth dag gate.u ≤ 2 ^ max (wireDepth dag gate.u) (wireDepth dag gate.v) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)
          have hpow_v : 2 ^ wireDepth dag gate.v ≤ 2 ^ max (wireDepth dag gate.u) (wireDepth dag gate.v) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
          have hpow_succ : 2 ^ (1 + max (wireDepth dag gate.u) (wireDepth dag gate.v)) =
              2 ^ max (wireDepth dag gate.u) (wireDepth dag gate.v) +
              2 ^ max (wireDepth dag gate.u) (wireDepth dag gate.v) := by
            rw [Nat.add_comm, Nat.pow_succ]
            omega
          omega
        · simp only [huv, ↓reduceIte]
          unfold supportSize
          have hzero : finSumNat (fun _ : Fin g => if (0 : Int) ≠ 0 then 1 else 0) =
              finSumNat (fun _ : Fin g => 0) := by
            apply finSumNat_congr; intro _; simp
          rw [hzero, finSumNat_const, Nat.mul_zero]
          exact Nat.zero_le _

theorem fullSupport_depth_lower_bound {g : Nat} (hg : 1 ≤ g) (dag : LinearDag g) (m : Nat)
    (hfull : isFullSupport (evalWireCoeff dag m)) :
    g ≤ 2 ^ wireDepth dag m ∧ ceilLog2 g ≤ wireDepth dag m := by
  have h1 := supportSize_evalWireCoeff_le_pow_depth dag m
  rw [supportSize_of_full hfull] at h1
  exact ⟨h1, ceilLog2_le_of_le_pow hg h1⟩

theorem wireDepth_le_maxWireDepthUpTo {g : Nat} (dag : LinearDag g) :
    ∀ (n m : Nat), m < n → wireDepth dag m ≤ maxWireDepthUpTo dag n
  | 0, _, hm => by omega
  | n + 1, m, hm => by
    unfold maxWireDepthUpTo
    by_cases heq : m = n
    · subst heq
      exact Nat.le_max_right _ _
    · have hlt : m < n := by omega
      exact Nat.le_trans (wireDepth_le_maxWireDepthUpTo dag n m hlt) (Nat.le_max_left _ _)

theorem wireDepth_le_dagDepth {g : Nat} (dag : LinearDag g) (m : Nat)
    (hm : m < g + dag.gates.length) :
    wireDepth dag m ≤ dagDepth dag :=
  wireDepth_le_maxWireDepthUpTo dag (g + dag.gates.length) m hm

/-! ## Connected-Component Coloring Lower Bound (`2^(g-1) + g - 2`) -/

/-- After `t` gates (wires `0 .. g + t - 1`), there exists a coloring of coordinates `Fin g`
    such that every wire's support is monochromatic and at least `g - t` distinct colors remain. -/
theorem support_coloring_invariant {g : Nat} (dag : LinearDag g) :
    ∀ t : Nat,
      ∃ (color : Fin g → Nat) (reps : Fin (g - t) → Fin g),
        (∀ m < g + t, ∀ i j : Fin g,
          evalWireCoeff dag m i ≠ 0 → evalWireCoeff dag m j ≠ 0 → color i = color j) ∧
        (∀ a1 a2 : Fin (g - t), color (reps a1) = color (reps a2) → a1 = a2) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun i => i.val, fun a => ⟨a.val, by omega⟩, ?_, ?_⟩
    · intro m hm i j hi hj
      rw [evalWireCoeff_unfold] at hi hj
      have hmg : m < g := by omega
      simp only [hmg, ↓reduceIte, unitVec] at hi hj
      dsimp only
      by_cases hi' : i.val = m <;> by_cases hj' : j.val = m
      · omega
      · simp [hj'] at hj
      · simp [hi'] at hi
      · simp [hi'] at hi
    · intro a1 a2 heq
      exact Fin.ext heq
  | succ t ih =>
    rcases ih with ⟨color, reps, hmono, hinj⟩
    by_cases hzero : g - (t + 1) = 0
    · refine ⟨fun _ => 0, fun a => absurd a.isLt (by omega), ?_, ?_⟩
      · intro _ _ _ _ _ _; rfl
      · intro a1; exact absurd a1.isLt (by omega)
    · have keepColor :
          (∀ i j : Fin g, evalWireCoeff dag (g + t) i ≠ 0 → evalWireCoeff dag (g + t) j ≠ 0 →
            color i = color j) →
          ∃ (color' : Fin g → Nat) (reps' : Fin (g - (t + 1)) → Fin g),
            (∀ m < g + (t + 1), ∀ i j : Fin g,
              evalWireCoeff dag m i ≠ 0 → evalWireCoeff dag m j ≠ 0 → color' i = color' j) ∧
            (∀ a1 a2 : Fin (g - (t + 1)), color' (reps' a1) = color' (reps' a2) → a1 = a2) := by
        intro hnew
        refine ⟨color, fun a => reps ⟨a.val, by omega⟩, ?_, ?_⟩
        · intro m hm i j hi hj
          by_cases hmlt : m < g + t
          · exact hmono m hmlt i j hi hj
          · have hmeq : m = g + t := by omega
            subst hmeq
            exact hnew i j hi hj
        · intro a1 a2 heq
          have hfin := hinj ⟨a1.val, by omega⟩ ⟨a2.val, by omega⟩ heq
          exact Fin.ext (Fin.mk.inj hfin)
      cases hgate : dag.gates[t]? with
      | none =>
        apply keepColor
        intro i _ hi _
        rw [evalWireCoeff_unfold] at hi
        have hnotlt : ¬(g + t < g) := by omega
        have hsub : g + t - g = t := by omega
        simp only [hnotlt, ↓reduceIte, hsub, hgate] at hi
        exact absurd rfl hi
      | some gate =>
        by_cases huv : gate.u < g + t ∧ gate.v < g + t
        · by_cases hu : ∃ i0 : Fin g, evalWireCoeff dag gate.u i0 ≠ 0
          · by_cases hv : ∃ j0 : Fin g, evalWireCoeff dag gate.v j0 ≠ 0
            · rcases hu with ⟨i0, hi0⟩
              rcases hv with ⟨j0, hj0⟩
              let a := color i0
              let b := color j0
              let color' : Fin g → Nat := fun x => if color x = b then a else color x
              have hmono' : ∀ m < g + (t + 1), ∀ i j : Fin g,
                  evalWireCoeff dag m i ≠ 0 → evalWireCoeff dag m j ≠ 0 → color' i = color' j := by
                intro m hm i j hi hj
                by_cases hmlt : m < g + t
                · have hci := hmono m hmlt i j hi hj
                  simp only [color', hci]
                · have hmeq : m = g + t := by omega
                  subst hmeq
                  have hcoord : ∀ x : Fin g, evalWireCoeff dag (g + t) x ≠ 0 → color' x = a := by
                    intro x hx
                    rw [evalWireCoeff_unfold] at hx
                    have hnotlt : ¬(g + t < g) := by omega
                    have hsub : g + t - g = t := by omega
                    simp only [hnotlt, ↓reduceIte, hsub, hgate, huv, and_self] at hx
                    by_cases hux : evalWireCoeff dag gate.u x ≠ 0
                    · have hcx : color x = a := hmono gate.u huv.1 x i0 hux hi0
                      simp only [color', hcx]
                      split <;> simp [*]
                    · have hvx : evalWireCoeff dag gate.v x ≠ 0 := by
                        intro hveq
                        have hueq : evalWireCoeff dag gate.u x = 0 := Classical.byContradiction hux
                        simp [hueq, hveq] at hx
                      have hcx : color x = b := hmono gate.v huv.2 x j0 hvx hj0
                      simp only [color', hcx, ↓reduceIte]
                  rw [hcoord i hi, hcoord j hj]
              by_cases hexB : ∃ k0 : Fin (g - t), color (reps k0) = b
              · rcases hexB with ⟨k0, hk0⟩
                let reps' : Fin (g - (t + 1)) → Fin g := fun k =>
                  if h : k.val < k0.val then reps ⟨k.val, by omega⟩
                  else reps ⟨k.val + 1, by omega⟩
                have hneB : ∀ k : Fin (g - (t + 1)), color (reps' k) ≠ b := by
                  intro k heq
                  dsimp [reps'] at heq
                  split at heq
                  · have hfin := hinj ⟨k.val, by omega⟩ k0 (heq.trans hk0.symm)
                    have hval := Fin.mk.inj hfin
                    omega
                  · have hfin := hinj ⟨k.val + 1, by omega⟩ k0 (heq.trans hk0.symm)
                    have hval := Fin.mk.inj hfin
                    omega
                refine ⟨color', reps', hmono', ?_⟩
                intro k1 k2 heq
                have h1 := hneB k1
                have h2 := hneB k2
                simp only [color', h1, h2, ↓reduceIte] at heq
                dsimp [reps'] at heq
                split at heq <;> split at heq
                · exact Fin.ext (Fin.mk.inj (hinj _ _ heq))
                · have hval := Fin.mk.inj (hinj _ _ heq); omega
                · have hval := Fin.mk.inj (hinj _ _ heq); omega
                · have hval := Fin.mk.inj (hinj _ _ heq); exact Fin.ext (by omega)
              · let reps' : Fin (g - (t + 1)) → Fin g := fun k => reps ⟨k.val, by omega⟩
                have hneB : ∀ k : Fin (g - (t + 1)), color (reps' k) ≠ b := by
                  intro k heq
                  exact hexB ⟨⟨k.val, by omega⟩, heq⟩
                refine ⟨color', reps', hmono', ?_⟩
                intro k1 k2 heq
                have h1 := hneB k1
                have h2 := hneB k2
                simp only [color', h1, h2, ↓reduceIte] at heq
                exact Fin.ext (Fin.mk.inj (hinj _ _ heq))
            · apply keepColor
              intro i j hi hj
              rw [evalWireCoeff_unfold] at hi hj
              have hnotlt : ¬(g + t < g) := by omega
              have hsub : g + t - g = t := by omega
              simp only [hnotlt, ↓reduceIte, hsub, hgate, huv, and_self] at hi hj
              have hvi : evalWireCoeff dag gate.v i = 0 :=
                Classical.byContradiction (fun h => hv ⟨i, h⟩)
              have hvj : evalWireCoeff dag gate.v j = 0 :=
                Classical.byContradiction (fun h => hv ⟨j, h⟩)
              simp only [hvi, hvj, Int.mul_zero, Int.add_zero] at hi hj
              have hui : evalWireCoeff dag gate.u i ≠ 0 := by intro h; simp [h] at hi
              have huj : evalWireCoeff dag gate.u j ≠ 0 := by intro h; simp [h] at hj
              exact hmono gate.u huv.1 i j hui huj
          · apply keepColor
            intro i j hi hj
            rw [evalWireCoeff_unfold] at hi hj
            have hnotlt : ¬(g + t < g) := by omega
            have hsub : g + t - g = t := by omega
            simp only [hnotlt, ↓reduceIte, hsub, hgate, huv, and_self] at hi hj
            have hui : evalWireCoeff dag gate.u i = 0 :=
              Classical.byContradiction (fun h => hu ⟨i, h⟩)
            have huj : evalWireCoeff dag gate.u j = 0 :=
              Classical.byContradiction (fun h => hu ⟨j, h⟩)
            simp only [hui, huj, Int.mul_zero, Int.zero_add] at hi hj
            have hvi : evalWireCoeff dag gate.v i ≠ 0 := by intro h; simp [h] at hi
            have hvj : evalWireCoeff dag gate.v j ≠ 0 := by intro h; simp [h] at hj
            exact hmono gate.v huv.2 i j hvi hvj
        · apply keepColor
          intro i _ hi _
          rw [evalWireCoeff_unfold] at hi
          have hnotlt : ¬(g + t < g) := by omega
          have hsub : g + t - g = t := by omega
          simp only [hnotlt, ↓reduceIte, hsub, hgate, huv] at hi
          exact absurd rfl hi

/-- Any full-support wire at gate index `t` (wire `g + t`) forces `g - 2 ≤ t`. -/
theorem fullSupport_gate_index_ge {g : Nat} (dag : LinearDag g) (t : Nat)
    (hfull : isFullSupport (evalWireCoeff dag (g + t))) :
    g - 2 ≤ t := by
  rcases support_coloring_invariant dag (t + 1) with ⟨color, reps, hmono, hinj⟩
  match Nat.lt_or_ge t (g - 2) with
  | Or.inr hge => exact hge
  | Or.inl hlt =>
    let a0 : Fin (g - (t + 1)) := ⟨0, by omega⟩
    let a1 : Fin (g - (t + 1)) := ⟨1, by omega⟩
    have hsame : color (reps a0) = color (reps a1) :=
      hmono (g + t) (by omega) (reps a0) (reps a1) (hfull (reps a0)) (hfull (reps a1))
    have heq := hinj a0 a1 hsame
    have hval := Fin.mk.inj heq
    omega

/-- Every sign-canonical binary target has full support. -/
theorem binaryTarget_fullSupport {g : Nat} (idx : Fin (2 ^ (g - 1))) :
    isFullSupport (binaryTarget g idx) := by
  intro j
  unfold binaryTarget
  split
  · decide
  · split <;> decide

/-- Two distinct indices in `Fin (2^(g-1))` yield distinct binary targets. -/
theorem binaryTarget_injective {g : Nat} (idx1 idx2 : Fin (2 ^ (g - 1)))
    (heq : binaryTarget g idx1 = binaryTarget g idx2) : idx1 = idx2 := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < g - 1
  · have hkj : k + 1 < g := by omega
    have hval := congrFun heq ⟨k + 1, hkj⟩
    unfold binaryTarget at hval
    have hne0 : ¬(k + 1 = 0) := by omega
    have hsub : k + 1 - 1 = k := by omega
    simp only [hne0, ↓reduceIte, hsub] at hval
    cases hb1 : idx1.val.testBit k <;> cases hb2 : idx2.val.testBit k
    · rfl
    · simp [hb1, hb2] at hval
    · simp [hb1, hb2] at hval
    · rfl
  · have hge : g - 1 ≤ k := by omega
    have h1 : idx1.val < 2 ^ k := Nat.lt_of_lt_of_le idx1.isLt (Nat.pow_le_pow_right (by decide) hge)
    have h2 : idx2.val < 2 ^ k := Nat.lt_of_lt_of_le idx2.isLt (Nat.pow_le_pow_right (by decide) hge)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

/-- No input wire `m < g` has full support when `g ≥ 2`. -/
theorem inputWire_not_fullSupport {g : Nat} (hg : 2 ≤ g) (dag : LinearDag g) (m : Nat)
    (hm : m < g) : ¬isFullSupport (evalWireCoeff dag m) := by
  intro hfull
  let j : Fin g := if m = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hj := hfull j
  rw [evalWireCoeff_unfold] at hj
  simp only [hm, ↓reduceIte, unitVec] at hj
  by_cases hm0 : m = 0
  · simp [j, hm0] at hj
  · simp [j, hm0] at hj
    exact hm0 hj.symm

/-- Universal lower bound: every 2-input linear DAG computing all `2^(g-1)` sign-canonical
    binary targets (`g ≥ 2`) uses at least `2^(g-1) + g - 2` operations. -/
theorem binary_dag_lower_bound_universal {g : Nat} (hg : 2 ≤ g) (dag : LinearDag g)
    (hcomp : computesAllBinary dag) :
    binaryLowerBound g ≤ dag.gates.length := by
  let f : Fin (2 ^ (g - 1)) → Nat := fun idx => Classical.choose (hcomp idx)
  have hf_spec : ∀ idx, f idx < g + dag.gates.length ∧ evalWireCoeff dag (f idx) = binaryTarget g idx :=
    fun idx => Classical.choose_spec (hcomp idx)
  have hf_ge : ∀ idx, g + (g - 2) ≤ f idx := by
    intro idx
    have hfull : isFullSupport (evalWireCoeff dag (f idx)) := by
      rw [(hf_spec idx).2]
      exact binaryTarget_fullSupport idx
    have hnot_in : ¬(f idx < g) := fun hlt => inputWire_not_fullSupport hg dag (f idx) hlt hfull
    have hge_g : g ≤ f idx := by omega
    have hfull' : isFullSupport (evalWireCoeff dag (g + (f idx - g))) := by
      have : g + (f idx - g) = f idx := by omega
      rw [this]; exact hfull
    have ht := fullSupport_gate_index_ge dag (f idx - g) hfull'
    omega
  have hf_inj : ∀ idx1 idx2, f idx1 = f idx2 → idx1 = idx2 := by
    intro idx1 idx2 heq
    apply binaryTarget_injective idx1 idx2
    rw [← (hf_spec idx1).2, ← (hf_spec idx2).2, heq]
  have hpig := fin_pigeonhole_interval (A := 2 ^ (g - 1)) (lo := g + (g - 2))
    (hi := g + dag.gates.length) f hf_inj (fun idx => ⟨hf_ge idx, (hf_spec idx).1⟩)
  have hpos : 0 < 2 ^ (g - 1) := Nat.pow_pos (by decide)
  have h0_ge := hf_ge ⟨0, hpos⟩
  have h0_lt := (hf_spec ⟨0, hpos⟩).1
  unfold binaryLowerBound
  omega

/-- Headline Theorem 1 (`binary_lut_dag_lower_bound_exact`):
    Universal gate-count lower bound `2^(g-1) + g - 2` and depth lower bound `ceilLog2 g`
    for any 2-input linear DAG computing all sign-canonical binary LUT entries, plus exact
    specializations for `g = 2, 3, 4, 5`. -/
theorem binary_lut_dag_lower_bound_exact :
    (∀ (g : Nat) (dag : LinearDag g), 2 ≤ g → computesAllBinary dag →
      binaryLowerBound g ≤ dag.gates.length) ∧
    (∀ (g : Nat) (dag : LinearDag g), 1 ≤ g → computesAllBinary dag →
      g ≤ 2 ^ dagDepth dag ∧ ceilLog2 g ≤ dagDepth dag) ∧
    (∀ (g : Nat) (dag : LinearDag g) (x : Fin g → Int) (m : Nat),
      evalWireVal dag x m = dotInt (evalWireCoeff dag m) x) ∧
    (binaryLowerBound 2 = 2 ∧ binaryLowerBound 3 = 5 ∧
     binaryLowerBound 4 = 10 ∧ binaryLowerBound 5 = 19) ∧
    (ceilLog2 2 = 1 ∧ ceilLog2 3 = 2 ∧ ceilLog2 4 = 2 ∧ ceilLog2 5 = 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g dag hg hcomp
    exact binary_dag_lower_bound_universal hg dag hcomp
  · intro g dag hg hcomp
    have hpos : 0 < 2 ^ (g - 1) := Nat.pow_pos (by decide)
    rcases hcomp ⟨0, hpos⟩ with ⟨m, hm, hcoeff⟩
    have hfull : isFullSupport (evalWireCoeff dag m) := by
      rw [hcoeff]
      exact binaryTarget_fullSupport ⟨0, hpos⟩
    have hd := fullSupport_depth_lower_bound hg dag m hfull
    have hle := wireDepth_le_dagDepth dag m hm
    exact ⟨Nat.le_trans hd.1 (Nat.pow_le_pow_right (by decide) hle), Nat.le_trans hd.2 hle⟩
  · intro g dag x m
    exact evalWireVal_eq_dotInt dag x m
  · decide
  · exact ceilLog2_values

/-! ## Concrete `g = 4` Binary Circuit Verification (Theorem 2) -/

def binVecEqBool {g : Nat} (u v : Fin g → Int) : Bool :=
  (List.finRange g).all (fun j => decide (u j = v j))

theorem binVecEqBool_true {g : Nat} {u v : Fin g → Int} (h : binVecEqBool u v = true) : u = v := by
  funext j
  unfold binVecEqBool at h
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h j (List.mem_finRange j))

def checkBinaryWireMap {g : Nat} (dag : LinearDag g) (wireOf : Fin (2 ^ (g - 1)) → Nat) : Bool :=
  (List.finRange (2 ^ (g - 1))).all (fun idx =>
    let m := wireOf idx
    decide (m < g + dag.gates.length) && binVecEqBool (evalWireCoeff dag m) (binaryTarget g idx))

theorem checkBinaryWireMap_true {g : Nat} {dag : LinearDag g}
    {wireOf : Fin (2 ^ (g - 1)) → Nat}
    (h : checkBinaryWireMap dag wireOf = true) : computesAllBinary dag := by
  intro idx
  unfold checkBinaryWireMap at h
  rw [List.all_eq_true] at h
  have h1 := h idx (List.mem_finRange idx)
  rw [Bool.and_eq_true] at h1
  exact ⟨wireOf idx, of_decide_eq_true h1.1, binVecEqBool_true h1.2⟩

def wireOfBalancedG4 (idx : Fin 8) : Nat :=
  match idx.val with
  | 0 => 8 | 1 => 12 | 2 => 11 | 3 => 15
  | 4 => 10 | 5 => 14 | 6 => 9 | _ => 13

def wireOfNaiveG4 (idx : Fin 8) : Nat :=
  match idx.val with
  | 0 => 10 | 1 => 14 | 2 => 12 | 3 => 16
  | 4 => 11 | 5 => 15 | 6 => 13 | _ => 17

def wireOfRdna3MidG4 (idx : Fin 8) : Nat :=
  match idx.val with
  | 0 => 7 | 1 => 9 | 2 => 12 | 3 => 14
  | 4 => 11 | 5 => 13 | 6 => 8 | _ => 10

def wireOfRdna3MinG4 (idx : Fin 8) : Nat :=
  match idx.val with
  | 0 => 6 | 1 => 10 | 2 => 9 | 3 => 13
  | 4 => 8 | 5 => 12 | 6 => 7 | _ => 11

theorem balancedTreeG4_valid : balancedTreeG4Dag.Valid := by
  intro k gate hgate
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 =>
    simp [balancedTreeG4Dag] at hgate; subst hgate; decide
  | k + 12 =>
    simp [balancedTreeG4Dag] at hgate

theorem balancedTreeG4_pureAddSub : balancedTreeG4Dag.isPureAddSub := by
  intro gate hmem
  simp only [balancedTreeG4Dag, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, by decide⟩

theorem balancedTreeG4_computesAll : computesAllBinary balancedTreeG4Dag :=
  checkBinaryWireMap_true (wireOf := wireOfBalancedG4) (by decide)

theorem naiveTmacG4_valid : naiveTmacG4Dag.Valid := by
  intro k gate hgate
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 =>
    simp [naiveTmacG4Dag] at hgate; subst hgate; decide
  | k + 14 =>
    simp [naiveTmacG4Dag] at hgate

theorem naiveTmacG4_pureAddSub : naiveTmacG4Dag.isPureAddSub := by
  intro gate hmem
  simp only [naiveTmacG4Dag, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, by decide⟩

theorem naiveTmacG4_computesAll : computesAllBinary naiveTmacG4Dag :=
  checkBinaryWireMap_true (wireOf := wireOfNaiveG4) (by decide)

theorem rdna3MidG4_valid : rdna3MidG4Dag.Valid := by
  intro k gate hgate
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 =>
    simp [rdna3MidG4Dag] at hgate; subst hgate; decide
  | k + 11 =>
    simp [rdna3MidG4Dag] at hgate

theorem rdna3MidG4_isRdna3 : rdna3MidG4Dag.isRdna3AddLshl := by
  intro gate hmem
  simp only [rdna3MidG4Dag, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide⟩

theorem rdna3MidG4_computesAll : computesAllBinary rdna3MidG4Dag :=
  checkBinaryWireMap_true (wireOf := wireOfRdna3MidG4) (by decide)

theorem rdna3MinOpsG4_valid : rdna3MinOpsG4Dag.Valid := by
  intro k gate hgate
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 =>
    simp [rdna3MinOpsG4Dag] at hgate; subst hgate; decide
  | k + 10 =>
    simp [rdna3MinOpsG4Dag] at hgate

theorem rdna3MinOpsG4_isRdna3 : rdna3MinOpsG4Dag.isRdna3AddLshl := by
  intro gate hmem
  simp only [rdna3MinOpsG4Dag, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide⟩

theorem rdna3MinOpsG4_computesAll : computesAllBinary rdna3MinOpsG4Dag :=
  checkBinaryWireMap_true (wireOf := wireOfRdna3MinG4) (by decide)

/-- Headline Theorem 2 (`tmac_depth2_optimal_12_vs_14_circuit`):
    Exact soundness, completeness, and Pareto dominance of the GPU-discovered `g = 4`
    circuits: balanced `(12 ops, depth 2)` strictly beats naive T-MAC `(14 ops, depth 3)`
    in both op count (`-1/7 = -14.3%`) and depth (`-1/3 = -33.3%`) while matching `ceilLog2 4 = 2`,
    and the RDNA 3 `V_ADD_LSHL` circuits achieve `(11 ops, depth 3)` and lower-bound-tight
    `(10 ops, depth 4)` (= `binaryLowerBound 4`). -/
theorem tmac_depth2_optimal_12_vs_14_circuit :
    (balancedTreeG4Dag.Valid ∧ balancedTreeG4Dag.isPureAddSub ∧
     balancedTreeG4Dag.gates.length = 12 ∧ dagDepth balancedTreeG4Dag = 2 ∧
     computesAllBinary balancedTreeG4Dag) ∧
    (naiveTmacG4Dag.Valid ∧ naiveTmacG4Dag.isPureAddSub ∧
     naiveTmacG4Dag.gates.length = 14 ∧ dagDepth naiveTmacG4Dag = 3 ∧
     computesAllBinary naiveTmacG4Dag) ∧
    (balancedTreeG4Dag.gates.length < naiveTmacG4Dag.gates.length ∧
     dagDepth balancedTreeG4Dag < dagDepth naiveTmacG4Dag ∧
     dagDepth balancedTreeG4Dag = ceilLog2 4 ∧
     (((naiveTmacG4Dag.gates.length - balancedTreeG4Dag.gates.length : Nat) : Rat) /
        (naiveTmacG4Dag.gates.length : Rat) = 1 / 7) ∧
     (((dagDepth naiveTmacG4Dag - dagDepth balancedTreeG4Dag : Nat) : Rat) /
        (dagDepth naiveTmacG4Dag : Rat) = 1 / 3)) ∧
    (rdna3MidG4Dag.Valid ∧ rdna3MidG4Dag.isRdna3AddLshl ∧
     rdna3MidG4Dag.gates.length = 11 ∧ dagDepth rdna3MidG4Dag = 3 ∧
     computesAllBinary rdna3MidG4Dag) ∧
    (rdna3MinOpsG4Dag.Valid ∧ rdna3MinOpsG4Dag.isRdna3AddLshl ∧
     rdna3MinOpsG4Dag.gates.length = 10 ∧
     rdna3MinOpsG4Dag.gates.length = binaryLowerBound 4 ∧
     dagDepth rdna3MinOpsG4Dag = 4 ∧
     computesAllBinary rdna3MinOpsG4Dag) ∧
    (∀ (x : Fin 4 → Int) (idx : Fin 8),
      (∃ m < 4 + balancedTreeG4Dag.gates.length,
        evalWireVal balancedTreeG4Dag x m = dotInt (binaryTarget 4 idx) x) ∧
      (∃ m < 4 + rdna3MinOpsG4Dag.gates.length,
        evalWireVal rdna3MinOpsG4Dag x m = dotInt (binaryTarget 4 idx) x)) := by
  have hbLen : balancedTreeG4Dag.gates.length = 12 := rfl
  have hnLen : naiveTmacG4Dag.gates.length = 14 := rfl
  have hbDep : dagDepth balancedTreeG4Dag = 2 := by decide
  have hnDep : dagDepth naiveTmacG4Dag = 3 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨balancedTreeG4_valid, balancedTreeG4_pureAddSub, hbLen, hbDep, balancedTreeG4_computesAll⟩
  · exact ⟨naiveTmacG4_valid, naiveTmacG4_pureAddSub, hnLen, hnDep, naiveTmacG4_computesAll⟩
  · refine ⟨by rw [hbLen, hnLen]; decide, by rw [hbDep, hnDep]; decide,
      by rw [hbDep]; decide, ?_, ?_⟩
    · rw [hbLen, hnLen]; grind
    · rw [hbDep, hnDep]; grind
  · exact ⟨rdna3MidG4_valid, rdna3MidG4_isRdna3, rfl, by decide, rdna3MidG4_computesAll⟩
  · exact ⟨rdna3MinOpsG4_valid, rdna3MinOpsG4_isRdna3, rfl, by decide, by decide, rdna3MinOpsG4_computesAll⟩
  · intro x idx
    constructor
    · rcases balancedTreeG4_computesAll idx with ⟨m, hm, hcoeff⟩
      exact ⟨m, hm, by rw [evalWireVal_eq_dotInt, hcoeff]⟩
    · rcases rdna3MinOpsG4_computesAll idx with ⟨m, hm, hcoeff⟩
      exact ⟨m, hm, by rw [evalWireVal_eq_dotInt, hcoeff]⟩

end BitSerialLutDag
