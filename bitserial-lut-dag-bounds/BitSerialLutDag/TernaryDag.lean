/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSerialLutDag.BinaryDag

/-!
# Ternary Sign-Folded LUT Bounds & Minimal Zero-Waste DAGs (`BitSerialLutDag.TernaryDag`)

Proves Headline Theorem 3 (`ternary_lut_dag_bounds_and_symmetry`):
- Exact symmetry-halved ternary codebook size `2 * ternaryFoldedSize g + 1 = 3 ^ g`
  (`4, 13, 40, 121` for `g = 2, 3, 4, 5`).
- Exact balanced-ternary reconstruction `balTernSum (ternaryTarget g idx) = idx.val + 1`,
  implying injectivity of `ternaryTarget g` for all `g`.
- Universal 2-input linear DAG lower bound `ternaryLowerBound g = (3^g - 1)/2 - g ≤ dag.gates.length`
  (`2, 10, 36, 116` for `g = 2, 3, 4, 5`) and universal depth lower bound `ceilLog2 g ≤ dagDepth dag`.
- Exact soundness & zero-waste optimality of `ternaryMinG2Dag` (`2 ops, depth 1`),
  `ternaryMinG3Dag` (`10 ops, depth 2`), `ternaryMinG4Dag` (`36 ops, depth 2`), and
  structured `(≤2, 4)` ternary sparsity DAG `ternarySparse2of4Dag` (`12 ops, depth 1`,
  `3×` fewer ops and `2×` lower depth than full `g = 4` ternary).
-/

namespace BitSerialLutDag

/-! ## Symmetry-Halved Ternary Size -/

theorem pow3_mod2 : ∀ g : Nat, 3 ^ g % 2 = 1
  | 0 => rfl
  | g + 1 => by
    rw [Nat.pow_succ]
    have ih := pow3_mod2 g
    omega

theorem two_mul_ternaryFoldedSize_add_one (g : Nat) :
    2 * ternaryFoldedSize g + 1 = 3 ^ g := by
  unfold ternaryFoldedSize
  have hodd := pow3_mod2 g
  have hpos : 1 ≤ 3 ^ g := Nat.pow_pos (by decide)
  omega

theorem ternary_sizes_exact :
    (ternaryFoldedSize 2 = 4 ∧ ternaryFoldedSize 3 = 13 ∧
     ternaryFoldedSize 4 = 40 ∧ ternaryFoldedSize 5 = 121) ∧
    (ternaryLowerBound 2 = 2 ∧ ternaryLowerBound 3 = 10 ∧
     ternaryLowerBound 4 = 36 ∧ ternaryLowerBound 5 = 116) := by
  decide

/-! ## Balanced-Ternary Reconstruction & Universal Lower Bound -/

/-- Weighted base-3 evaluation `∑_{j=0}^{g-1} w_j * 3^j`. -/
def balTernSum {g : Nat} (w : Fin g → Int) : Int :=
  finSumInt (fun j => w j * ((3 ^ j.val : Nat) : Int))

theorem finSumAuxInt_succ_shift {g : Nat} (f : Fin (g + 1) → Int) :
    ∀ (k : Nat) (hk : k ≤ g),
      finSumAuxInt f (k + 1) (Nat.succ_le_succ hk) =
        f ⟨0, Nat.zero_lt_succ g⟩ +
        finSumAuxInt (fun j : Fin g => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) k hk
  | 0, _ => by
    simp only [finSumAuxInt, Int.zero_add, Int.add_zero]
  | k + 1, hk => by
    have hstep : finSumAuxInt f (k + 2) (Nat.succ_le_succ hk) =
        finSumAuxInt f (k + 1) (Nat.succ_le_succ (Nat.le_of_succ_le hk)) +
        f ⟨k + 1, Nat.succ_lt_succ hk⟩ := rfl
    rw [hstep, finSumAuxInt_succ_shift f k (Nat.le_of_succ_le hk), finSumAuxInt]
    dsimp only
    omega

theorem finSumInt_succ_shift {g : Nat} (f : Fin (g + 1) → Int) :
    finSumInt f =
      f ⟨0, Nat.zero_lt_succ g⟩ +
      finSumInt (fun j : Fin g => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) :=
  finSumAuxInt_succ_shift f g (Nat.le_refl g)

theorem balTernSum_balTernDigit : ∀ (g n : Nat),
    n ≤ ternaryFoldedSize g →
    balTernSum (fun j : Fin g => balTernDigit j.val n) = (n : Int)
  | 0, n, hn => by
    have h0 : ternaryFoldedSize 0 = 0 := rfl
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | g + 1, n, hn => by
    unfold balTernSum
    rw [finSumInt_succ_shift]
    let q : Nat := match n % 3 with
      | 2 => n / 3 + 1
      | _ => n / 3
    have hpow : 3 ^ (g + 1) = 3 * 3 ^ g := by rw [Nat.pow_succ]; omega
    have hodd : 3 ^ g % 2 = 1 := pow3_mod2 g
    have hpos : 1 ≤ 3 ^ g := Nat.pow_pos (by decide)
    have h2n : 2 * n ≤ 3 * 3 ^ g - 1 := by
      unfold ternaryFoldedSize at hn
      omega
    have hq_le : q ≤ ternaryFoldedSize g := by
      unfold ternaryFoldedSize
      dsimp only [q]
      cases hm : n % 3 with
      | zero => simp only; omega
      | succ r =>
        cases r with
        | zero => simp only; omega
        | succ r' =>
          cases r' with
          | zero => simp only; omega
          | succ _ => omega
    have htail :
        finSumInt (fun j : Fin g => balTernDigit (j.val + 1) n * ((3 ^ (j.val + 1) : Nat) : Int)) =
        3 * balTernSum (fun j : Fin g => balTernDigit j.val q) := by
      unfold balTernSum
      rw [← finSumInt_mul_left]
      apply finSumInt_congr
      intro j
      have h3 : ((3 ^ (j.val + 1) : Nat) : Int) = 3 * ((3 ^ j.val : Nat) : Int) := by
        rw [Nat.pow_succ]
        omega
      have hdig : balTernDigit (j.val + 1) n = balTernDigit j.val q := rfl
      rw [h3, hdig]
      rw [← Int.mul_assoc, Int.mul_comm (balTernDigit j.val q) 3, Int.mul_assoc]
    rw [htail, balTernSum_balTernDigit g q hq_le]
    have h0 : ((3 ^ 0 : Nat) : Int) = 1 := rfl
    rw [h0, Int.mul_one]
    dsimp only [balTernDigit, q]
    cases hm : n % 3 with
    | zero => simp only; omega
    | succ r =>
      cases r with
      | zero => simp only; omega
      | succ r' =>
        cases r' with
        | zero => simp only; omega
        | succ _ => omega

theorem ternaryTarget_injective {g : Nat} (idx1 idx2 : Fin (ternaryFoldedSize g))
    (heq : ternaryTarget g idx1 = ternaryTarget g idx2) : idx1 = idx2 := by
  have h1 := balTernSum_balTernDigit g (idx1.val + 1) (by omega)
  have h2 := balTernSum_balTernDigit g (idx2.val + 1) (by omega)
  have hsum : balTernSum (ternaryTarget g idx1) = balTernSum (ternaryTarget g idx2) := by
    rw [heq]
  unfold ternaryTarget at hsum
  rw [h1, h2] at hsum
  apply Fin.ext
  omega

theorem balTernDigit_allOnes : ∀ (g j : Nat),
    j < g → balTernDigit j (ternaryFoldedSize g) = 1
  | 0, _, hj => by omega
  | g + 1, 0, _ => by
    unfold balTernDigit ternaryFoldedSize
    have hpow : 3 ^ (g + 1) = 3 * 3 ^ g := by rw [Nat.pow_succ]; omega
    have hodd : 3 ^ g % 2 = 1 := pow3_mod2 g
    have hpos : 1 ≤ 3 ^ g := Nat.pow_pos (by decide)
    have hmod : (3 ^ (g + 1) - 1) / 2 % 3 = 1 := by omega
    rw [hmod]
    rfl
  | g + 1, j + 1, hj => by
    unfold balTernDigit
    have hpow : 3 ^ (g + 1) = 3 * 3 ^ g := by rw [Nat.pow_succ]; omega
    have hodd : 3 ^ g % 2 = 1 := pow3_mod2 g
    have hpos : 1 ≤ 3 ^ g := Nat.pow_pos (by decide)
    have hmod : ternaryFoldedSize (g + 1) % 3 = 1 := by
      unfold ternaryFoldedSize; omega
    have hdiv : ternaryFoldedSize (g + 1) / 3 = ternaryFoldedSize g := by
      unfold ternaryFoldedSize; omega
    simp only [hmod, hdiv]
    exact balTernDigit_allOnes g j (by omega)

theorem ternary_dag_lower_bound_universal {g : Nat} (dag : LinearDag g)
    (hcomp : computesAllTernary dag) :
    ternaryLowerBound g ≤ dag.gates.length := by
  let f : Fin (ternaryFoldedSize g) → Nat := fun idx => Classical.choose (hcomp idx)
  have hf_spec : ∀ idx, f idx < g + dag.gates.length ∧
      evalWireCoeff dag (f idx) = ternaryTarget g idx :=
    fun idx => Classical.choose_spec (hcomp idx)
  have hf_inj : ∀ idx1 idx2, f idx1 = f idx2 → idx1 = idx2 := by
    intro idx1 idx2 heq
    apply ternaryTarget_injective idx1 idx2
    rw [← (hf_spec idx1).2, ← (hf_spec idx2).2, heq]
  have hpig := fin_pigeonhole_zero (B := g + dag.gates.length) f hf_inj (fun idx => (hf_spec idx).1)
  unfold ternaryLowerBound
  omega

theorem ternary_dag_depth_lower_bound_universal {g : Nat} (hg : 1 ≤ g) (dag : LinearDag g)
    (hcomp : computesAllTernary dag) :
    g ≤ 2 ^ dagDepth dag ∧ ceilLog2 g ≤ dagDepth dag := by
  have hpos : 1 ≤ ternaryFoldedSize g := by
    have h1 := two_mul_ternaryFoldedSize_add_one g
    have h3 : 3 ≤ 3 ^ g := by
      have : 3 ^ 1 ≤ 3 ^ g := Nat.pow_le_pow_right (by decide) hg
      simpa using this
    omega
  let idxMax : Fin (ternaryFoldedSize g) := ⟨ternaryFoldedSize g - 1, by omega⟩
  rcases hcomp idxMax with ⟨m, hm, hcoeff⟩
  have hfull : isFullSupport (evalWireCoeff dag m) := by
    rw [hcoeff]
    intro j
    unfold ternaryTarget
    have heq : idxMax.val + 1 = ternaryFoldedSize g := by
      dsimp [idxMax]; omega
    rw [heq, balTernDigit_allOnes g j.val j.isLt]
    decide
  have hd := fullSupport_depth_lower_bound hg dag m hfull
  have hle := wireDepth_le_dagDepth dag m hm
  exact ⟨Nat.le_trans hd.1 (Nat.pow_le_pow_right (by decide) hle), Nat.le_trans hd.2 hle⟩

/-! ## Fast Direct-Wire Soundness Checkers for Minimal Concrete Ternary DAGs -/

def vecEqBool {g : Nat} (u v : Fin g → Int) : Bool :=
  (List.finRange g).all (fun j => decide (u j = v j))

theorem vecEqBool_true {g : Nat} {u v : Fin g → Int} (h : vecEqBool u v = true) : u = v := by
  funext j
  unfold vecEqBool at h
  rw [List.all_eq_true] at h
  have hmem : j ∈ List.finRange g := List.mem_finRange j
  exact of_decide_eq_true (h j hmem)

def checkWireMap {g : Nat} (dag : LinearDag g) (wireOf : Fin (ternaryFoldedSize g) → Nat) : Bool :=
  (List.finRange (ternaryFoldedSize g)).all (fun idx =>
    let m := wireOf idx
    decide (m < g + dag.gates.length) && vecEqBool (evalWireCoeff dag m) (ternaryTarget g idx))

theorem checkWireMap_true {g : Nat} {dag : LinearDag g}
    {wireOf : Fin (ternaryFoldedSize g) → Nat}
    (h : checkWireMap dag wireOf = true) : computesAllTernary dag := by
  intro idx
  unfold checkWireMap at h
  rw [List.all_eq_true] at h
  have h1 := h idx (List.mem_finRange idx)
  rw [Bool.and_eq_true] at h1
  exact ⟨wireOf idx, of_decide_eq_true h1.1, vecEqBool_true h1.2⟩

def checkBoundedWireMap {g : Nat} (dag : LinearDag g) (k : Nat)
    (wireOf : Fin (ternaryFoldedSize g) → Nat) : Bool :=
  (List.finRange (ternaryFoldedSize g)).all (fun idx =>
    if supportSize (ternaryTarget g idx) ≤ k then
      let m := wireOf idx
      decide (m < g + dag.gates.length) && vecEqBool (evalWireCoeff dag m) (ternaryTarget g idx)
    else true)

theorem checkBoundedWireMap_true {g : Nat} {dag : LinearDag g} {k : Nat}
    {wireOf : Fin (ternaryFoldedSize g) → Nat}
    (h : checkBoundedWireMap dag k wireOf = true) : computesBoundedTernary dag k := by
  intro idx hsupp
  unfold checkBoundedWireMap at h
  rw [List.all_eq_true] at h
  have h1 := h idx (List.mem_finRange idx)
  simp only [hsupp, ↓reduceIte, Bool.and_eq_true] at h1
  exact ⟨wireOf idx, of_decide_eq_true h1.1, vecEqBool_true h1.2⟩

def checkDagValid {g : Nat} (dag : LinearDag g) : Bool :=
  (List.range dag.gates.length).all (fun k =>
    match dag.gates[k]? with
    | none => true
    | some gate => decide (gate.u < g + k ∧ gate.v < g + k))

theorem checkDagValid_true {g : Nat} {dag : LinearDag g}
    (h : checkDagValid dag = true) : dag.Valid := by
  intro k gate hgate
  have hk : k < dag.gates.length := by
    cases Nat.lt_or_ge k dag.gates.length with
    | inl hlt => exact hlt
    | inr hge =>
      rw [List.getElem?_eq_none hge] at hgate
      cases hgate
  unfold checkDagValid at h
  rw [List.all_eq_true] at h
  have h1 := h k (List.mem_range.mpr hk)
  rw [hgate] at h1
  exact of_decide_eq_true h1

def checkPureAddSub {g : Nat} (dag : LinearDag g) : Bool :=
  dag.gates.all (fun gate => decide (gate.c1 = 1 ∧ (gate.c2 = 1 ∨ gate.c2 = -1)))

theorem checkPureAddSub_true {g : Nat} {dag : LinearDag g}
    (h : checkPureAddSub dag = true) : dag.isPureAddSub := by
  intro gate hmem
  unfold checkPureAddSub at h
  rw [List.all_eq_true] at h
  unfold LinearGate.isPureAddSub
  exact of_decide_eq_true (h gate hmem)

/-- Direct O(1) wire map for `ternaryMinG2Dag`. -/
def wireOfTernary2 (idx : Fin (ternaryFoldedSize 2)) : Nat :=
  let w := ternaryTarget 2 idx
  match w ⟨0, by decide⟩, w ⟨1, by decide⟩ with
  | 1, 0 => 0
  | 0, 1 => 1
  | 1, 1 => 2
  | -1, 1 => 3
  | _, _ => 0

/-- Direct O(1) wire map for `ternaryMinG3Dag`. -/
def wireOfTernary3 (idx : Fin (ternaryFoldedSize 3)) : Nat :=
  let w := ternaryTarget 3 idx
  match w ⟨0, by decide⟩, w ⟨1, by decide⟩, w ⟨2, by decide⟩ with
  | 1, 0, 0 => 0
  | 0, 1, 0 => 1
  | 0, 0, 1 => 2
  | 1, 1, 0 => 3
  | -1, 1, 0 => 4
  | 1, 0, 1 => 5
  | -1, 0, 1 => 6
  | 0, 1, 1 => 7
  | 0, -1, 1 => 8
  | 1, 1, 1 => 9
  | -1, -1, 1 => 10
  | -1, 1, 1 => 11
  | 1, -1, 1 => 12
  | _, _, _ => 0

/-- Direct O(1) wire map for `ternaryMinG4Dag` (balanced 2+2 tree). -/
def wireOfTernary4 (idx : Fin (ternaryFoldedSize 4)) : Nat :=
  let w := ternaryTarget 4 idx
  let d0 := w ⟨0, by decide⟩
  let d1 := w ⟨1, by decide⟩
  let d2 := w ⟨2, by decide⟩
  let d3 := w ⟨3, by decide⟩
  let leftInfo : Option (Nat × Nat) :=
    match d0, d1 with
    | 1, 0 => some (0, 0)
    | -1, 0 => some (0, 1)
    | 0, 1 => some (1, 0)
    | 0, -1 => some (1, 1)
    | 1, 1 => some (2, 0)
    | -1, -1 => some (2, 1)
    | -1, 1 => some (3, 0)
    | 1, -1 => some (3, 1)
    | _, _ => none
  let rightInfo : Option Nat :=
    match d2, d3 with
    | 1, 0 => some 0
    | 0, 1 => some 1
    | 1, 1 => some 2
    | -1, 1 => some 3
    | _, _ => none
  match rightInfo, leftInfo with
  | none, some (0, 0) => 0
  | none, some (1, 0) => 1
  | none, some (2, 0) => 4
  | none, some (3, 0) => 5
  | some 0, none => 2
  | some 1, none => 3
  | some 2, none => 6
  | some 3, none => 7
  | some rIdx, some (lIdx, sBit) => 8 + 8 * rIdx + 2 * lIdx + sBit
  | _, _ => 0

/-- Direct O(1) wire map for `ternarySparse2of4Dag` (`≤ 2` nonzeros in `g = 4`). -/
def wireOfSparse2of4 (idx : Fin (ternaryFoldedSize 4)) : Nat :=
  let w := ternaryTarget 4 idx
  match w ⟨0, by decide⟩, w ⟨1, by decide⟩, w ⟨2, by decide⟩, w ⟨3, by decide⟩ with
  | 1, 0, 0, 0 => 0
  | 0, 1, 0, 0 => 1
  | 0, 0, 1, 0 => 2
  | 0, 0, 0, 1 => 3
  | 1, 1, 0, 0 => 4
  | -1, 1, 0, 0 => 5
  | 1, 0, 1, 0 => 6
  | -1, 0, 1, 0 => 7
  | 0, 1, 1, 0 => 8
  | 0, -1, 1, 0 => 9
  | 1, 0, 0, 1 => 10
  | -1, 0, 0, 1 => 11
  | 0, 1, 0, 1 => 12
  | 0, -1, 0, 1 => 13
  | 0, 0, 1, 1 => 14
  | 0, 0, -1, 1 => 15
  | _, _, _, _ => 0

theorem ternaryMinG2_sound :
    ternaryMinG2Dag.Valid ∧ ternaryMinG2Dag.isPureAddSub ∧
    ternaryMinG2Dag.gates.length = ternaryLowerBound 2 ∧
    dagDepth ternaryMinG2Dag = ceilLog2 2 ∧
    computesAllTernary ternaryMinG2Dag :=
  ⟨checkDagValid_true (by decide), checkPureAddSub_true (by decide),
   by decide, by decide, checkWireMap_true (wireOf := wireOfTernary2) (by decide)⟩

theorem ternaryMinG3_sound :
    ternaryMinG3Dag.Valid ∧ ternaryMinG3Dag.isPureAddSub ∧
    ternaryMinG3Dag.gates.length = ternaryLowerBound 3 ∧
    dagDepth ternaryMinG3Dag = ceilLog2 3 ∧
    computesAllTernary ternaryMinG3Dag :=
  ⟨checkDagValid_true (by decide), checkPureAddSub_true (by decide),
   by decide, by decide, checkWireMap_true (wireOf := wireOfTernary3) (by decide)⟩

theorem ternaryMinG4_sound :
    ternaryMinG4Dag.Valid ∧ ternaryMinG4Dag.isPureAddSub ∧
    ternaryMinG4Dag.gates.length = ternaryLowerBound 4 ∧
    dagDepth ternaryMinG4Dag = ceilLog2 4 ∧
    computesAllTernary ternaryMinG4Dag :=
  ⟨checkDagValid_true (by decide), checkPureAddSub_true (by decide),
   by decide, by decide, checkWireMap_true (wireOf := wireOfTernary4) (by decide)⟩

theorem ternarySparse2of4_sound :
    ternarySparse2of4Dag.Valid ∧ ternarySparse2of4Dag.isPureAddSub ∧
    ternarySparse2of4Dag.gates.length = 12 ∧
    dagDepth ternarySparse2of4Dag = 1 ∧
    countBoundedTernary 4 2 = 16 ∧
    computesBoundedTernary ternarySparse2of4Dag 2 :=
  ⟨checkDagValid_true (by decide), checkPureAddSub_true (by decide),
   rfl, by decide, by decide, checkBoundedWireMap_true (wireOf := wireOfSparse2of4) (by decide)⟩

/-- Headline Theorem 3 (`ternary_lut_dag_bounds_and_symmetry`):
    Proves exact symmetry-halved ternary LUT size `2 * ternaryFoldedSize g + 1 = 3 ^ g`
    (`4, 13, 40, 121` for `g = 2, 3, 4, 5`), universal lower bounds `(3^g - 1)/2 - g` ops
    and `ceilLog2 g` depth, exact soundness & zero-waste optimality of the minimal ternary
    DAGs for `g = 2, 3, 4`, and the structured `(≤2, 4)` ternary sparsity DAG (`12 ops, depth 1`,
    `16` entries vs `40`). -/
theorem ternary_lut_dag_bounds_and_symmetry :
    (∀ g : Nat, 2 * ternaryFoldedSize g + 1 = 3 ^ g) ∧
    (ternaryFoldedSize 2 = 4 ∧ ternaryFoldedSize 3 = 13 ∧
     ternaryFoldedSize 4 = 40 ∧ ternaryFoldedSize 5 = 121) ∧
    (ternaryLowerBound 2 = 2 ∧ ternaryLowerBound 3 = 10 ∧
     ternaryLowerBound 4 = 36 ∧ ternaryLowerBound 5 = 116) ∧
    (∀ (g : Nat) (dag : LinearDag g), computesAllTernary dag →
      ternaryLowerBound g ≤ dag.gates.length) ∧
    (∀ (g : Nat) (dag : LinearDag g), 1 ≤ g → computesAllTernary dag →
      g ≤ 2 ^ dagDepth dag ∧ ceilLog2 g ≤ dagDepth dag) ∧
    (ternaryMinG2Dag.Valid ∧ ternaryMinG2Dag.isPureAddSub ∧
     ternaryMinG2Dag.gates.length = 2 ∧ dagDepth ternaryMinG2Dag = 1 ∧
     computesAllTernary ternaryMinG2Dag) ∧
    (ternaryMinG3Dag.Valid ∧ ternaryMinG3Dag.isPureAddSub ∧
     ternaryMinG3Dag.gates.length = 10 ∧ dagDepth ternaryMinG3Dag = 2 ∧
     computesAllTernary ternaryMinG3Dag) ∧
    (ternaryMinG4Dag.Valid ∧ ternaryMinG4Dag.isPureAddSub ∧
     ternaryMinG4Dag.gates.length = 36 ∧ dagDepth ternaryMinG4Dag = 2 ∧
     computesAllTernary ternaryMinG4Dag) ∧
    (ternarySparse2of4Dag.Valid ∧ ternarySparse2of4Dag.isPureAddSub ∧
     ternarySparse2of4Dag.gates.length = 12 ∧ dagDepth ternarySparse2of4Dag = 1 ∧
     countBoundedTernary 4 2 = 16 ∧ computesBoundedTernary ternarySparse2of4Dag 2) :=
  ⟨two_mul_ternaryFoldedSize_add_one,
   ternary_sizes_exact.1,
   ternary_sizes_exact.2,
   fun _ dag hcomp => ternary_dag_lower_bound_universal dag hcomp,
   fun _ dag hg hcomp => ternary_dag_depth_lower_bound_universal hg dag hcomp,
   ternaryMinG2_sound,
   ternaryMinG3_sound,
   ternaryMinG4_sound,
   ternarySparse2of4_sound⟩

end BitSerialLutDag
