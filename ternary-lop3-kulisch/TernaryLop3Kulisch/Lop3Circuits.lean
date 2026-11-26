/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TernaryLop3Kulisch.Defs

/-!
# Exact Minimal-`LOP3` Ternary & Harley–Seal Counter Theorems

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. `ternary_k2_4_lop3_exact_and_lb`: Exhaustive verification of the 4-`LOP3` `K=2` balanced-ternary
   counter across all 9 valid states + exact general-DAG lower bound `dag.length ≥ 4`.
2. `ternary_k3_7_lop3_exact`: Exhaustive verification of the 7-`LOP3` depth-3 `K=3` balanced-ternary
   counter across all 27 valid states + general-DAG fan-in lower bound `dag.length ≥ 5`.
3. `harley_seal_n7_8_lop3_exact_and_lb`: Exhaustive verification of the 8-`LOP3` depth-3 `N=7`
   Harley–Seal 7→3 compressor across all 128 inputs + general-DAG fan-in lower bound `dag.length ≥ 5`.
-/

namespace TernaryLop3Kulisch

/-! ## 1. General `Lop3Dag` Wire & Support-Size Machinery -/

theorem evalDagGo_length (wires : List Bool) (dag : Lop3Dag) :
    (evalDagGo wires dag).length = wires.length + dag.length := by
  induction dag generalizing wires with
  | nil => simp [evalDagGo]
  | cons g rest ih =>
    simp only [evalDagGo, ih, List.length_append, List.length_cons, List.length_nil]
    omega

theorem evalDag_length {n : Nat} (dag : Lop3Dag) (x : Fin n → Bool) :
    (evalDag dag x).length = n + dag.length := by
  unfold evalDag
  rw [evalDagGo_length, List.length_map, List.length_finRange]

theorem getD_append_left {α : Type} (l₁ l₂ : List α) (i : Nat) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD, List.getElem?_append_left hi]

theorem getD_append_singleton_end {α : Type} (l : List α) (a d : α) (k : Nat) (hk : l.length = k) :
    (l ++ [a]).getD k d = a := by
  subst hk
  simp [List.getD]

theorem evalDagGo_getD_lt (wires : List Bool) (dag : Lop3Dag) (k : Nat) (hk : k < wires.length) :
    (evalDagGo wires dag).getD k false = wires.getD k false := by
  induction dag generalizing wires with
  | nil => rfl
  | cons g rest ih =>
    unfold evalDagGo
    have hk' : k < (wires ++ [lop3 g.imm8 (wires.getD g.a false) (wires.getD g.b false) (wires.getD g.c false)]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih _ hk', getD_append_left _ _ _ _ hk]

theorem evalWire_input {n : Nat} (dag : Lop3Dag) (x : Fin n → Bool) (w : Nat) (hw : w < n) :
    evalWire dag x w = x ⟨w, hw⟩ := by
  unfold evalWire evalDag
  have hlen : w < ((List.finRange n).map x).length := by
    simp only [List.length_map, List.length_finRange]
    exact hw
  rw [evalDagGo_getD_lt _ _ _ hlen]
  simp only [List.getD, List.getElem?_eq_getElem hlen, List.getElem_map, List.getElem_finRange]
  rfl

theorem evalWire_ge_len {n : Nat} (dag : Lop3Dag) (x : Fin n → Bool) (w : Nat)
    (hw : n + dag.length ≤ w) :
    evalWire dag x w = false := by
  unfold evalWire
  have hlen : (evalDag dag x).length ≤ w := by
    rw [evalDag_length]
    exact hw
  simp only [List.getD, List.getElem?_eq_none hlen, Option.getD_none]

theorem evalWire_gate0 {n : Nat} (g : Lop3Gate) (rest : Lop3Dag) (x : Fin n → Bool) :
    evalWire (g :: rest) x n =
      lop3 g.imm8 (evalWire [] x g.a) (evalWire [] x g.b) (evalWire [] x g.c) := by
  unfold evalWire evalDag evalDagGo
  dsimp only
  let w0 := (List.finRange n).map x
  have hw0 : w0.length = n := by simp [w0]
  have hn : n < (w0 ++ [lop3 g.imm8 (w0.getD g.a false) (w0.getD g.b false) (w0.getD g.c false)]).length := by
    simp [hw0]
  change (evalDagGo (w0 ++ [lop3 g.imm8 (w0.getD g.a false) (w0.getD g.b false) (w0.getD g.c false)]) rest).getD n false =
    lop3 g.imm8 (w0.getD g.a false) (w0.getD g.b false) (w0.getD g.c false)
  rw [evalDagGo_getD_lt _ _ _ hn]
  exact getD_append_singleton_end w0 _ false n hw0

theorem evalWire_gate1 {n : Nat} (g0 g1 : Lop3Gate) (rest : Lop3Dag) (x : Fin n → Bool) :
    evalWire (g0 :: g1 :: rest) x (n + 1) =
      lop3 g1.imm8 (evalWire [g0] x g1.a) (evalWire [g0] x g1.b) (evalWire [g0] x g1.c) := by
  unfold evalWire evalDag evalDagGo
  dsimp only
  let w0 := (List.finRange n).map x
  let w1 := w0 ++ [lop3 g0.imm8 (w0.getD g0.a false) (w0.getD g0.b false) (w0.getD g0.c false)]
  have hw1 : w1.length = n + 1 := by simp [w1, w0]
  have hn1 : n + 1 < (w1 ++ [lop3 g1.imm8 (w1.getD g1.a false) (w1.getD g1.b false) (w1.getD g1.c false)]).length := by
    simp [hw1]
  change (evalDagGo (w1 ++ [lop3 g1.imm8 (w1.getD g1.a false) (w1.getD g1.b false) (w1.getD g1.c false)]) rest).getD (n + 1) false =
    lop3 g1.imm8 (w1.getD g1.a false) (w1.getD g1.b false) (w1.getD g1.c false)
  rw [evalDagGo_getD_lt _ _ _ hn1]
  exact getD_append_singleton_end w1 _ false (n + 1) hw1

/-- A Boolean function on `Fin n → Bool` depends only on coordinates in `S`. -/
def DependsOnSubset {n : Nat} (S : List (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → f x = f y

/-- Single-input support list for a wire index `u` relative to `n` primary inputs. -/
def wireInSupport (n u : Nat) : List (Fin n) :=
  if h : u < n then [⟨u, h⟩] else []

theorem wireInSupport_length_le (n u : Nat) : (wireInSupport n u).length ≤ 1 := by
  unfold wireInSupport
  split <;> simp

theorem dependsOnSubset_evalWire_nil {n : Nat} (u : Nat) :
    DependsOnSubset (wireInSupport n u) (fun x => evalWire [] x u) := by
  intro x y hxy
  dsimp only
  unfold wireInSupport at hxy
  by_cases hu : u < n
  · rw [evalWire_input _ _ _ hu, evalWire_input _ _ _ hu]
    simp only [hu, ↓reduceDIte, List.mem_singleton] at hxy
    exact hxy ⟨u, hu⟩ rfl
  · have hge : n + ([] : Lop3Dag).length ≤ u := by simp; omega
    rw [evalWire_ge_len _ _ _ hge, evalWire_ge_len _ _ _ hge]

theorem dependsOnSubset_lop3 {n : Nat} {Sa Sb Sc : List (Fin n)}
    {fa fb fc : (Fin n → Bool) → Bool} (imm8 : UInt8)
    (ha : DependsOnSubset Sa fa) (hb : DependsOnSubset Sb fb) (hc : DependsOnSubset Sc fc) :
    DependsOnSubset (Sa ++ Sb ++ Sc) (fun x => lop3 imm8 (fa x) (fb x) (fc x)) := by
  intro x y hxy
  dsimp only
  have h1 : fa x = fa y := ha x y (fun i hi => hxy i (by simp [hi]))
  have h2 : fb x = fb y := hb x y (fun i hi => hxy i (by simp [hi]))
  have h3 : fc x = fc y := hc x y (fun i hi => hxy i (by simp [hi]))
  rw [h1, h2, h3]

/-- Support list of gate 0 (`wire n`): at most 3 primary inputs. -/
def gate0Support (n : Nat) (g0 : Lop3Gate) : List (Fin n) :=
  wireInSupport n g0.a ++ wireInSupport n g0.b ++ wireInSupport n g0.c

theorem gate0Support_length_le (n : Nat) (g0 : Lop3Gate) :
    (gate0Support n g0).length ≤ 3 := by
  unfold gate0Support
  have ha := wireInSupport_length_le n g0.a
  have hb := wireInSupport_length_le n g0.b
  have hc := wireInSupport_length_le n g0.c
  simp only [List.length_append]
  omega

theorem dependsOnSubset_gate0 {n : Nat} (g0 : Lop3Gate) (rest : Lop3Dag) :
    DependsOnSubset (gate0Support n g0) (fun x => evalWire (g0 :: rest) x n) := by
  intro x y hxy
  dsimp only
  rw [evalWire_gate0, evalWire_gate0]
  exact dependsOnSubset_lop3 g0.imm8
    (dependsOnSubset_evalWire_nil g0.a)
    (dependsOnSubset_evalWire_nil g0.b)
    (dependsOnSubset_evalWire_nil g0.c) x y hxy

theorem evalWire_singleton_eq {n : Nat} (g0 : Lop3Gate) (u : Nat) :
    DependsOnSubset (if u = n then gate0Support n g0 else wireInSupport n u)
      (fun x => evalWire [g0] x u) := by
  split
  · next h =>
    subst h
    exact dependsOnSubset_gate0 g0 []
  · next h =>
    intro x y hxy
    dsimp only
    by_cases hu : u < n
    · rw [evalWire_input _ _ _ hu, evalWire_input _ _ _ hu]
      unfold wireInSupport at hxy
      simp only [hu, ↓reduceDIte, List.mem_singleton] at hxy
      exact hxy ⟨u, hu⟩ rfl
    · have hge : n + ([g0] : Lop3Dag).length ≤ u := by simp; omega
      rw [evalWire_ge_len _ _ _ hge, evalWire_ge_len _ _ _ hge]

/-- Any wire `w ≤ n` in any `Lop3Dag` on `n` inputs depends on at most 3 inputs. -/
theorem exists_support_le_three_of_le_n {n : Nat} (dag : Lop3Dag) (w : Nat) (hw : w ≤ n) :
    ∃ S : List (Fin n), S.length ≤ 3 ∧ DependsOnSubset S (fun x => evalWire dag x w) := by
  by_cases hlt : w < n
  · refine ⟨[⟨w, hlt⟩], by simp, ?_⟩
    intro x y hxy
    dsimp only
    rw [evalWire_input _ _ _ hlt, evalWire_input _ _ _ hlt]
    exact hxy ⟨w, hlt⟩ (by simp)
  · have heq : w = n := by omega
    rw [heq]
    cases dag with
    | nil =>
      refine ⟨[], by simp, ?_⟩
      intro x y _
      dsimp only
      rw [evalWire_ge_len _ _ _ (by simp), evalWire_ge_len _ _ _ (by simp)]
    | cons g0 rest =>
      exact ⟨gate0Support n g0, gate0Support_length_le n g0, dependsOnSubset_gate0 g0 rest⟩

/-- Gate 1 (`wire n + 1`) depends on at most 5 primary inputs. -/
theorem exists_support_le_five_gate1 {n : Nat} (g0 g1 : Lop3Gate) (rest : Lop3Dag) :
    ∃ S : List (Fin n), S.length ≤ 5 ∧
      DependsOnSubset S (fun x => evalWire (g0 :: g1 :: rest) x (n + 1)) := by
  by_cases huse : g1.a = n ∨ g1.b = n ∨ g1.c = n
  · let extra : List (Fin n) :=
      (if g1.a = n then [] else wireInSupport n g1.a) ++
      (if g1.b = n then [] else wireInSupport n g1.b) ++
      (if g1.c = n then [] else wireInSupport n g1.c)
    have hextra : extra.length ≤ 2 := by
      have ha := wireInSupport_length_le n g1.a
      have hb := wireInSupport_length_le n g1.b
      have hc := wireInSupport_length_le n g1.c
      rcases huse with ha' | hb' | hc'
      · simp only [extra, ha', ↓reduceIte, List.length_append, List.length_nil]
        split <;> split <;> simp <;> omega
      · simp only [extra, hb', ↓reduceIte, List.length_append, List.length_nil]
        split <;> split <;> simp <;> omega
      · simp only [extra, hc', ↓reduceIte, List.length_append, List.length_nil]
        split <;> split <;> simp <;> omega
    refine ⟨gate0Support n g0 ++ extra, ?_, ?_⟩
    · have h0 := gate0Support_length_le n g0
      simp only [List.length_append]
      omega
    · intro x y hxy
      dsimp only
      rw [evalWire_gate1, evalWire_gate1]
      have ha : evalWire [g0] x g1.a = evalWire [g0] y g1.a := by
        apply evalWire_singleton_eq g0 g1.a x y
        intro i hi
        by_cases h : g1.a = n
        · simp only [h, ↓reduceIte] at hi
          exact hxy i (by simp [hi])
        · simp only [h, ↓reduceIte] at hi
          exact hxy i (by simp [extra, h, hi])
      have hb : evalWire [g0] x g1.b = evalWire [g0] y g1.b := by
        apply evalWire_singleton_eq g0 g1.b x y
        intro i hi
        by_cases h : g1.b = n
        · simp only [h, ↓reduceIte] at hi
          exact hxy i (by simp [hi])
        · simp only [h, ↓reduceIte] at hi
          exact hxy i (by simp [extra, h, hi])
      have hc : evalWire [g0] x g1.c = evalWire [g0] y g1.c := by
        apply evalWire_singleton_eq g0 g1.c x y
        intro i hi
        by_cases h : g1.c = n
        · simp only [h, ↓reduceIte] at hi
          exact hxy i (by simp [hi])
        · simp only [h, ↓reduceIte] at hi
          exact hxy i (by simp [extra, h, hi])
      rw [ha, hb, hc]
  · have hna : g1.a ≠ n := fun h => huse (Or.inl h)
    have hnb : g1.b ≠ n := fun h => huse (Or.inr (Or.inl h))
    have hnc : g1.c ≠ n := fun h => huse (Or.inr (Or.inr h))
    refine ⟨wireInSupport n g1.a ++ wireInSupport n g1.b ++ wireInSupport n g1.c, ?_, ?_⟩
    · have ha := wireInSupport_length_le n g1.a
      have hb := wireInSupport_length_le n g1.b
      have hc := wireInSupport_length_le n g1.c
      simp only [List.length_append]
      omega
    · intro x y hxy
      dsimp only
      rw [evalWire_gate1, evalWire_gate1]
      have ha : evalWire [g0] x g1.a = evalWire [g0] y g1.a := by
        apply evalWire_singleton_eq g0 g1.a x y
        intro i hi
        simp only [hna, ↓reduceIte] at hi
        exact hxy i (by simp [hi])
      have hb : evalWire [g0] x g1.b = evalWire [g0] y g1.b := by
        apply evalWire_singleton_eq g0 g1.b x y
        intro i hi
        simp only [hnb, ↓reduceIte] at hi
        exact hxy i (by simp [hi])
      have hc : evalWire [g0] x g1.c = evalWire [g0] y g1.c := by
        apply evalWire_singleton_eq g0 g1.c x y
        intro i hi
        simp only [hnc, ↓reduceIte] at hi
        exact hxy i (by simp [hi])
      rw [ha, hb, hc]

/-- Any wire `w ≤ n + 1` in any `Lop3Dag` on `n` inputs depends on at most 5 primary inputs. -/
theorem exists_support_le_five_of_le_n_add_one {n : Nat} (dag : Lop3Dag) (w : Nat) (hw : w ≤ n + 1) :
    ∃ S : List (Fin n), S.length ≤ 5 ∧ DependsOnSubset S (fun x => evalWire dag x w) := by
  by_cases hle : w ≤ n
  · rcases exists_support_le_three_of_le_n dag w hle with ⟨S, hlen, hdep⟩
    exact ⟨S, by omega, hdep⟩
  · have heq : w = n + 1 := by omega
    subst heq
    cases dag with
    | nil =>
      refine ⟨[], by simp, ?_⟩
      intro x y _
      dsimp only
      rw [evalWire_ge_len _ _ _ (by simp), evalWire_ge_len _ _ _ (by simp)]
    | cons g0 rest =>
      cases rest with
      | nil =>
        refine ⟨[], by simp, ?_⟩
        intro x y _
        dsimp only
        rw [evalWire_ge_len _ _ _ (by simp), evalWire_ge_len _ _ _ (by simp)]
      | cons g1 rest2 =>
        exact exists_support_le_five_gate1 g0 g1 rest2

/-- Pigeonhole on `Fin n`: any list `S : List (Fin n)` of length `< n` misses at least one coordinate. -/
theorem exists_not_mem_of_length_lt {n : Nat} (S : List (Fin n)) (hlen : S.length < n) :
    ∃ i : Fin n, i ∉ S := by
  apply Classical.byContradiction
  intro hall
  have hsub : ∀ i ∈ List.finRange n, i ∈ S := by
    intro i _
    exact Classical.byContradiction (fun hni => hall ⟨i, hni⟩)
  have hle : (List.finRange n).length ≤ S.length := by
    have haux : ∀ (l₁ l₂ : List (Fin n)), l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length := by
      intro l₁
      induction l₁ with
      | nil => intro _ _ _; exact Nat.zero_le _
      | cons a t ih =>
        intro l₂ hnd hs
        rw [List.nodup_cons] at hnd
        have ha : a ∈ l₂ := hs a (List.mem_cons_self ..)
        have ht : ∀ x ∈ t, x ∈ l₂.erase a := by
          intro x hx
          have hne : x ≠ a := fun heq => hnd.1 (heq ▸ hx)
          exact (List.mem_erase_of_ne hne).mpr (hs x (List.mem_cons_of_mem a hx))
        have h1 := ih (l₂.erase a) hnd.2 ht
        have h2 : (l₂.erase a).length = l₂.length - 1 := List.length_erase_of_mem ha
        have hpos : 0 < l₂.length := List.length_pos_of_mem ha
        simp only [List.length_cons]
        omega
    exact haux (List.finRange n) S (List.nodup_finRange n) hsub
  rw [List.length_finRange] at hle
  omega

/-- Helper to update a single coordinate of `x : Fin n → Bool`. -/
def setCoord {n : Nat} (x : Fin n → Bool) (i : Fin n) (v : Bool) : Fin n → Bool :=
  fun j => if j = i then v else x j

theorem setCoord_eq_outside {n : Nat} (x : Fin n → Bool) (i : Fin n) (v : Bool)
    (S : List (Fin n)) (hni : i ∉ S) :
    ∀ j ∈ S, setCoord x i v j = x j := by
  intro j hj
  unfold setCoord
  have hne : j ≠ i := fun heq => hni (heq ▸ hj)
  simp [hne]

/-! ## 2. Theorem 1: Exact 4-`LOP3` `K=2` Balanced-Ternary Counter & Exact `≥ 4` Lower Bound -/

theorem ternaryK2Lop3_exact :
    ∀ p0 n0 p1 n1 : Bool,
      tritValid p0 n0 = true → tritValid p1 n1 = true →
      let (s0, s1, s2) := ternaryK2Lop3 p0 n0 p1 n1
      twosComp3 s0 s1 s2 = tritVal p0 n0 + tritVal p1 n1 := by
  decide

theorem ternaryK2Dag_exact :
    ternaryK2Dag.length = 4 ∧
    ∀ x : Fin 4 → Bool, validK2 x →
      twosComp3 (evalWire ternaryK2Dag x 5) (evalWire ternaryK2Dag x 7) (evalWire ternaryK2Dag x 6) =
        tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
        tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) := by
  refine ⟨rfl, ?_⟩
  intro x hx
  rcases hx with ⟨h01, h23⟩
  have hEq :
      (evalWire ternaryK2Dag x 5, evalWire ternaryK2Dag x 7, evalWire ternaryK2Dag x 6) =
      ternaryK2Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) := by
    rfl
  have h5 : evalWire ternaryK2Dag x 5 = (ternaryK2Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩)).1 :=
    congrArg Prod.fst hEq
  have h7 : evalWire ternaryK2Dag x 7 = (ternaryK2Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩)).2.1 :=
    congrArg (fun p => p.2.1) hEq
  have h6 : evalWire ternaryK2Dag x 6 = (ternaryK2Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩)).2.2 :=
    congrArg (fun p => p.2.2) hEq
  rw [h5, h7, h6]
  exact ternaryK2Lop3_exact _ _ _ _ h01 h23

def vec4 (b0 b1 b2 b3 : Bool) : Fin 4 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3

theorem twosComp3_bits_unique (s0 s1 s2 t0 t1 t2 : Bool)
    (h : twosComp3 s0 s1 s2 = twosComp3 t0 t1 t2) :
    s0 = t0 ∧ s1 = t1 ∧ s2 = t2 := by
  revert h
  cases s0 <;> cases s1 <;> cases s2 <;> cases t0 <;> cases t1 <;> cases t2 <;> decide

/-- Exact general-DAG lower bound for `K=2` balanced ternary:
    NO `Lop3Dag` with `< 4` gates can compute the 3-bit two's-complement sum on all 9 valid states. -/
theorem ternaryK2_dag_ge_4 (dag : Lop3Dag) (o0 o1 o2 : Nat)
    (hspec : ∀ x : Fin 4 → Bool, validK2 x →
      twosComp3 (evalWire dag x o0) (evalWire dag x o1) (evalWire dag x o2) =
        tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
        tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩)) :
    4 ≤ dag.length := by
  have hbits : ∀ b0 b1 b2 b3 : Bool,
      tritValid b0 b1 = true → tritValid b2 b3 = true →
      evalWire dag (vec4 b0 b1 b2 b3) o0 = (ternaryK2Lop3 b0 b1 b2 b3).1 ∧
      evalWire dag (vec4 b0 b1 b2 b3) o1 = (ternaryK2Lop3 b0 b1 b2 b3).2.1 ∧
      evalWire dag (vec4 b0 b1 b2 b3) o2 = (ternaryK2Lop3 b0 b1 b2 b3).2.2 := by
    intro b0 b1 b2 b3 h01 h23
    have h1 := hspec (vec4 b0 b1 b2 b3) ⟨h01, h23⟩
    have h2 : twosComp3 (ternaryK2Lop3 b0 b1 b2 b3).1 (ternaryK2Lop3 b0 b1 b2 b3).2.1
        (ternaryK2Lop3 b0 b1 b2 b3).2.2 = tritVal b0 b1 + tritVal b2 b3 :=
      ternaryK2Lop3_exact b0 b1 b2 b3 h01 h23
    have h3 : twosComp3 (evalWire dag (vec4 b0 b1 b2 b3) o0)
        (evalWire dag (vec4 b0 b1 b2 b3) o1) (evalWire dag (vec4 b0 b1 b2 b3) o2) =
        twosComp3 (ternaryK2Lop3 b0 b1 b2 b3).1 (ternaryK2Lop3 b0 b1 b2 b3).2.1
          (ternaryK2Lop3 b0 b1 b2 b3).2.2 := by
      dsimp only [vec4] at h1
      rw [h1, h2]
    exact twosComp3_bits_unique _ _ _ _ _ _ h3
  have ho0_gt : 4 < o0 := by
    apply Nat.lt_of_not_le
    intro hle
    rcases exists_support_le_three_of_le_n dag o0 hle with ⟨S, hSlen, hSdep⟩
    rcases exists_not_mem_of_length_lt S (by omega) with ⟨i, hi⟩
    rcases i with ⟨iv, hiv⟩
    match iv with
    | 0 =>
      have heq := hSdep (vec4 false false false false) (vec4 true false false false)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 0 := fun h => hi (by subst h; exact hj)
          match jv with
          | 0 => exact absurd rfl hne
          | 1 => rfl | 2 => rfl | 3 => rfl)
      dsimp only at heq
      rw [(hbits false false false false rfl rfl).1, (hbits true false false false rfl rfl).1] at heq
      exact absurd heq (by decide)
    | 1 =>
      have heq := hSdep (vec4 false false false false) (vec4 false true false false)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 1 := fun h => hi (by subst h; exact hj)
          match jv with
          | 1 => exact absurd rfl hne
          | 0 => rfl | 2 => rfl | 3 => rfl)
      dsimp only at heq
      rw [(hbits false false false false rfl rfl).1, (hbits false true false false rfl rfl).1] at heq
      exact absurd heq (by decide)
    | 2 =>
      have heq := hSdep (vec4 false false false false) (vec4 false false true false)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 2 := fun h => hi (by subst h; exact hj)
          match jv with
          | 2 => exact absurd rfl hne
          | 0 => rfl | 1 => rfl | 3 => rfl)
      dsimp only at heq
      rw [(hbits false false false false rfl rfl).1, (hbits false false true false rfl rfl).1] at heq
      exact absurd heq (by decide)
    | 3 =>
      have heq := hSdep (vec4 false false false false) (vec4 false false false true)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 3 := fun h => hi (by subst h; exact hj)
          match jv with
          | 3 => exact absurd rfl hne
          | 0 => rfl | 1 => rfl | 2 => rfl)
      dsimp only at heq
      rw [(hbits false false false false rfl rfl).1, (hbits false false false true rfl rfl).1] at heq
      exact absurd heq (by decide)
  have ho1_gt : 4 < o1 := by
    apply Nat.lt_of_not_le
    intro hle
    rcases exists_support_le_three_of_le_n dag o1 hle with ⟨S, hSlen, hSdep⟩
    rcases exists_not_mem_of_length_lt S (by omega) with ⟨i, hi⟩
    rcases i with ⟨iv, hiv⟩
    match iv with
    | 0 =>
      have heq := hSdep (vec4 false false true false) (vec4 true false true false)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 0 := fun h => hi (by subst h; exact hj)
          match jv with | 0 => exact absurd rfl hne | 1 => rfl | 2 => rfl | 3 => rfl)
      dsimp only at heq
      rw [(hbits false false true false rfl rfl).2.1, (hbits true false true false rfl rfl).2.1] at heq
      exact absurd heq (by decide)
    | 1 =>
      have heq := hSdep (vec4 false false false false) (vec4 false true false false)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 1 := fun h => hi (by subst h; exact hj)
          match jv with | 1 => exact absurd rfl hne | 0 => rfl | 2 => rfl | 3 => rfl)
      dsimp only at heq
      rw [(hbits false false false false rfl rfl).2.1, (hbits false true false false rfl rfl).2.1] at heq
      exact absurd heq (by decide)
    | 2 =>
      have heq := hSdep (vec4 true false false false) (vec4 true false true false)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 2 := fun h => hi (by subst h; exact hj)
          match jv with | 2 => exact absurd rfl hne | 0 => rfl | 1 => rfl | 3 => rfl)
      dsimp only at heq
      rw [(hbits true false false false rfl rfl).2.1, (hbits true false true false rfl rfl).2.1] at heq
      exact absurd heq (by decide)
    | 3 =>
      have heq := hSdep (vec4 false false false false) (vec4 false false false true)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 3 := fun h => hi (by subst h; exact hj)
          match jv with | 3 => exact absurd rfl hne | 0 => rfl | 1 => rfl | 2 => rfl)
      dsimp only at heq
      rw [(hbits false false false false rfl rfl).2.1, (hbits false false false true rfl rfl).2.1] at heq
      exact absurd heq (by decide)
  have ho2_gt : 4 < o2 := by
    apply Nat.lt_of_not_le
    intro hle
    rcases exists_support_le_three_of_le_n dag o2 hle with ⟨S, hSlen, hSdep⟩
    rcases exists_not_mem_of_length_lt S (by omega) with ⟨i, hi⟩
    rcases i with ⟨iv, hiv⟩
    match iv with
    | 0 =>
      have heq := hSdep (vec4 false false false true) (vec4 true false false true)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 0 := fun h => hi (by subst h; exact hj)
          match jv with | 0 => exact absurd rfl hne | 1 => rfl | 2 => rfl | 3 => rfl)
      dsimp only at heq
      rw [(hbits false false false true rfl rfl).2.2, (hbits true false false true rfl rfl).2.2] at heq
      exact absurd heq (by decide)
    | 1 =>
      have heq := hSdep (vec4 false false false false) (vec4 false true false false)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 1 := fun h => hi (by subst h; exact hj)
          match jv with | 1 => exact absurd rfl hne | 0 => rfl | 2 => rfl | 3 => rfl)
      dsimp only at heq
      rw [(hbits false false false false rfl rfl).2.2, (hbits false true false false rfl rfl).2.2] at heq
      exact absurd heq (by decide)
    | 2 =>
      have heq := hSdep (vec4 false true false false) (vec4 false true true false)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 2 := fun h => hi (by subst h; exact hj)
          match jv with | 2 => exact absurd rfl hne | 0 => rfl | 1 => rfl | 3 => rfl)
      dsimp only at heq
      rw [(hbits false true false false rfl rfl).2.2, (hbits false true true false rfl rfl).2.2] at heq
      exact absurd heq (by decide)
    | 3 =>
      have heq := hSdep (vec4 false false false false) (vec4 false false false true)
        (fun j hj => by
          rcases j with ⟨jv, hjv⟩
          have hne : jv ≠ 3 := fun h => hi (by subst h; exact hj)
          match jv with | 3 => exact absurd rfl hne | 0 => rfl | 1 => rfl | 2 => rfl)
      dsimp only at heq
      rw [(hbits false false false false rfl rfl).2.2, (hbits false false false true rfl rfl).2.2] at heq
      exact absurd heq (by decide)
  have ho0_lt : o0 < 4 + dag.length := by
    apply Nat.lt_of_not_le
    intro hge
    have h := evalWire_ge_len dag (vec4 true false false false) o0 hge
    rw [(hbits true false false false rfl rfl).1] at h
    exact absurd h (by decide)
  have ho1_lt : o1 < 4 + dag.length := by
    apply Nat.lt_of_not_le
    intro hge
    have h := evalWire_ge_len dag (vec4 false true false false) o1 hge
    rw [(hbits false true false false rfl rfl).2.1] at h
    exact absurd h (by decide)
  have ho2_lt : o2 < 4 + dag.length := by
    apply Nat.lt_of_not_le
    intro hge
    have h := evalWire_ge_len dag (vec4 false true false false) o2 hge
    rw [(hbits false true false false rfl rfl).2.2] at h
    exact absurd h (by decide)
  have h01 : o0 ≠ o1 := by
    intro heq
    have hA := hbits true false false false rfl rfl
    have h1 := hA.1; have h2 := hA.2.1
    rw [heq] at h1; rw [h1] at h2; exact absurd h2 (by decide)
  have h02 : o0 ≠ o2 := by
    intro heq
    have hA := hbits true false false false rfl rfl
    have h1 := hA.1; have h2 := hA.2.2
    rw [heq] at h1; rw [h1] at h2; exact absurd h2 (by decide)
  have h12 : o1 ≠ o2 := by
    intro heq
    have hA := hbits true false true false rfl rfl
    have h1 := hA.2.1; have h2 := hA.2.2
    rw [heq] at h1; rw [h1] at h2; exact absurd h2 (by decide)
  omega

/-- Headline Theorem 1: Exact 4-`LOP3` `K=2` balanced-ternary counter + exact `≥ 4` lower bound. -/
theorem ternary_k2_4_lop3_exact_and_lb :
    (∀ p0 n0 p1 n1 : Bool,
      tritValid p0 n0 = true → tritValid p1 n1 = true →
      let (s0, s1, s2) := ternaryK2Lop3 p0 n0 p1 n1
      twosComp3 s0 s1 s2 = tritVal p0 n0 + tritVal p1 n1) ∧
    (ternaryK2Dag.length = 4 ∧
      ∀ x : Fin 4 → Bool, validK2 x →
        twosComp3 (evalWire ternaryK2Dag x 5) (evalWire ternaryK2Dag x 7) (evalWire ternaryK2Dag x 6) =
          tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
          tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩)) ∧
    (∀ (dag : Lop3Dag) (o0 o1 o2 : Nat),
      (∀ x : Fin 4 → Bool, validK2 x →
        twosComp3 (evalWire dag x o0) (evalWire dag x o1) (evalWire dag x o2) =
          tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
          tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩)) →
      4 ≤ dag.length) :=
  ⟨ternaryK2Lop3_exact, ternaryK2Dag_exact, ternaryK2_dag_ge_4⟩

/-! ## 3. Theorem 2: Exact 7-`LOP3` Depth-3 `K=3` Balanced-Ternary Counter & `≥ 5` Fan-In Lower Bound -/

theorem ternaryK3Lop3_exact :
    ∀ p0 n0 p1 n1 p2 n2 : Bool,
      tritValid p0 n0 = true → tritValid p1 n1 = true → tritValid p2 n2 = true →
      let (s0, s1, s2) := ternaryK3Lop3 p0 n0 p1 n1 p2 n2
      twosComp3 s0 s1 s2 = tritVal p0 n0 + tritVal p1 n1 + tritVal p2 n2 := by
  decide

theorem ternaryK3Dag_exact :
    ternaryK3Dag.length = 7 ∧
    ∀ x : Fin 6 → Bool, validK3 x →
      twosComp3 (evalWire ternaryK3Dag x 8) (evalWire ternaryK3Dag x 11) (evalWire ternaryK3Dag x 12) =
        tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
        tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) +
        tritVal (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) := by
  refine ⟨rfl, ?_⟩
  intro x hx
  rcases hx with ⟨h01, h23, h45⟩
  have hEq :
      (evalWire ternaryK3Dag x 8, evalWire ternaryK3Dag x 11, evalWire ternaryK3Dag x 12) =
      ternaryK3Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩)
        (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) := by
    rfl
  have h8 : evalWire ternaryK3Dag x 8 = (ternaryK3Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩)).1 :=
    congrArg Prod.fst hEq
  have h11 : evalWire ternaryK3Dag x 11 = (ternaryK3Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩)).2.1 :=
    congrArg (fun p => p.2.1) hEq
  have h12 : evalWire ternaryK3Dag x 12 = (ternaryK3Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩)).2.2 :=
    congrArg (fun p => p.2.2) hEq
  rw [h8, h11, h12]
  exact ternaryK3Lop3_exact _ _ _ _ _ _ h01 h23 h45

def vec6 (b0 b1 b2 b3 b4 b5 : Bool) : Fin 6 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5

/-- General fan-in lower bound for `K=3` balanced ternary:
    every `LOP3` DAG computing the 3-bit two's-complement sum on all 27 valid states has `dag.length ≥ 5`. -/
theorem ternaryK3_dag_ge_5 (dag : Lop3Dag) (o0 o1 o2 : Nat)
    (hspec : ∀ x : Fin 6 → Bool, validK3 x →
      twosComp3 (evalWire dag x o0) (evalWire dag x o1) (evalWire dag x o2) =
        tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
        tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) +
        tritVal (x ⟨4, by decide⟩) (x ⟨5, by decide⟩)) :
    5 ≤ dag.length := by
  have hbits : ∀ b0 b1 b2 b3 b4 b5 : Bool,
      tritValid b0 b1 = true → tritValid b2 b3 = true → tritValid b4 b5 = true →
      evalWire dag (vec6 b0 b1 b2 b3 b4 b5) o0 = (ternaryK3Lop3 b0 b1 b2 b3 b4 b5).1 ∧
      evalWire dag (vec6 b0 b1 b2 b3 b4 b5) o1 = (ternaryK3Lop3 b0 b1 b2 b3 b4 b5).2.1 ∧
      evalWire dag (vec6 b0 b1 b2 b3 b4 b5) o2 = (ternaryK3Lop3 b0 b1 b2 b3 b4 b5).2.2 := by
    intro b0 b1 b2 b3 b4 b5 h01 h23 h45
    have h1 := hspec (vec6 b0 b1 b2 b3 b4 b5) ⟨h01, h23, h45⟩
    have h2 : twosComp3 (ternaryK3Lop3 b0 b1 b2 b3 b4 b5).1 (ternaryK3Lop3 b0 b1 b2 b3 b4 b5).2.1
        (ternaryK3Lop3 b0 b1 b2 b3 b4 b5).2.2 = tritVal b0 b1 + tritVal b2 b3 + tritVal b4 b5 :=
      ternaryK3Lop3_exact b0 b1 b2 b3 b4 b5 h01 h23 h45
    have h3 : twosComp3 (evalWire dag (vec6 b0 b1 b2 b3 b4 b5) o0)
        (evalWire dag (vec6 b0 b1 b2 b3 b4 b5) o1) (evalWire dag (vec6 b0 b1 b2 b3 b4 b5) o2) =
        twosComp3 (ternaryK3Lop3 b0 b1 b2 b3 b4 b5).1 (ternaryK3Lop3 b0 b1 b2 b3 b4 b5).2.1
          (ternaryK3Lop3 b0 b1 b2 b3 b4 b5).2.2 := by
      dsimp only [vec6] at h1
      rw [h1, h2]
    exact twosComp3_bits_unique _ _ _ _ _ _ h3
  have ho0_gt : 7 < o0 := by
    apply Nat.lt_of_not_le
    intro hle
    rcases exists_support_le_five_of_le_n_add_one dag o0 hle with ⟨S, hSlen, hSdep⟩
    rcases exists_not_mem_of_length_lt S (by omega) with ⟨⟨iv, hiv⟩, hi⟩
    have hflip : ∀ (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool),
        (∀ j : Fin 6, j.val ≠ iv → vec6 a0 a1 a2 a3 a4 a5 j = vec6 b0 b1 b2 b3 b4 b5 j) →
        evalWire dag (vec6 a0 a1 a2 a3 a4 a5) o0 = evalWire dag (vec6 b0 b1 b2 b3 b4 b5) o0 :=
      fun _ _ _ _ _ _ _ _ _ _ _ _ h => hSdep _ _ (fun j hj => h j (fun heq => hi (by
        have hjeq : j = ⟨iv, hiv⟩ := Fin.ext heq
        exact hjeq ▸ hj)))
    match iv with
    | 0 =>
      have heq := hflip false false false false false false true false false false false false (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).1,
          (hbits true false false false false false rfl rfl rfl).1] at heq
      exact absurd heq (by decide)
    | 1 =>
      have heq := hflip false false false false false false false true false false false false (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).1,
          (hbits false true false false false false rfl rfl rfl).1] at heq
      exact absurd heq (by decide)
    | 2 =>
      have heq := hflip false false false false false false false false true false false false (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).1,
          (hbits false false true false false false rfl rfl rfl).1] at heq
      exact absurd heq (by decide)
    | 3 =>
      have heq := hflip false false false false false false false false false true false false (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).1,
          (hbits false false false true false false rfl rfl rfl).1] at heq
      exact absurd heq (by decide)
    | 4 =>
      have heq := hflip false false false false false false false false false false true false (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).1,
          (hbits false false false false true false rfl rfl rfl).1] at heq
      exact absurd heq (by decide)
    | 5 =>
      have heq := hflip false false false false false false false false false false false true (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).1,
          (hbits false false false false false true rfl rfl rfl).1] at heq
      exact absurd heq (by decide)
  have ho1_gt : 7 < o1 := by
    apply Nat.lt_of_not_le
    intro hle
    rcases exists_support_le_five_of_le_n_add_one dag o1 hle with ⟨S, hSlen, hSdep⟩
    rcases exists_not_mem_of_length_lt S (by omega) with ⟨⟨iv, hiv⟩, hi⟩
    have hflip : ∀ (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool),
        (∀ j : Fin 6, j.val ≠ iv → vec6 a0 a1 a2 a3 a4 a5 j = vec6 b0 b1 b2 b3 b4 b5 j) →
        evalWire dag (vec6 a0 a1 a2 a3 a4 a5) o1 = evalWire dag (vec6 b0 b1 b2 b3 b4 b5) o1 :=
      fun _ _ _ _ _ _ _ _ _ _ _ _ h => hSdep _ _ (fun j hj => h j (fun heq => hi (by
        have hjeq : j = ⟨iv, hiv⟩ := Fin.ext heq
        exact hjeq ▸ hj)))
    match iv with
    | 0 =>
      have heq := hflip false false true false false false true false true false false false (by decide)
      rw [(hbits false false true false false false rfl rfl rfl).2.1,
          (hbits true false true false false false rfl rfl rfl).2.1] at heq
      exact absurd heq (by decide)
    | 1 =>
      have heq := hflip false false false false false false false true false false false false (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).2.1,
          (hbits false true false false false false rfl rfl rfl).2.1] at heq
      exact absurd heq (by decide)
    | 2 =>
      have heq := hflip true false false false false false true false true false false false (by decide)
      rw [(hbits true false false false false false rfl rfl rfl).2.1,
          (hbits true false true false false false rfl rfl rfl).2.1] at heq
      exact absurd heq (by decide)
    | 3 =>
      have heq := hflip false false false false false false false false false true false false (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).2.1,
          (hbits false false false true false false rfl rfl rfl).2.1] at heq
      exact absurd heq (by decide)
    | 4 =>
      have heq := hflip true false false false false false true false false false true false (by decide)
      rw [(hbits true false false false false false rfl rfl rfl).2.1,
          (hbits true false false false true false rfl rfl rfl).2.1] at heq
      exact absurd heq (by decide)
    | 5 =>
      have heq := hflip false false false false false false false false false false false true (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).2.1,
          (hbits false false false false false true rfl rfl rfl).2.1] at heq
      exact absurd heq (by decide)
  have ho2_gt : 7 < o2 := by
    apply Nat.lt_of_not_le
    intro hle
    rcases exists_support_le_five_of_le_n_add_one dag o2 hle with ⟨S, hSlen, hSdep⟩
    rcases exists_not_mem_of_length_lt S (by omega) with ⟨⟨iv, hiv⟩, hi⟩
    have hflip : ∀ (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool),
        (∀ j : Fin 6, j.val ≠ iv → vec6 a0 a1 a2 a3 a4 a5 j = vec6 b0 b1 b2 b3 b4 b5 j) →
        evalWire dag (vec6 a0 a1 a2 a3 a4 a5) o2 = evalWire dag (vec6 b0 b1 b2 b3 b4 b5) o2 :=
      fun _ _ _ _ _ _ _ _ _ _ _ _ h => hSdep _ _ (fun j hj => h j (fun heq => hi (by
        have hjeq : j = ⟨iv, hiv⟩ := Fin.ext heq
        exact hjeq ▸ hj)))
    match iv with
    | 0 =>
      have heq := hflip false false false true false false true false false true false false (by decide)
      rw [(hbits false false false true false false rfl rfl rfl).2.2,
          (hbits true false false true false false rfl rfl rfl).2.2] at heq
      exact absurd heq (by decide)
    | 1 =>
      have heq := hflip false false false false false false false true false false false false (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).2.2,
          (hbits false true false false false false rfl rfl rfl).2.2] at heq
      exact absurd heq (by decide)
    | 2 =>
      have heq := hflip false true false false false false false true true false false false (by decide)
      rw [(hbits false true false false false false rfl rfl rfl).2.2,
          (hbits false true true false false false rfl rfl rfl).2.2] at heq
      exact absurd heq (by decide)
    | 3 =>
      have heq := hflip false false false false false false false false false true false false (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).2.2,
          (hbits false false false true false false rfl rfl rfl).2.2] at heq
      exact absurd heq (by decide)
    | 4 =>
      have heq := hflip false true false false false false false true false false true false (by decide)
      rw [(hbits false true false false false false rfl rfl rfl).2.2,
          (hbits false true false false true false rfl rfl rfl).2.2] at heq
      exact absurd heq (by decide)
    | 5 =>
      have heq := hflip false false false false false false false false false false false true (by decide)
      rw [(hbits false false false false false false rfl rfl rfl).2.2,
          (hbits false false false false false true rfl rfl rfl).2.2] at heq
      exact absurd heq (by decide)
  have ho0_lt : o0 < 6 + dag.length := by
    apply Nat.lt_of_not_le
    intro hge
    have h := evalWire_ge_len dag (vec6 true false false false false false) o0 hge
    rw [(hbits true false false false false false rfl rfl rfl).1] at h
    exact absurd h (by decide)
  have ho1_lt : o1 < 6 + dag.length := by
    apply Nat.lt_of_not_le
    intro hge
    have h := evalWire_ge_len dag (vec6 false true false false false false) o1 hge
    rw [(hbits false true false false false false rfl rfl rfl).2.1] at h
    exact absurd h (by decide)
  have ho2_lt : o2 < 6 + dag.length := by
    apply Nat.lt_of_not_le
    intro hge
    have h := evalWire_ge_len dag (vec6 false true false false false false) o2 hge
    rw [(hbits false true false false false false rfl rfl rfl).2.2] at h
    exact absurd h (by decide)
  have h01 : o0 ≠ o1 := by
    intro heq
    have hA := hbits true false false false false false rfl rfl rfl
    have h1 := hA.1; have h2 := hA.2.1
    rw [heq] at h1; rw [h1] at h2; exact absurd h2 (by decide)
  have h02 : o0 ≠ o2 := by
    intro heq
    have hA := hbits true false false false false false rfl rfl rfl
    have h1 := hA.1; have h2 := hA.2.2
    rw [heq] at h1; rw [h1] at h2; exact absurd h2 (by decide)
  have h12 : o1 ≠ o2 := by
    intro heq
    have hA := hbits true false true false false false rfl rfl rfl
    have h1 := hA.2.1; have h2 := hA.2.2
    rw [heq] at h1; rw [h1] at h2; exact absurd h2 (by decide)
  omega

/-- Headline Theorem 2: Exact 7-`LOP3` depth-3 `K=3` balanced-ternary counter + `≥ 5` general-DAG lower bound. -/
theorem ternary_k3_7_lop3_exact :
    (∀ p0 n0 p1 n1 p2 n2 : Bool,
      tritValid p0 n0 = true → tritValid p1 n1 = true → tritValid p2 n2 = true →
      let (s0, s1, s2) := ternaryK3Lop3 p0 n0 p1 n1 p2 n2
      twosComp3 s0 s1 s2 = tritVal p0 n0 + tritVal p1 n1 + tritVal p2 n2) ∧
    (ternaryK3Dag.length = 7 ∧
      ∀ x : Fin 6 → Bool, validK3 x →
        twosComp3 (evalWire ternaryK3Dag x 8) (evalWire ternaryK3Dag x 11) (evalWire ternaryK3Dag x 12) =
          tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
          tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) +
          tritVal (x ⟨4, by decide⟩) (x ⟨5, by decide⟩)) ∧
    (∀ (dag : Lop3Dag) (o0 o1 o2 : Nat),
      (∀ x : Fin 6 → Bool, validK3 x →
        twosComp3 (evalWire dag x o0) (evalWire dag x o1) (evalWire dag x o2) =
          tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
          tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) +
          tritVal (x ⟨4, by decide⟩) (x ⟨5, by decide⟩)) →
      5 ≤ dag.length) :=
  ⟨ternaryK3Lop3_exact, ternaryK3Dag_exact, ternaryK3_dag_ge_5⟩

/-! ## 4. Theorem 3: Exact 8-`LOP3` `N=7` Harley–Seal 7→3 Compressor & Lower Bound -/

theorem harleySealN7Lop3_exact :
    ∀ x0 x1 x2 x3 x4 x5 x6 : Bool,
      let (s0, s1, s2) := harleySealN7Lop3 x0 x1 x2 x3 x4 x5 x6
      u3Val s0 s1 s2 = popcount7 x0 x1 x2 x3 x4 x5 x6 := by
  decide

theorem harleySealN7Dag_exact :
    harleySealN7Dag.length = 8 ∧
    ∀ x : Fin 7 → Bool,
      u3Val (evalWire harleySealN7Dag x 11) (evalWire harleySealN7Dag x 13) (evalWire harleySealN7Dag x 14) =
        popcount7Vec x := by
  refine ⟨rfl, ?_⟩
  intro x
  have hEq :
      (evalWire harleySealN7Dag x 11, evalWire harleySealN7Dag x 13, evalWire harleySealN7Dag x 14) =
      harleySealN7Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩)
        (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) (x ⟨6, by decide⟩) := by
    rfl
  have h11 : evalWire harleySealN7Dag x 11 = (harleySealN7Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) (x ⟨6, by decide⟩)).1 :=
    congrArg Prod.fst hEq
  have h13 : evalWire harleySealN7Dag x 13 = (harleySealN7Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) (x ⟨6, by decide⟩)).2.1 :=
    congrArg (fun p => p.2.1) hEq
  have h14 : evalWire harleySealN7Dag x 14 = (harleySealN7Lop3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) (x ⟨6, by decide⟩)).2.2 :=
    congrArg (fun p => p.2.2) hEq
  rw [h11, h13, h14]
  exact harleySealN7Lop3_exact _ _ _ _ _ _ _

def oneHot7 (i : Fin 7) : Fin 7 → Bool := fun j => j == i

def twoHot7 (i j : Fin 7) : Fin 7 → Bool := fun k => (k == i) || (k == j)

def fourHot7 (i : Fin 7) : Fin 7 → Bool :=
  fun k =>
    if k = i then true
    else
      let r := if k.val < i.val then k.val else k.val - 1
      decide (r < 3)

theorem popcount7Vec_zero : popcount7Vec (fun _ => false) = 0 := by decide

theorem popcount7Vec_oneHot7 : ∀ i : Fin 7, popcount7Vec (oneHot7 i) = 1 := by decide

theorem popcount7Vec_twoHot7 : ∀ i j : Fin 7, i ≠ j → popcount7Vec (twoHot7 i j) = 2 := by decide

theorem popcount7Vec_fourHot7 : ∀ i : Fin 7, popcount7Vec (fourHot7 i) = 4 := by decide

theorem popcount7Vec_fourHot7_clear : ∀ i : Fin 7,
    popcount7Vec (setCoord (fourHot7 i) i false) = 3 := by decide

theorem nextMod7_ne : ∀ i : Fin 7, i ≠ ⟨(i.val + 1) % 7, Nat.mod_lt _ (by decide)⟩ := by decide

theorem u3Val_eq_bits (s0 s1 s2 : Bool) (k : Nat) (hk : u3Val s0 s1 s2 = k) :
    s0 = (k % 2 == 1) ∧ s1 = ((k / 2) % 2 == 1) ∧ s2 = decide (k ≥ 4) := by
  subst hk
  cases s0 <;> cases s1 <;> cases s2 <;> decide

/-- Every output bit of a 7→3 compressor depends on all 7 inputs, forcing `dag.length ≥ 5`. -/
theorem harleySealN7_dag_ge_5 (dag : Lop3Dag) (o0 o1 o2 : Nat)
    (hspec : ∀ x : Fin 7 → Bool,
      u3Val (evalWire dag x o0) (evalWire dag x o1) (evalWire dag x o2) = popcount7Vec x) :
    5 ≤ dag.length := by
  have hbits : ∀ x : Fin 7 → Bool,
      evalWire dag x o0 = (popcount7Vec x % 2 == 1) ∧
      evalWire dag x o1 = ((popcount7Vec x / 2) % 2 == 1) ∧
      evalWire dag x o2 = decide (popcount7Vec x ≥ 4) :=
    fun x => u3Val_eq_bits _ _ _ _ (hspec x)
  have ho0_gt : 8 < o0 := by
    apply Nat.lt_of_not_le
    intro hle
    rcases exists_support_le_five_of_le_n_add_one dag o0 hle with ⟨S, hSlen, hSdep⟩
    rcases exists_not_mem_of_length_lt S (by omega) with ⟨i, hi⟩
    have heq : evalWire dag (fun _ => false) o0 = evalWire dag (oneHot7 i) o0 :=
      hSdep _ _ (fun j hj => by
        have hne : j ≠ i := fun h => hi (h ▸ hj)
        simp [oneHot7, hne])
    rw [(hbits _).1, (hbits _).1, popcount7Vec_zero, popcount7Vec_oneHot7] at heq
    exact absurd heq (by decide)
  have ho1_gt : 8 < o1 := by
    apply Nat.lt_of_not_le
    intro hle
    rcases exists_support_le_five_of_le_n_add_one dag o1 hle with ⟨S, hSlen, hSdep⟩
    rcases exists_not_mem_of_length_lt S (by omega) with ⟨i, hi⟩
    let j : Fin 7 := ⟨(i.val + 1) % 7, Nat.mod_lt _ (by decide)⟩
    have hne : i ≠ j := nextMod7_ne i
    have heq : evalWire dag (oneHot7 j) o1 = evalWire dag (twoHot7 i j) o1 :=
      hSdep _ _ (fun k hk => by
        have hki : k ≠ i := fun h => hi (h ▸ hk)
        simp [oneHot7, twoHot7, hki])
    rw [(hbits _).2.1, (hbits _).2.1, popcount7Vec_oneHot7, popcount7Vec_twoHot7 i j hne] at heq
    exact absurd heq (by decide)
  have ho2_gt : 8 < o2 := by
    apply Nat.lt_of_not_le
    intro hle
    rcases exists_support_le_five_of_le_n_add_one dag o2 hle with ⟨S, hSlen, hSdep⟩
    rcases exists_not_mem_of_length_lt S (by omega) with ⟨i, hi⟩
    have heq : evalWire dag (setCoord (fourHot7 i) i false) o2 = evalWire dag (fourHot7 i) o2 :=
      hSdep _ _ (setCoord_eq_outside (fourHot7 i) i false S hi)
    rw [(hbits _).2.2, (hbits _).2.2, popcount7Vec_fourHot7_clear, popcount7Vec_fourHot7] at heq
    exact absurd heq (by decide)
  have ho0_lt : o0 < 7 + dag.length := by
    apply Nat.lt_of_not_le
    intro hge
    have h := evalWire_ge_len dag (oneHot7 ⟨0, by decide⟩) o0 hge
    rw [(hbits _).1, popcount7Vec_oneHot7] at h
    exact absurd h (by decide)
  have ho1_lt : o1 < 7 + dag.length := by
    apply Nat.lt_of_not_le
    intro hge
    have h := evalWire_ge_len dag (twoHot7 ⟨0, by decide⟩ ⟨1, by decide⟩) o1 hge
    rw [(hbits _).2.1, popcount7Vec_twoHot7 _ _ (by decide)] at h
    exact absurd h (by decide)
  have ho2_lt : o2 < 7 + dag.length := by
    apply Nat.lt_of_not_le
    intro hge
    have h := evalWire_ge_len dag (fourHot7 ⟨0, by decide⟩) o2 hge
    rw [(hbits _).2.2, popcount7Vec_fourHot7] at h
    exact absurd h (by decide)
  have h01 : o0 ≠ o1 := by
    intro heq
    have hA := hbits (oneHot7 ⟨0, by decide⟩)
    have h1 := hA.1; have h2 := hA.2.1
    rw [heq] at h1; rw [h1, popcount7Vec_oneHot7] at h2; exact absurd h2 (by decide)
  have h02 : o0 ≠ o2 := by
    intro heq
    have hA := hbits (oneHot7 ⟨0, by decide⟩)
    have h1 := hA.1; have h2 := hA.2.2
    rw [heq] at h1; rw [h1, popcount7Vec_oneHot7] at h2; exact absurd h2 (by decide)
  have h12 : o1 ≠ o2 := by
    intro heq
    have hA := hbits (twoHot7 ⟨0, by decide⟩ ⟨1, by decide⟩)
    have h1 := hA.2.1; have h2 := hA.2.2
    rw [heq] at h1; rw [h1, popcount7Vec_twoHot7 _ _ (by decide)] at h2; exact absurd h2 (by decide)
  omega

/-- Headline Theorem 3: Exact 8-`LOP3` depth-3 `N=7` Harley–Seal 7→3 compressor + `≥ 5` general-DAG lower bound. -/
theorem harley_seal_n7_8_lop3_exact_and_lb :
    (∀ x0 x1 x2 x3 x4 x5 x6 : Bool,
      let (s0, s1, s2) := harleySealN7Lop3 x0 x1 x2 x3 x4 x5 x6
      u3Val s0 s1 s2 = popcount7 x0 x1 x2 x3 x4 x5 x6) ∧
    (harleySealN7Dag.length = 8 ∧
      ∀ x : Fin 7 → Bool,
        u3Val (evalWire harleySealN7Dag x 11) (evalWire harleySealN7Dag x 13) (evalWire harleySealN7Dag x 14) =
          popcount7Vec x) ∧
    (∀ (dag : Lop3Dag) (o0 o1 o2 : Nat),
      (∀ x : Fin 7 → Bool,
        u3Val (evalWire dag x o0) (evalWire dag x o1) (evalWire dag x o2) = popcount7Vec x) →
      5 ≤ dag.length) :=
  ⟨harleySealN7Lop3_exact, harleySealN7Dag_exact, harleySealN7_dag_ge_5⟩

end TernaryLop3Kulisch
