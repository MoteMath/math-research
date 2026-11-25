import Std

/-!
# Core Combinatorial Definitions for `gpu-comb-mining-20261117`

Pure `Std`/`Init` definitions and counting lemmas for:
  1. Finite simple graphs (`SimpleGraphFin n`), degrees, Albertson irregularity,
     ordered induced `P_3` wedges, triangle-freeness, `C_4`-freeness, connectedness,
     matchings, and dominating sets.
  2. Finite Sidon subsets on `Nat`, symmetric difference defect, runs, isolated elements,
     and modular sumset cardinality.
  3. Permutations (`PermFin n`), descents, strictly increasing/decreasing subsequences,
     `321`- and `231`-avoidance, weak excedances, left-to-right maxima, inversions,
     and Spearman displacement (`2 * disp`).
-/

namespace CombMining

-- ============================================================================
-- General List / Nat Helpers
-- ============================================================================

def sumNat {α : Type} (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => f x + sumNat rest f

def natAbsDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

theorem natAbsDiff_symm (a b : Nat) : natAbsDiff a b = natAbsDiff b a := by
  unfold natAbsDiff
  split <;> split <;> omega

theorem natAbsDiff_add_cancel (a b c : Nat) :
    natAbsDiff (c + a) (c + b) = natAbsDiff a b := by
  unfold natAbsDiff
  split <;> split <;> omega

theorem natAbsDiff_le_add (a b : Nat) : natAbsDiff a b ≤ a + b := by
  unfold natAbsDiff
  split <;> omega

theorem sumNat_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : sumNat xs f ≤ sumNat xs g := by
  induction xs with
  | nil => simp [sumNat]
  | cons x rest ih =>
    simp only [sumNat]
    have hx : f x ≤ g x := h x (by simp)
    have hr : sumNat rest f ≤ sumNat rest g := ih (fun y hy => h y (by simp [hy]))
    omega

theorem sumNat_add {α : Type} (xs : List α) (f g : α → Nat) :
    sumNat xs (fun x => f x + g x) = sumNat xs f + sumNat xs g := by
  induction xs with
  | nil => simp [sumNat]
  | cons x rest ih =>
    simp only [sumNat, ih]
    omega

theorem sumNat_congr {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x = g x) : sumNat xs f = sumNat xs g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [sumNat]
    have hx := h x (by simp)
    have hr := ih (fun y hy => h y (by simp [hy]))
    omega

theorem sumNat_const_mul {α : Type} (c : Nat) (xs : List α) (f : α → Nat) :
    c * sumNat xs f = sumNat xs (fun x => c * f x) := by
  induction xs with
  | nil => simp [sumNat]
  | cons x rest ih =>
    simp only [sumNat]
    rw [Nat.mul_add, ih]

theorem sumNat_append {α : Type} (xs ys : List α) (f : α → Nat) :
    sumNat (xs ++ ys) f = sumNat xs f + sumNat ys f := by
  induction xs with
  | nil => simp [sumNat]
  | cons x rest ih =>
    simp only [List.cons_append, sumNat, ih]
    omega

theorem sumNat_map {α β : Type} (xs : List α) (g : α → β) (f : β → Nat) :
    sumNat (xs.map g) f = sumNat xs (fun x => f (g x)) := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [sumNat, ih]

theorem sumNat_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumNat xs (fun x => sumNat ys (fun y => f x y)) =
    sumNat ys (fun y => sumNat xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    simp only [sumNat]
    induction ys with
    | nil => rfl
    | cons y rest ihy => simp only [sumNat, ← ihy]
  | cons x rest ihx =>
    simp only [sumNat, ihx]
    symm
    exact sumNat_add ys (fun y => f x y) (fun y => sumNat rest (fun r => f r y))

theorem countP_eq_sumNat {α : Type} (xs : List α) (P : α → Bool) :
    xs.countP P = sumNat xs (fun x => if P x then 1 else 0) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.countP_cons, sumNat, ih]
    cases P x <;> simp <;> omega

private theorem sumNat_eq_zero_of_not_mem {α : Type} [DecidableEq α]
    (xs : List α) (v : α) (hnot : v ∉ xs) :
    sumNat xs (fun y => if y = v then 1 else 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    simp only [sumNat]
    have hrv : r ≠ v := fun h => hnot (by simp [h])
    have hrs := ih (fun hm => hnot (by simp [hm]))
    simp [hrv, hrs]

theorem sumNat_eq_indicator_one {α : Type} [DecidableEq α]
    (xs : List α) (hnodup : xs.Nodup) (v : α) (hv : v ∈ xs) :
    sumNat xs (fun x => if x = v then 1 else 0) = 1 := by
  induction xs with
  | nil => simp at hv
  | cons x rest ih =>
    simp only [sumNat]
    rw [List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hv with hxv | hrv
    · subst hxv
      have hzero := sumNat_eq_zero_of_not_mem rest v hnodup.1
      simp [hzero]
    · have hxv : x ≠ v := fun h => hnodup.1 (h ▸ hrv)
      have hr := ih hnodup.2 hrv
      simp [hxv, hr]

private theorem countP_erase_of_mem {β : Type} [DecidableEq β]
    (ys : List β) (a : β) (Q : β → Bool) (hny : ys.Nodup) (hmem : a ∈ ys) (hq : Q a = true) :
    ys.countP Q = (ys.erase a).countP Q + 1 := by
  induction ys with
  | nil => simp at hmem
  | cons y yr ih =>
    rw [List.nodup_cons] at hny
    by_cases hy : y = a
    · subst hy
      simp [List.erase_cons_head, hq]
    · have hmemr : a ∈ yr := (List.mem_cons.mp hmem).resolve_left (Ne.symm hy)
      have hrec := ih hny.2 hmemr
      have hbeq : (y == a) = false := beq_false_of_ne hy
      have h_er : (y :: yr).erase a = y :: yr.erase a := by
        simp [hbeq]
      rw [h_er, List.countP_cons, List.countP_cons]
      cases Q y <;> simp <;> omega

theorem countP_map_le {α β : Type} [DecidableEq β] (f : α → β)
    (hinj : ∀ a b, f a = f b → a = b)
    (xs : List α) (ys : List β) (hnx : xs.Nodup) (hny : ys.Nodup)
    (P : α → Bool) (Q : β → Bool)
    (hmap : ∀ x ∈ xs, P x = true → f x ∈ ys ∧ Q (f x) = true) :
    xs.countP P ≤ ys.countP Q := by
  induction xs generalizing ys with
  | nil => simp
  | cons x rest ih =>
    rw [List.nodup_cons] at hnx
    rcases hnx with ⟨hxnot, hnr⟩
    simp only [List.countP_cons]
    cases hpx : P x
    · simp
      exact ih ys hnr hny (fun z hz hpz => hmap z (by simp [hz]) hpz)
    · simp
      have hfx := hmap x (by simp) hpx
      have hmem : f x ∈ ys := hfx.1
      have hqx : Q (f x) = true := hfx.2
      let ys' := ys.erase (f x)
      have hny' : ys'.Nodup := List.Nodup.erase (f x) hny
      have hsub : rest.countP P ≤ ys'.countP Q := by
        apply ih ys' hnr hny'
        intro z hz hpz
        have hfz := hmap z (by simp [hz]) hpz
        have hne : f z ≠ f x := by
          intro heq
          have hzx : z = x := hinj z x heq
          subst hzx
          exact hxnot hz
        exact ⟨(List.mem_erase_of_ne hne).mpr hfz.1, hfz.2⟩
      have hy_cnt := countP_erase_of_mem ys (f x) Q hny hmem hqx
      dsimp [ys'] at hsub
      omega

theorem finRange_map_val (n : Nat) :
    (List.finRange n).map Fin.val = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last, List.map_append, List.map_map]
    simp only [Function.comp_def, Fin.val_castSucc, Fin.val_last, List.map_singleton]
    rw [ih, List.range_succ]

theorem countP_range_lt (n k : Nat) :
    (List.range n).countP (fun x => decide (x < k)) = min k n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil]
    by_cases h : n < k <;> simp [h] <;> omega

theorem countP_finRange_lt (n k : Nat) :
    (List.finRange n).countP (fun x => decide (x.val < k)) = min k n := by
  have h1 : (List.finRange n).countP (fun x => decide (x.val < k)) =
      ((List.finRange n).map Fin.val).countP (fun x => decide (x < k)) := by
    rw [List.countP_map]
    rfl
  rw [h1, finRange_map_val, countP_range_lt]

-- ============================================================================
-- 1. Finite Simple Graphs
-- ============================================================================

structure SimpleGraphFin (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

namespace SimpleGraphFin

def deg {n : Nat} (G : SimpleGraphFin n) (u : Fin n) : Nat :=
  (List.finRange n).countP (fun v => G.adj u v)

def edgeCount {n : Nat} (G : SimpleGraphFin n) : Nat :=
  sumNat (List.finRange n) (fun u =>
    (List.finRange n).countP (fun v => decide (u.val < v.val) && G.adj u v))

def minDeg {n : Nat} (G : SimpleGraphFin n) : Nat :=
  match List.finRange n with
  | [] => 0
  | v :: vs => vs.foldl (fun acc w => min acc (G.deg w)) (G.deg v)

def albertson {n : Nat} (G : SimpleGraphFin n) : Nat :=
  sumNat (List.finRange n) (fun u =>
    sumNat (List.finRange n) (fun v =>
      if u.val < v.val ∧ G.adj u v = true then natAbsDiff (G.deg u) (G.deg v) else 0))

def orderedIndP3 {n : Nat} (G : SimpleGraphFin n) : Nat :=
  sumNat (List.finRange n) (fun u =>
    sumNat (List.finRange n) (fun v =>
      sumNat (List.finRange n) (fun w =>
        if G.adj u v = true ∧ G.adj u w = true ∧ G.adj v w = false ∧ w ≠ v then 1 else 0)))

def TriangleFree {n : Nat} (G : SimpleGraphFin n) : Prop :=
  ∀ u v w : Fin n, !(G.adj u v = true ∧ G.adj v w = true ∧ G.adj u w = true)

def C4Free {n : Nat} (G : SimpleGraphFin n) : Prop :=
  ∀ a b c d : Fin n,
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    !(G.adj a b = true ∧ G.adj b c = true ∧ G.adj c d = true ∧ G.adj d a = true)

def IsWalk {n : Nat} (G : SimpleGraphFin n) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => G.adj u v = true ∧ IsWalk G (v :: rest)

def Connected {n : Nat} (G : SimpleGraphFin n) : Prop :=
  ∀ s t : Fin n, ∃ walk : List (Fin n),
    walk ≠ [] ∧ walk.head? = some s ∧ walk.getLast? = some t ∧ G.IsWalk walk

def IsMatching {n : Nat} (G : SimpleGraphFin n) (M : List (Fin n × Fin n)) : Prop :=
  (∀ e ∈ M, e.1.val < e.2.val ∧ G.adj e.1 e.2 = true) ∧
  (M.flatMap (fun e => [e.1, e.2])).Nodup

def MatchingNum {n : Nat} (G : SimpleGraphFin n) (k : Nat) : Prop :=
  (∃ M, G.IsMatching M ∧ M.length = k) ∧
  (∀ M, G.IsMatching M → M.length ≤ k)

def IsDominatingSet {n : Nat} (G : SimpleGraphFin n) (D : List (Fin n)) : Prop :=
  D.Nodup ∧ ∀ v : Fin n, v ∈ D ∨ ∃ u ∈ D, G.adj u v = true

def DominationNum {n : Nat} (G : SimpleGraphFin n) (k : Nat) : Prop :=
  (∃ D, G.IsDominatingSet D ∧ D.length = k) ∧
  (∀ D, G.IsDominatingSet D → k ≤ D.length)

def commonDeg {n : Nat} (G : SimpleGraphFin n) (u v : Fin n) : Nat :=
  (List.finRange n).countP (fun w => G.adj u w && G.adj v w)

def trA4 {n : Nat} (G : SimpleGraphFin n) : Nat :=
  sumNat (List.finRange n) (fun u =>
    sumNat (List.finRange n) (fun v =>
      let c := G.commonDeg u v
      c * c))

def zagreb2 {n : Nat} (G : SimpleGraphFin n) : Nat :=
  sumNat (List.finRange n) (fun u =>
    sumNat (List.finRange n) (fun v =>
      if u.val < v.val ∧ G.adj u v = true then G.deg u * G.deg v else 0))

def indC4Cnt {n : Nat} (G : SimpleGraphFin n) : Nat :=
  sumNat (List.finRange n) (fun u =>
    sumNat (List.finRange n) (fun v =>
      if decide (u.val < v.val) && !(G.adj u v) then
        sumNat (List.finRange n) (fun a =>
          if G.adj u a && G.adj v a then
            (List.finRange n).countP (fun b =>
              decide (a.val < b.val) && G.adj u b && G.adj v b && !(G.adj a b))
          else 0)
      else 0)) / 2

def clawCnt {n : Nat} (G : SimpleGraphFin n) : Nat :=
  sumNat (List.finRange n) (fun u =>
    sumNat (List.finRange n) (fun a =>
      if G.adj u a then
        sumNat (List.finRange n) (fun b =>
          if decide (a.val < b.val) && G.adj u b && !(G.adj a b) then
            (List.finRange n).countP (fun c =>
              decide (b.val < c.val) && G.adj u c && !(G.adj a c) && !(G.adj b c))
          else 0)
      else 0))

def indP4Cnt {n : Nat} (G : SimpleGraphFin n) : Nat :=
  sumNat (List.finRange n) (fun u =>
    sumNat (List.finRange n) (fun v =>
      if decide (u.val < v.val) && G.adj u v then
        sumNat (List.finRange n) (fun a =>
          if G.adj u a && !(G.adj v a) && decide (a ≠ v) then
            (List.finRange n).countP (fun b =>
              G.adj v b && !(G.adj u b) && decide (b ≠ u) && !(G.adj a b))
          else 0)
      else 0))

def IsTree {n : Nat} (G : SimpleGraphFin n) : Prop :=
  G.Connected ∧ G.edgeCount + 1 = n

def IsIndepSet {n : Nat} (G : SimpleGraphFin n) (S : List (Fin n)) : Prop :=
  S.Nodup ∧ ∀ u ∈ S, ∀ v ∈ S, G.adj u v = false

def IsIndepDomSet {n : Nat} (G : SimpleGraphFin n) (S : List (Fin n)) : Prop :=
  G.IsIndepSet S ∧ G.IsDominatingSet S

def IndepDominationNum {n : Nat} (G : SimpleGraphFin n) (k : Nat) : Prop :=
  (∃ S, G.IsIndepDomSet S ∧ S.length = k) ∧
  (∀ S, G.IsIndepDomSet S → k ≤ S.length)

def Bipartite {n : Nat} (G : SimpleGraphFin n) : Prop :=
  ∃ col : Fin n → Bool, ∀ u v : Fin n, G.adj u v = true → col u != col v

def IsInducedMatching {n : Nat} (G : SimpleGraphFin n) (M : List (Fin n × Fin n)) : Prop :=
  G.IsMatching M ∧
  ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 →
    G.adj e1.1 e2.1 = false ∧ G.adj e1.1 e2.2 = false ∧
    G.adj e1.2 e2.1 = false ∧ G.adj e1.2 e2.2 = false

def InducedMatchingNum {n : Nat} (G : SimpleGraphFin n) (k : Nat) : Prop :=
  (∃ M, G.IsInducedMatching M ∧ M.length = k) ∧
  (∀ M, G.IsInducedMatching M → M.length ≤ k)

def WithinDist {n : Nat} (G : SimpleGraphFin n) (s t : Fin n) (d : Nat) : Prop :=
  ∃ walk : List (Fin n),
    walk ≠ [] ∧ walk.head? = some s ∧ walk.getLast? = some t ∧
    G.IsWalk walk ∧ walk.length ≤ d + 1

def DiameterNum {n : Nat} (G : SimpleGraphFin n) (d : Nat) : Prop :=
  (∀ s t : Fin n, G.WithinDist s t d) ∧
  (∀ d' : Nat, (∀ s t : Fin n, G.WithinDist s t d') → d ≤ d')

def maxDeg {n : Nat} (G : SimpleGraphFin n) : Nat :=
  (List.finRange n).foldl (fun acc w => max acc (G.deg w)) 0

def IndependenceNum {n : Nat} (G : SimpleGraphFin n) (k : Nat) : Prop :=
  (∃ S, G.IsIndepSet S ∧ S.length = k) ∧
  (∀ S, G.IsIndepSet S → S.length ≤ k)

def IsClique {n : Nat} (G : SimpleGraphFin n) (K : List (Fin n)) : Prop :=
  K.Nodup ∧ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.adj u v = true

def CliqueNum {n : Nat} (G : SimpleGraphFin n) (k : Nat) : Prop :=
  (∃ K, G.IsClique K ∧ K.length = k) ∧
  (∀ K, G.IsClique K → K.length ≤ k)

end SimpleGraphFin

-- ============================================================================
-- 2. Finite Additive Subsets and Sidon Sets
-- ============================================================================

def IsSidonPred (A : Nat → Bool) : Prop :=
  ∀ a b c d : Nat, A a = true → A b = true → A c = true → A d = true →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def cardInterval (A : Nat → Bool) (mn mx : Nat) : Nat :=
  sumNat (List.range (mx - mn + 1)) (fun k => if A (mn + k) then 1 else 0)

def symDefectInterval (A : Nat → Bool) (mn mx : Nat) : Nat :=
  sumNat (List.range (mx - mn + 1)) (fun k =>
    if A (mn + k) != A (mx - k) then 1 else 0)

def cardPrefix (A : Nat → Bool) (N : Nat) : Nat :=
  sumNat (List.range N) (fun x => if A x then 1 else 0)

def isRunStart (A : Nat → Bool) (x : Nat) : Bool :=
  A x && (if x = 0 then true else !(A (x - 1)))

def isRunEnd (A : Nat → Bool) (x : Nat) : Bool :=
  A x && !(A (x + 1))

def isIsolated (A : Nat → Bool) (x : Nat) : Bool :=
  isRunStart A x && !(A (x + 1))

def runsPrefix (A : Nat → Bool) (N : Nat) : Nat :=
  sumNat (List.range N) (fun x => if isRunStart A x then 1 else 0)

def isolatedPrefix (A : Nat → Bool) (N : Nat) : Nat :=
  sumNat (List.range N) (fun x => if isIsolated A x then 1 else 0)

def modSumsetCard (N : Nat) (A : Fin N → Bool) : Nat :=
  (List.finRange N).countP (fun s =>
    (List.finRange N).any (fun a =>
      (List.finRange N).any (fun b =>
        A a && A b && decide ((a.val + b.val) % N = s.val))))

def symDefectFin (N : Nat) (A : Fin N → Bool) : Nat :=
  (List.finRange N).countP (fun x =>
    A x != A ⟨N - 1 - x.val, by omega⟩)

def intSumsetCard (A : Nat → Bool) (N : Nat) : Nat :=
  (List.range (2 * N)).countP (fun s =>
    (List.range N).any (fun a =>
      (List.range N).any (fun b =>
        A a && A b && decide (a + b = s))))

def intRestSumCard (A : Nat → Bool) (N : Nat) : Nat :=
  (List.range (2 * N)).countP (fun s =>
    (List.range N).any (fun a =>
      (List.range N).any (fun b =>
        A a && A b && decide (a < b) && decide (a + b = s))))

def intDilateSum2Card (A : Nat → Bool) (N : Nat) : Nat :=
  (List.range (3 * N)).countP (fun s =>
    (List.range N).any (fun a =>
      (List.range N).any (fun b =>
        A a && A b && decide (a + 2 * b = s))))

def IsAP3FreePrefix (A : Nat → Bool) (N : Nat) : Prop :=
  ∀ a b c : Nat, a < N → b < N → c < N →
    A a = true → A b = true → A c = true → a < b → a + b ≠ 2 * c

def intDilateSum3Card (A : Nat → Bool) (N : Nat) : Nat :=
  (List.range (4 * N)).countP (fun s =>
    (List.range N).any (fun a =>
      (List.range N).any (fun b =>
        A a && A b && decide (a + 3 * b = s))))

def symDefectPrefix (A : Nat → Bool) (N : Nat) : Nat :=
  sumNat (List.range N) (fun x =>
    if A x != A (N - 1 - x) then 1 else 0)

def intDiffsetCard (A : Nat → Bool) (N : Nat) : Nat :=
  (List.range (2 * N)).countP (fun s =>
    (List.range N).any (fun a =>
      (List.range N).any (fun b =>
        A a && A b && decide (a + (N - 1) = s + b))))

def intSum3Card (A : Nat → Bool) (N : Nat) : Nat :=
  (List.range (3 * N)).countP (fun s =>
    (List.range N).any (fun a =>
      (List.range N).any (fun b =>
        (List.range N).any (fun c =>
          A a && A b && A c && decide (a + b + c = s)))))

def intDilateDiff2Card (A : Nat → Bool) (N : Nat) : Nat :=
  (List.range (3 * N)).countP (fun s =>
    (List.range N).any (fun a =>
      (List.range N).any (fun b =>
        A a && A b && decide (a + 2 * (N - 1 - b) = s))))

def intSum2Diff1Card (A : Nat → Bool) (N : Nat) : Nat :=
  (List.range (3 * N)).countP (fun s =>
    (List.range N).any (fun a =>
      (List.range N).any (fun b =>
        (List.range N).any (fun c =>
          A a && A b && A c && decide (a + b + (N - 1) = s + c)))))

-- ============================================================================
-- 3. Permutations and Permutation Statistics
-- ============================================================================

structure PermFin (n : Nat) where
  toFun : Fin n → Fin n
  invFun : Fin n → Fin n
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

namespace PermFin

theorem toFun_inj {n : Nat} (p : PermFin n) {a b : Fin n}
    (h : p.toFun a = p.toFun b) : a = b := by
  have := congrArg p.invFun h
  simpa [p.left_inv] using this

theorem invFun_inj {n : Nat} (p : PermFin n) {a b : Fin n}
    (h : p.invFun a = p.invFun b) : a = b := by
  have := congrArg p.toFun h
  simpa [p.right_inv] using this

def toList {n : Nat} (p : PermFin n) : List Nat :=
  (List.finRange n).map (fun i => (p.toFun i).val)

def IsWeakExcedance {n : Nat} (p : PermFin n) (i : Fin n) : Prop :=
  i.val ≤ (p.toFun i).val

def IsLeftToRightMax {n : Nat} (p : PermFin n) (i : Fin n) : Prop :=
  ∀ j : Fin n, j.val < i.val → (p.toFun j).val < (p.toFun i).val

def Avoids321 {n : Nat} (p : PermFin n) : Prop :=
  ∀ i j k : Fin n, i.val < j.val → j.val < k.val →
    ¬ ((p.toFun i).val > (p.toFun j).val ∧ (p.toFun j).val > (p.toFun k).val)

def Avoids231 {n : Nat} (p : PermFin n) : Prop :=
  ∀ i j k : Fin n, i.val < j.val → j.val < k.val →
    ¬ ((p.toFun k).val < (p.toFun i).val ∧ (p.toFun i).val < (p.toFun j).val)

def invCnt {n : Nat} (p : PermFin n) : Nat :=
  sumNat (List.finRange n) (fun i =>
    (List.finRange n).countP (fun j =>
      decide (i.val < j.val) && decide ((p.toFun j).val < (p.toFun i).val)))

def disp2 {n : Nat} (p : PermFin n) : Nat :=
  sumNat (List.finRange n) (fun i => natAbsDiff (p.toFun i).val i.val)

def excCnt {n : Nat} (p : PermFin n) : Nat :=
  (List.finRange n).countP (fun i => decide (i.val < (p.toFun i).val))

def StrictDecSubseq {n : Nat} (p : PermFin n) (sub : List Nat) : Prop :=
  sub.Sublist p.toList ∧ sub.Pairwise (· > ·)

def StrictIncSubseq (sub xs : List Nat) : Prop :=
  sub.Sublist xs ∧ sub.Pairwise (· < ·)

end PermFin

def desList : List Nat → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: rest => (if x > y then 1 else 0) + desList (y :: rest)

def westStep : List Nat → Nat → List Nat × List Nat
  | [], x => ([], [x])
  | top :: rest, x =>
    if top < x then
      let res := westStep rest x
      (top :: res.1, res.2)
    else
      ([], x :: top :: rest)

def westSortAux : List Nat → List Nat → List Nat
  | [], stk => stk
  | x :: xs, stk =>
    let res := westStep stk x
    res.1 ++ westSortAux xs res.2

def westSortList (xs : List Nat) : List Nat :=
  westSortAux xs []

def listInvCnt : List Nat → Nat
  | [] => 0
  | a :: xs => xs.countP (fun b => decide (b < a)) + listInvCnt xs

def pairs31 : List Nat → Nat → Nat
  | [], _ => 0
  | b :: rest, s =>
    (if s < b then rest.countP (fun c => decide (c < s)) else 0) + pairs31 rest s

def pat231List : List Nat → Nat
  | [] => 0
  | a :: rest => pairs31 rest a + pat231List rest

def popRuns : List Nat → List (List Nat)
  | [] => []
  | x :: rest =>
    match popRuns rest with
    | [] => [[x]]
    | (y :: ys) :: runs =>
      if y < x then (x :: y :: ys) :: runs
      else [x] :: (y :: ys) :: runs
    | [] :: runs => [x] :: runs

def popSortList (xs : List Nat) : List Nat :=
  (popRuns xs).flatMap List.reverse

namespace PermFin

def pat231 {n : Nat} (p : PermFin n) : Nat :=
  pat231List p.toList

def stackInv {n : Nat} (p : PermFin n) : Nat :=
  listInvCnt (westSortList p.toList)

def stack2Inv {n : Nat} (p : PermFin n) : Nat :=
  listInvCnt (westSortList (westSortList p.toList))

def stackDes {n : Nat} (p : PermFin n) : Nat :=
  desList (westSortList p.toList)

def popInv {n : Nat} (p : PermFin n) : Nat :=
  listInvCnt (popSortList p.toList)

def popDes {n : Nat} (p : PermFin n) : Nat :=
  desList (popSortList p.toList)

def iterPerm {n : Nat} (p : PermFin n) : Nat → Fin n → Fin n
  | 0, x => x
  | k + 1, x => p.toFun (iterPerm p k x)

def isCycleMin {n : Nat} (p : PermFin n) (i : Fin n) : Bool :=
  (List.range n).all (fun k => decide (i.val ≤ (iterPerm p k i).val))

def cycCnt {n : Nat} (p : PermFin n) : Nat :=
  (List.finRange n).countP (isCycleMin p)

def IsInvolution {n : Nat} (p : PermFin n) : Prop :=
  ∀ i : Fin n, p.toFun (p.toFun i) = i

end PermFin

def listPeaksCnt : List Nat → Nat
  | a :: b :: c :: rest =>
    (if a < b ∧ c < b then 1 else 0) + listPeaksCnt (b :: c :: rest)
  | _ => 0

def PermFin.peaksCnt {n : Nat} (p : PermFin n) : Nat :=
  listPeaksCnt p.toList

end CombMining
