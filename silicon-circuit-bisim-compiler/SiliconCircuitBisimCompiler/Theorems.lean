/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SiliconCircuitBisimCompiler.Defs

/-!
# Theorems (`SiliconCircuitBisimCompiler`)

# SiliconBisim: Verified Lean 4 Bit-Slice & Recursive Circuit-Generator Bisimulation Compiler

Standalone Lean 4.36.0 (zero Mathlib, zero external imports).

A reusable, kernel-verified pure-silicon proof-reflection and certificate-compiler engine
where finite binary certificates (checked by `decide`) + proved general soundness meta-theorems
automatically discharge infinite universally quantified circuit-generator equivalences
(`∀ w : Nat` and `∀ k : Nat` at width `2^k`) across four hardware generator families:

  - **Engine 1 (`SliceBisimCompiler`)**: Arbitrary-width linear & multi-stride (2-bit block)
    bit-slice circuit generators with differing internal state encodings (Ripple-Carry,
    Dual-Rail Complementary Carry, 2-Bit Speculative Carry-Select, Gray Transducers).
  - **Engine 2 (`PrefixTreeCompiler`)**: Dyadic `2^k`-width parallel-prefix tree generators
    (`Serial`, `Sklansky`, `Brent–Kung`, `Kogge–Stone`) with reachable-subset associativity
    and monoid-action homomorphism certificates (handling cross-encoding equivalences and
    don't-care-glitched black cells that are NOT globally associative!).
  - **Engine 3 (`ShifterCompiler`)**: Arbitrary-width logarithmic mux barrel shifters and
    `2^k`-width recursive unshuffle-rotate-interleave tree shifters vs iterated 1-bit shifters.
  - **Engine 4 (`ButterflyBitonicCompiler`)**: `2^k`-width Butterfly networks (4-wire
    Interchange lifting, 2-wire Inverse cancellation, Pease/Omega constant-geometry
    equivalence) AND Batcher Bitonic Sort ≡ Batcher Odd-Even Mergesort ≡ Threshold Sort,
    lifted to arbitrary total orders via a kernel-checked Knuth 0–1 Principle.
-/


namespace SiliconBisim
theorem forallBv_sound {n : Nat} {P : BitVec n → Bool}
    (h : forallBv n P = true) : ∀ v : BitVec n, P v = true := by
  intro v
  unfold forallBv at h
  rw [List.all_eq_true] at h
  have hmem : v.toNat ∈ List.range (2 ^ n) := List.mem_range.mpr v.isLt
  have hv := h v.toNat hmem
  simpa [BitVec.ofNat_toNat] using hv

/-- **General Soundness Meta-Theorem (Engine 1A)**:
    A verified finite binary bisimulation certificate discharges arbitrary-width equivalence
    `∀ w : Nat, ∀ xs` of length `w` between two concrete gate-level bit-slice generators
    (even with completely different internal state widths and encodings). -/
theorem slice_bisim_sound (G1 G2 : SliceGen)
    (hIn : G1.inW = G2.inW) (hOut : G1.outW = G2.outW) (hFin : G1.finW = G2.finW)
    (cert : SliceBisimCert G1.stW G2.stW)
    (hCert : checkSliceBisim G1 G2 hIn hOut hFin cert = true) :
    ∀ (xs : List (BitVec G1.inW)),
      let (ys1, f1) := evalSliceGen G1 xs
      let (ys2, f2) := evalSliceGen G2 (xs.map (fun x => hIn ▸ x))
      ys1 = ys2.map (fun y => hOut ▸ y) ∧ f1 = (hFin ▸ f2) := by
  unfold checkSliceBisim at hCert
  simp only [Bool.and_eq_true] at hCert
  rcases hCert with ⟨⟨hBase, hStep⟩, hFinOk⟩
  have hStepAll := forallBv_sound hStep
  have hFinAll := forallBv_sound hFinOk
  have hInv : ∀ (xs : List (BitVec G1.inW)) (q1 : BitVec G1.stW) (q2 : BitVec G2.stW),
      cert.rel q1 q2 = true →
      let (ys1, f1) := evalSliceFrom G1 q1 xs
      let (ys2, f2) := evalSliceFrom G2 q2 (xs.map (fun x => hIn ▸ x))
      ys1 = ys2.map (fun y => hOut ▸ y) ∧ f1 = (hFin ▸ f2) := by
    intro xs
    induction xs with
    | nil =>
      intro q1 q2 hR
      simp only [List.map_nil, evalSliceFrom]
      refine ⟨trivial, ?_⟩
      have hf := forallBv_sound (hFinAll q1) q2
      simp only [hR, ↓reduceIte, decide_eq_true_eq] at hf
      exact hf
    | cons x rest ih =>
      intro q1 q2 hR
      simp only [List.map_cons, evalSliceFrom]
      have hs := forallBv_sound (hStepAll q1) q2
      simp only [hR, ↓reduceIte] at hs
      have hsx := forallBv_sound hs x
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsx
      rcases hsx with ⟨hy, hR'⟩
      have hRec := ih (G1.step q1 x).1 (G2.step q2 (hIn ▸ x)).1 hR'
      exact ⟨by simp [hy, hRec.1], hRec.2⟩
  intro xs
  exact hInv xs G1.initSt G2.initSt hBase

def evalBlock2From (B : Block2Gen) (q : BitVec B.stW) :
    List (BitVec B.inW × BitVec B.inW) → List (BitVec B.outW) × BitVec B.finW
  | [] => ([], B.final q)
  | (x0, x1) :: rest =>
    let (q', y0, y1) := B.step q x0 x1
    let (ys, f) := evalBlock2From B q' rest
    (y0 :: y1 :: ys, f)

def evalBlock2Gen (B : Block2Gen) (blocks : List (BitVec B.inW × BitVec B.inW)) :
    List (BitVec B.outW) × BitVec B.finW :=
  evalBlock2From B B.initSt blocks

def flattenPairs {α : Type} : List (α × α) → List α
  | [] => []
  | (a, b) :: rest => a :: b :: flattenPairs rest

/-- Decidable finite 2-step synchronization checker between 1-bit `G1` and 2-bit block `B2`. -/
def checkBlock2Bisim (G1 : SliceGen) (B2 : Block2Gen)
    (hIn : G1.inW = B2.inW) (hOut : G1.outW = B2.outW) (hFin : G1.finW = B2.finW)
    (cert : SliceBisimCert G1.stW B2.stW) : Bool :=
  let baseOk := cert.rel G1.initSt B2.initSt
  let stepOk := forallBv G1.stW fun q1 =>
    forallBv B2.stW fun q2 =>
      if cert.rel q1 q2 then
        forallBv G1.inW fun x0 =>
          forallBv G1.inW fun x1 =>
            let (q1m, y10) := G1.step q1 x0
            let (q1', y11) := G1.step q1m x1
            let (q2', y20, y21) := B2.step q2 (hIn ▸ x0) (hIn ▸ x1)
            decide (y10 = (hOut ▸ y20)) && decide (y11 = (hOut ▸ y21)) && cert.rel q1' q2'
      else true
  let finOk := forallBv G1.stW fun q1 =>
    forallBv B2.stW fun q2 =>
      if cert.rel q1 q2 then
        decide (G1.final q1 = (hFin ▸ B2.final q2))
      else true
  baseOk && stepOk && finOk

/-- **General Soundness Meta-Theorem (Engine 1B)**:
    A finite 2-stride bisimulation certificate discharges equivalence of a 1-bit serial
    bit-slice generator and a 2-bit speculative/block generator for ALL `n : Nat` (width `2n`). -/
theorem block2_bisim_sound (G1 : SliceGen) (B2 : Block2Gen)
    (hIn : G1.inW = B2.inW) (hOut : G1.outW = B2.outW) (hFin : G1.finW = B2.finW)
    (cert : SliceBisimCert G1.stW B2.stW)
    (hCert : checkBlock2Bisim G1 B2 hIn hOut hFin cert = true) :
    ∀ (blocks : List (BitVec G1.inW × BitVec G1.inW)),
      let (ys1, f1) := evalSliceGen G1 (flattenPairs blocks)
      let (ys2, f2) := evalBlock2Gen B2 (blocks.map (fun p => (hIn ▸ p.1, hIn ▸ p.2)))
      ys1 = ys2.map (fun y => hOut ▸ y) ∧ f1 = (hFin ▸ f2) := by
  unfold checkBlock2Bisim at hCert
  simp only [Bool.and_eq_true] at hCert
  rcases hCert with ⟨⟨hBase, hStep⟩, hFinOk⟩
  have hStepAll := forallBv_sound hStep
  have hFinAll := forallBv_sound hFinOk
  have hInv : ∀ (blocks : List (BitVec G1.inW × BitVec G1.inW))
      (q1 : BitVec G1.stW) (q2 : BitVec B2.stW),
      cert.rel q1 q2 = true →
      let (ys1, f1) := evalSliceFrom G1 q1 (flattenPairs blocks)
      let (ys2, f2) := evalBlock2From B2 q2 (blocks.map (fun p => (hIn ▸ p.1, hIn ▸ p.2)))
      ys1 = ys2.map (fun y => hOut ▸ y) ∧ f1 = (hFin ▸ f2) := by
    intro blocks
    induction blocks with
    | nil =>
      intro q1 q2 hR
      simp only [flattenPairs, List.map_nil, evalSliceFrom, evalBlock2From]
      refine ⟨trivial, ?_⟩
      have hf := forallBv_sound (hFinAll q1) q2
      simp only [hR, ↓reduceIte, decide_eq_true_eq] at hf
      exact hf
    | cons p rest ih =>
      rcases p with ⟨x0, x1⟩
      intro q1 q2 hR
      simp only [flattenPairs, List.map_cons, evalSliceFrom, evalBlock2From]
      have hs := forallBv_sound (hStepAll q1) q2
      simp only [hR, ↓reduceIte] at hs
      have hs01 := forallBv_sound (forallBv_sound hs x0) x1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs01
      rcases hs01 with ⟨⟨hy0, hy1⟩, hR'⟩
      have hRec := ih (G1.step (G1.step q1 x0).1 x1).1 (B2.step q2 (hIn ▸ x0) (hIn ▸ x1)).1 hR'
      exact ⟨by simp [hy0, hy1, hRec.1], hRec.2⟩
  intro blocks
  exact hInv blocks G1.initSt B2.initSt hBase

theorem rangeFold_valid {α : Type} {op : α → α → α} {V : α → Bool}
    (hClosed : ∀ u v, V u = true → V v = true → V (op u v) = true)
    {xs : Nat → α} (hxs : ∀ i, V (xs i) = true) :
    ∀ lo len, V (rangeFold op xs lo len) = true := by
  intro lo len
  induction len with
  | zero => exact hxs lo
  | succ n ih =>
    cases n with
    | zero => exact hxs lo
    | succ m =>
      simp only [rangeFold]
      exact hClosed _ _ ih (hxs _)

theorem rangeFold_append {α : Type} {op : α → α → α} {V : α → Bool}
    (hClosed : ∀ u v, V u = true → V v = true → V (op u v) = true)
    (hAssoc : ∀ u v w, V u = true → V v = true → V w = true → op (op u v) w = op u (op v w))
    {xs : Nat → α} (hxs : ∀ i, V (xs i) = true) :
    ∀ lo a b, a ≥ 1 → b ≥ 1 →
      op (rangeFold op xs lo a) (rangeFold op xs (lo + a) b) = rangeFold op xs lo (a + b) := by
  intro lo a b ha hb
  induction b with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      -- b = 1: op (rangeFold lo a) (xs (lo + a)) = rangeFold lo (a + 1)
      cases a with
      | zero => omega
      | succ a' =>
        simp only [rangeFold, Nat.add_assoc]
    | succ m' =>
      -- b = m' + 2
      have hb' : m' + 1 ≥ 1 := by omega
      have hRec := ih hb'
      simp only [rangeFold]
      rw [← hAssoc _ _ _
            (rangeFold_valid hClosed hxs lo a)
            (rangeFold_valid hClosed hxs (lo + a) (m' + 1))
            (hxs _)]
      rw [hRec]
      -- Now LHS is op (rangeFold lo (a + (m' + 1))) (xs (lo + a + m' + 1))
      -- RHS is op (rangeFold lo (a.add m' + 1)) (xs (lo + a.add m' + 1))
      have hEq1 : a + (m' + 1) = a.add m' + 1 := by simp [Nat.add_eq]; omega
      have hEq2 : lo + a + m' + 1 = lo + a.add m' + 1 := by simp [Nat.add_eq]; omega
      rw [hEq1, hEq2]

-- Soundness proofs for ALL THREE parallel topologies = `serialPrefix` under REACHABLE associativity!

theorem sklansky_eq_serial {α : Type} {op : α → α → α} {V : α → Bool}
    (hClosed : ∀ u v, V u = true → V v = true → V (op u v) = true)
    (hAssoc : ∀ u v w, V u = true → V v = true → V w = true → op (op u v) w = op u (op v w)) :
    ∀ (k : Nat) (xs : Fin (2 ^ k) → α), (∀ i, V (xs i) = true) →
      sklanskyPrefix op k xs = serialPrefix op k xs := by
  intro k
  induction k with
  | zero =>
    intro xs _
    funext i
    have hi : i.val = 0 := by have := i.isLt; simp at this; omega
    simp only [sklanskyPrefix, serialPrefix, hi, rangeFold, liftFn]
    have hlt : 0 < 2 ^ 0 := Nat.two_pow_pos 0
    simp only [hlt, ↓reduceDIte]
    congr 1
    exact Fin.ext hi
  | succ k ih =>
    intro xs hV
    funext i
    simp only [sklanskyPrefix, serialPrefix]
    let half := 2 ^ k
    let xsL : Fin half → α := fun j => xs ⟨j.val, by have := j.isLt; simp [half, Nat.pow_succ]; omega⟩
    let xsR : Fin half → α := fun j => xs ⟨half + j.val, by have := j.isLt; simp [half, Nat.pow_succ]; omega⟩
    have hVL : ∀ j, V (xsL j) = true := fun j => hV _
    have hVR : ∀ j, V (xsR j) = true := fun j => hV _
    have ihL := ih xsL hVL
    have ihR := ih xsR hVR
    have hPos : half ≥ 1 := Nat.two_pow_pos k
    have hLiftEq : ∀ (f g : Nat → α) (lo len : Nat),
        (∀ t, t < len → f (lo + t) = g (lo + t)) →
        len ≥ 1 → rangeFold op f lo len = rangeFold op g lo len := by
      intro f g lo len hfg hlen
      induction len with
      | zero => omega
      | succ m ihm =>
        cases m with
        | zero =>
          simp only [rangeFold]
          simpa using hfg 0 (by omega)
        | succ m' =>
          simp only [rangeFold]
          rw [ihm (fun t ht => hfg t (by omega)) (by omega)]
          have hlast := hfg (m' + 1) (by omega)
          have heq : lo + m' + 1 = lo + (m' + 1) := by omega
          rw [heq, hlast]
    by_cases hi : i.val < 2 ^ k
    · simp only [hi, ↓reduceDIte]
      have h1 := congrFun ihL ⟨i.val, hi⟩
      rw [h1]
      simp only [serialPrefix]
      apply hLiftEq
      · intro t ht
        simp only [liftFn, Nat.zero_add]
        have ht1 : t < 2 ^ k := by omega
        have ht2 : t < 2 ^ (k + 1) := by simp [Nat.pow_succ]; omega
        simp only [ht1, ht2, ↓reduceDIte, xsL]
      · omega
    · simp only [hi, ↓reduceDIte]
      have hLast := congrFun ihL ⟨half - 1, by omega⟩
      have hRight := congrFun ihR ⟨i.val - half, by have := i.isLt; simp [half, Nat.pow_succ] at *; omega⟩
      rw [hLast, hRight]
      simp only [serialPrefix]
      have hL_eq : rangeFold op (liftFn (xsL ⟨0, hPos⟩) xsL) 0 (half - 1 + 1) =
                   rangeFold op (liftFn (xs ⟨0, Nat.two_pow_pos (k + 1)⟩) xs) 0 half := by
        have hsub : half - 1 + 1 = half := by omega
        rw [hsub]
        apply hLiftEq
        · intro t ht
          simp only [liftFn, Nat.zero_add]
          have ht1 : t < half := by omega
          have ht2 : t < 2 ^ (k + 1) := by simp [half, Nat.pow_succ] at *; omega
          simp only [ht1, ht2, ↓reduceDIte, xsL]
        · omega
      have hR_eq : rangeFold op (liftFn (xsR ⟨0, hPos⟩) xsR) 0 (i.val - half + 1) =
                   rangeFold op (liftFn (xs ⟨0, Nat.two_pow_pos (k + 1)⟩) xs) half (i.val - half + 1) := by
        -- shift rangeFold by half!
        have hShift : ∀ (m : Nat), m ≥ 1 → m ≤ half →
            rangeFold op (liftFn (xsR ⟨0, hPos⟩) xsR) 0 m =
            rangeFold op (liftFn (xs ⟨0, Nat.two_pow_pos (k + 1)⟩) xs) half m := by
          intro m hm hle
          induction m with
          | zero => omega
          | succ m' ihm =>
            cases m' with
            | zero =>
              simp only [rangeFold, liftFn]
              have h0 : 0 < half := by omega
              have h2 : half < 2 ^ (k + 1) := by simp [Nat.pow_succ]; omega
              simp only [h0, h2, ↓reduceDIte, xsR, Nat.add_zero]
            | succ m'' =>
              simp only [rangeFold]
              rw [ihm (by omega) (by omega)]
              simp only [liftFn]
              have h1 : 0 + m'' + 1 < half := by omega
              have h2 : half + m'' + 1 < 2 ^ (k + 1) := by simp [Nat.pow_succ]; omega
              simp only [h1, h2, ↓reduceDIte, xsR]
              apply congrArg (op _)
              apply congrArg xs
              exact Fin.ext (by dsimp only; omega)
        exact hShift (i.val - half + 1) (by omega) (by have := i.isLt; simp [Nat.pow_succ] at *; omega)
      rw [hL_eq, hR_eq]
      have hVlift : ∀ t, V (liftFn (xs ⟨0, Nat.two_pow_pos (k + 1)⟩) xs t) = true := by
        intro t; simp only [liftFn]; split <;> exact hV _
      have hApp := rangeFold_append hClosed hAssoc hVlift 0 half (i.val - half + 1) hPos (by omega)
      have hLen : half + (i.val - half + 1) = i.val + 1 := by omega
      simpa [Nat.zero_add, hLen] using hApp

theorem brentKung_eq_serial {α : Type} {op : α → α → α} {V : α → Bool}
    (hClosed : ∀ u v, V u = true → V v = true → V (op u v) = true)
    (hAssoc : ∀ u v w, V u = true → V v = true → V w = true → op (op u v) w = op u (op v w)) :
    ∀ (k : Nat) (xs : Fin (2 ^ k) → α), (∀ i, V (xs i) = true) →
      brentKungPrefix op k xs = serialPrefix op k xs := by
  intro k
  induction k with
  | zero =>
    intro xs _
    funext i
    have hi : i.val = 0 := by have := i.isLt; simp at this; omega
    simp only [brentKungPrefix, serialPrefix, hi, rangeFold, liftFn]
    have hlt : 0 < 2 ^ 0 := Nat.two_pow_pos 0
    simp only [hlt, ↓reduceDIte]
    congr 1; exact Fin.ext hi
  | succ k ih =>
    intro xs hV
    let half := 2 ^ k
    have hPos : half ≥ 1 := Nat.two_pow_pos k
    let pairs : Fin half → α := fun j =>
      op (xs ⟨2 * j.val, by have := j.isLt; simp [half, Nat.pow_succ]; omega⟩)
         (xs ⟨2 * j.val + 1, by have := j.isLt; simp [half, Nat.pow_succ]; omega⟩)
    have hVpairs : ∀ j, V (pairs j) = true := fun j => hClosed _ _ (hV _) (hV _)
    have hVlift : ∀ t, V (liftFn (xs ⟨0, Nat.two_pow_pos (k + 1)⟩) xs t) = true := by
      intro t; simp only [liftFn]; split <;> exact hV _
    -- Key lemma: rangeFold of `pairs` on `0 .. m` equals rangeFold of `xs` on `0 .. 2*m`!
    have hPairsFold : ∀ m, 1 ≤ m → m ≤ half →
        rangeFold op (liftFn (pairs ⟨0, hPos⟩) pairs) 0 m =
        rangeFold op (liftFn (xs ⟨0, Nat.two_pow_pos (k + 1)⟩) xs) 0 (2 * m) := by
      intro m hm hle
      induction m with
      | zero => omega
      | succ m' ihm =>
        cases m' with
        | zero =>
          simp only [rangeFold, liftFn]
          have h0 : 0 < half := by omega
          have h0' : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
          have h1' : 1 < 2 ^ (k + 1) := by simp [Nat.pow_succ]; omega
          simp only [h0, h0', h1', ↓reduceDIte, pairs, Nat.mul_zero, Nat.zero_add]
        | succ m'' =>
          simp only [rangeFold]
          rw [ihm (by omega) (by omega)]
          have hlt : m'' + 1 < half := by omega
          have hlt0 : 2 * (m'' + 1) < 2 ^ (k + 1) := by simp [Nat.pow_succ]; omega
          have hlt1 : 2 * (m'' + 1) + 1 < 2 ^ (k + 1) := by simp [Nat.pow_succ]; omega
          have hPairEl : liftFn (pairs ⟨0, hPos⟩) pairs (0 + m'' + 1) =
              rangeFold op (liftFn (xs ⟨0, Nat.two_pow_pos (k + 1)⟩) xs) (2 * (m'' + 1)) 2 := by
            simp only [liftFn, rangeFold, Nat.zero_add, Nat.add_zero]
            simp only [hlt, hlt0, hlt1, ↓reduceDIte, pairs]
          rw [hPairEl]
          have hApp := rangeFold_append hClosed hAssoc hVlift 0 (2 * (m'' + 1)) 2 (by omega) (by omega)
          have hLen : 2 * (m'' + 1) + 2 = 2 * (m'' + 2) := by omega
          simpa [Nat.zero_add, hLen] using hApp
    have ihP := ih pairs hVpairs
    funext i
    simp only [brentKungPrefix, serialPrefix]
    by_cases h0 : i.val = 0
    · simp only [h0, ↓reduceDIte, rangeFold, liftFn]
      have hlt : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
      simp only [hlt, ↓reduceDIte]
    · simp only [h0, ↓reduceDIte]
      by_cases hOdd : i.val % 2 = 1
      · simp only [hOdd, ↓reduceDIte]
        have hP := congrFun ihP ⟨i.val / 2, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
        rw [hP]
        simp only [serialPrefix]
        have hEq := hPairsFold (i.val / 2 + 1) (by omega) (by have := i.isLt; simp [Nat.pow_succ] at *; omega)
        have hLen : 2 * (i.val / 2 + 1) = i.val + 1 := by omega
        simpa [hLen] using hEq
      · simp only [hOdd, ↓reduceDIte]
        have hP := congrFun ihP ⟨i.val / 2 - 1, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
        rw [hP]
        simp only [serialPrefix]
        have hEq := hPairsFold (i.val / 2 - 1 + 1) (by omega) (by have := i.isLt; simp [Nat.pow_succ] at *; omega)
        rw [hEq]
        have hLen : 2 * (i.val / 2 - 1 + 1) = i.val := by omega
        rw [hLen]
        have hTail : xs i = rangeFold op (liftFn (xs ⟨0, Nat.two_pow_pos (k + 1)⟩) xs) i.val 1 := by
          simp only [rangeFold, liftFn, i.isLt, ↓reduceDIte]
        rw [hTail]
        have hApp := rangeFold_append hClosed hAssoc hVlift 0 i.val 1 (by omega) (by omega)
        simpa [Nat.zero_add] using hApp

theorem koggeStone_eq_serial {α : Type} {op : α → α → α} {V : α → Bool}
    (hClosed : ∀ u v, V u = true → V v = true → V (op u v) = true)
    (hAssoc : ∀ u v w, V u = true → V v = true → V w = true → op (op u v) w = op u (op v w)) :
    ∀ (k : Nat) (xs : Fin (2 ^ k) → α), (∀ i, V (xs i) = true) →
      koggeStonePrefix op k xs = serialPrefix op k xs := by
  intro k xs hV
  have hVlift : ∀ t, V (liftFn (xs ⟨0, Nat.two_pow_pos k⟩) xs t) = true := by
    intro t; simp only [liftFn]; split <;> exact hV _
  -- Stage invariant: after `s` stages, wire `i` holds the fold of length `min (i + 1) (2^s)` ending at `i`!
  have hStage : ∀ (s : Nat) (i : Fin (2 ^ k)),
      koggeStoneRun op s xs i =
        rangeFold op (liftFn (xs ⟨0, Nat.two_pow_pos k⟩) xs)
          (i.val + 1 - min (i.val + 1) (2 ^ s)) (min (i.val + 1) (2 ^ s)) := by
    intro s
    induction s with
    | zero =>
      intro i
      simp only [koggeStoneRun, Nat.pow_zero]
      have hmin : min (i.val + 1) 1 = 1 := by omega
      rw [hmin]
      have hsub : i.val + 1 - 1 = i.val := by omega
      rw [hsub]
      simp only [rangeFold, liftFn, i.isLt, ↓reduceDIte]
    | succ s ih =>
      intro i
      simp only [koggeStoneRun, koggeStoneStage]
      by_cases hlt : i.val < 2 ^ s
      · simp only [hlt, ↓reduceIte]
        rw [ih i]
        have hm1 : min (i.val + 1) (2 ^ s) = i.val + 1 := by omega
        have hm2 : min (i.val + 1) (2 ^ (s + 1)) = i.val + 1 := by simp [Nat.pow_succ]; omega
        rw [hm1, hm2]
      · simp only [hlt, ↓reduceIte]
        let d := 2 ^ s
        have hdPos : d ≥ 1 := Nat.two_pow_pos s
        have hLeft := ih ⟨i.val - d, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
        have hRight := ih i
        rw [hLeft, hRight]
        have hmR : min (i.val + 1) d = d := by omega
        rw [hmR]
        let a := min (i.val - d + 1) d
        have haPos : a ≥ 1 := by omega
        have hStartL : i.val - d + 1 - a + a = i.val + 1 - d := by omega
        have hApp := rangeFold_append hClosed hAssoc hVlift (i.val - d + 1 - a) a d haPos hdPos
        rw [hStartL] at hApp
        rw [hApp]
        have hmTot : min (i.val + 1) (2 ^ (s + 1)) = a + d := by simp [a, d, Nat.pow_succ]; omega
        have hLoTot : i.val + 1 - (a + d) = i.val - d + 1 - a := by omega
        rw [hmTot, hLoTot]
  funext i
  simp only [koggeStonePrefix, serialPrefix]
  rw [hStage k i]
  have hmin : min (i.val + 1) (2 ^ k) = i.val + 1 := by have := i.isLt; omega
  rw [hmin]
  have hsub : i.val + 1 - (i.val + 1) = 0 := by omega
  rw [hsub]

/-- Helper: evaluate `SliceGen` state after `len` steps starting at `lo`. -/
def sliceStateAfter (G : SliceGen) (xs : Nat → BitVec G.inW) (c0 : BitVec G.stW) :
    Nat → BitVec G.stW
  | 0     => c0
  | n + 1 => (G.step (sliceStateAfter G xs c0 n) (xs n)).1

/-- Helper: `evalSliceFrom` on `List.ofFn xs` produces outputs `(G.step (sliceStateAfter n) (xs n)).2`
    and final output `G.final (sliceStateAfter n)`. -/
theorem evalSliceFrom_ofFn (G : SliceGen) :
    ∀ (n : Nat) (c0 : BitVec G.stW) (xs : Fin n → BitVec G.inW),
      let d := BitVec.zero G.inW
      let res := evalSliceFrom G c0 (finToList xs)
      res.1 = finToList (fun i : Fin n => (G.step (sliceStateAfter G (liftFn d xs) c0 i.val) (xs i)).2) ∧
      res.2 = G.final (sliceStateAfter G (liftFn d xs) c0 n) := by
  intro n
  induction n with
  | zero =>
    intro c0 xs
    simp [finToList, List.finRange_zero, evalSliceFrom, sliceStateAfter]
  | succ n ih =>
    intro c0 xs
    have hFinRange : List.finRange (n + 1) = ⟨0, Nat.zero_lt_succ n⟩ :: (List.finRange n).map Fin.succ :=
      List.finRange_succ
    simp only [finToList, hFinRange, List.map_cons, List.map_map, evalSliceFrom]
    let d := BitVec.zero G.inW
    let xsTail : Fin n → BitVec G.inW := fun j => xs j.succ
    let c1 := (G.step c0 (xs ⟨0, Nat.zero_lt_succ n⟩)).1
    have hRec := ih c1 xsTail
    -- Relate sliceStateAfter on xsTail from c1 to sliceStateAfter on xs from c0 at m + 1
    have hShift : ∀ (m : Nat), m ≤ n →
        sliceStateAfter G (liftFn d xsTail) c1 m =
        sliceStateAfter G (liftFn d xs) c0 (m + 1) := by
      intro m hm
      induction m with
      | zero =>
        simp only [sliceStateAfter, liftFn, Nat.zero_lt_succ, ↓reduceDIte, c1]
      | succ m' ihm =>
        simp only [sliceStateAfter]
        rw [ihm (by omega)]
        simp only [liftFn]
        have h1 : m' < n := by omega
        have h2 : m' + 1 < n + 1 := by omega
        simp only [h1, h2, ↓reduceDIte, xsTail, Fin.succ]
        rfl
    constructor
    · change (G.step c0 (xs ⟨0, Nat.zero_lt_succ n⟩)).2 :: (evalSliceFrom G c1 (finToList xsTail)).1 = _
      rw [hRec.1]
      apply congrArg ((G.step c0 (xs ⟨0, Nat.zero_lt_succ n⟩)).2 :: ·)
      simp only [finToList]
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, xsTail]
      rw [hShift j.val (Nat.le_of_lt j.isLt)]
      rfl
    · change (evalSliceFrom G c1 (finToList xsTail)).2 = _
      rw [hRec.2, hShift n (Nat.le_refl n)]

/-- **General Soundness Meta-Theorem (Engine 2)**:
    A single finite `PrefixToSliceCert` (checked by `decide`) certifies that ALL FOUR
    `2^k`-width parallel-prefix hardware circuits (`Serial`, `Sklansky`, `Brent–Kung`,
    `Kogge–Stone`) are bit-for-bit equivalent to the bit-slice generator `G` for ALL `k : Nat`,
    ALL `2^k`-width inputs `xs`, and ALL initial carry/state values `c0`! -/
theorem prefix_all_topologies_sound (P : PrefixSpec) (G : SliceGen)
    (hIn : P.inW = G.inW) (hSt : P.stW = G.stW) (hOut : P.outW = G.outW)
    (cert : PrefixToSliceCert P.tokW)
    (hCert : checkPrefixToSliceCert P G hIn hSt hOut cert = true) :
    ∀ (k : Nat) (c0 : BitVec P.stW) (xs : Fin (2 ^ k) → BitVec P.inW),
      -- 1. All 4 hardware topologies produce identical outputs and carry-out!
      evalPrefixCircuit P sklanskyPrefix k c0 xs = evalPrefixCircuit P serialPrefix k c0 xs ∧
      evalPrefixCircuit P brentKungPrefix k c0 xs = evalPrefixCircuit P serialPrefix k c0 xs ∧
      evalPrefixCircuit P koggeStonePrefix k c0 xs = evalPrefixCircuit P serialPrefix k c0 xs ∧
      -- 2. And they ALL match the serial bit-slice generator `G` bit-for-bit!
      (let (outFn, cOut) := evalPrefixCircuit P serialPrefix k c0 xs
       let (ysG, fG) := evalSliceFrom G (hSt ▸ c0) (finToList (fun i => hIn ▸ xs i))
       finToList (fun i => hOut ▸ outFn i) = ysG ∧ G.final (hSt ▸ cOut) = fG) := by
  unfold checkPrefixToSliceCert at hCert
  simp only [Bool.and_eq_true] at hCert
  rcases hCert with ⟨⟨⟨⟨hPre, hClosed⟩, hAssoc⟩, hHom⟩, hBase⟩
  have hPreAll := forallBv_sound hPre
  have hClosedFn : ∀ u v, cert.valid u = true → cert.valid v = true → cert.valid (P.op u v) = true := by
    intro u v hu hv
    have h := forallBv_sound (forallBv_sound hClosed u) v
    simpa [hu, hv] using h
  have hAssocFn : ∀ u v w, cert.valid u = true → cert.valid v = true → cert.valid w = true →
      P.op (P.op u v) w = P.op u (P.op v w) := by
    intro u v w hu hv hw
    have h := forallBv_sound (forallBv_sound (forallBv_sound hAssoc u) v) w
    simpa [hu, hv, hw] using h
  have hHomFn : ∀ u v c, cert.valid u = true → cert.valid v = true →
      P.act (P.op u v) c = P.act v (P.act u c) := by
    intro u v c hu hv
    have h := forallBv_sound (forallBv_sound hHom u) v
    simp [hu, hv] at h
    have hc := forallBv_sound h c
    simpa using hc
  have hBaseFn : ∀ c x,
      P.act (P.pre x) c = (hSt.symm ▸ (G.step (hSt ▸ c) (hIn ▸ x)).1) ∧
      P.post x c = (hOut.symm ▸ (G.step (hSt ▸ c) (hIn ▸ x)).2) := by
    intro c x
    have h := forallBv_sound (forallBv_sound hBase c) x
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h
  intro k c0 xs
  have hVtoks : ∀ i : Fin (2 ^ k), cert.valid (P.pre (xs i)) = true := fun i => hPreAll (xs i)
  have hSkl := sklansky_eq_serial hClosedFn hAssocFn k (fun i => P.pre (xs i)) hVtoks
  have hBK  := brentKung_eq_serial hClosedFn hAssocFn k (fun i => P.pre (xs i)) hVtoks
  have hKS  := koggeStone_eq_serial hClosedFn hAssocFn k (fun i => P.pre (xs i)) hVtoks
  refine ⟨by simp [evalPrefixCircuit, hSkl], by simp [evalPrefixCircuit, hBK],
          by simp [evalPrefixCircuit, hKS], ?_⟩
  -- Helper when widths are definitionally equal, avoiding struct-expansion noise
  have hSerialEq : ∀ (P0 : PrefixSpec) (G0 : SliceGen)
      (hIn0 : P0.inW = G0.inW) (hSt0 : P0.stW = G0.stW) (hOut0 : P0.outW = G0.outW)
      (V : BitVec P0.tokW → Bool)
      (hPre0 : ∀ x, V (P0.pre x) = true)
      (hCl0 : ∀ u v, V u = true → V v = true → V (P0.op u v) = true)
      (hHom0 : ∀ u v c, V u = true → V v = true → P0.act (P0.op u v) c = P0.act v (P0.act u c))
      (hBase0 : ∀ c x,
        P0.act (P0.pre x) c = (hSt0.symm ▸ (G0.step (hSt0 ▸ c) (hIn0 ▸ x)).1) ∧
        P0.post x c = (hOut0.symm ▸ (G0.step (hSt0 ▸ c) (hIn0 ▸ x)).2))
      (c0 : BitVec P0.stW) (xs : Fin (2 ^ k) → BitVec P0.inW),
      let (outFn, cOut) := evalPrefixCircuit P0 serialPrefix k c0 xs
      let (ysG, fG) := evalSliceFrom G0 (hSt0 ▸ c0) (finToList (fun i => hIn0 ▸ xs i))
      finToList (fun i => hOut0 ▸ outFn i) = ysG ∧ G0.final (hSt0 ▸ cOut) = fG := by
    intro P0 G0 hIn0 hSt0 hOut0
    cases P0 with | mk inW tokW stW outW preNet opNet actNet postNet hPreIn hPreOut hOpIn hOpOut hActIn hActOut hPostIn hPostOut =>
    cases G0 with | mk stW' inW' outW' finW' initSt stepNet finNet hStepIn hStepOut hFinIn hFinOut =>
    dsimp only at hIn0 hSt0 hOut0
    subst hIn0; subst hSt0; subst hOut0
    intro V hPre0 hCl0 hHom0 hBase0 c0 xs
    let P' : PrefixSpec := ⟨inW, tokW, stW, outW, preNet, opNet, actNet, postNet,
                            hPreIn, hPreOut, hOpIn, hOpOut, hActIn, hActOut, hPostIn, hPostOut⟩
    let G' : SliceGen := ⟨stW, inW, outW, finW', initSt, stepNet, finNet,
                          hStepIn, hStepOut, hFinIn, hFinOut⟩
    have hVlift : ∀ t, V (liftFn (P'.pre (xs ⟨0, Nat.two_pow_pos k⟩)) (fun i => P'.pre (xs i)) t) = true := by
      intro t; simp only [liftFn]; split <;> exact hPre0 _
    have hActRange : ∀ m, m < 2 ^ k →
        P'.act (rangeFold P'.op (liftFn (P'.pre (xs ⟨0, Nat.two_pow_pos k⟩)) (fun i => P'.pre (xs i))) 0 (m + 1)) c0 =
        sliceStateAfter G' (liftFn (BitVec.zero inW) xs) c0 (m + 1) := by
      intro m hm
      induction m with
      | zero =>
        simp only [rangeFold, liftFn, Nat.two_pow_pos k, ↓reduceDIte, sliceStateAfter]
        exact (hBase0 c0 (xs ⟨0, Nat.two_pow_pos k⟩)).1
      | succ m' ihm =>
        simp only [rangeFold, sliceStateAfter]
        rw [hHom0 _ _ c0 (rangeFold_valid hCl0 hVlift 0 (m' + 1)) (hVlift _)]
        rw [ihm (by omega)]
        have hlt : m' + 1 < 2 ^ k := by omega
        simp only [liftFn, Nat.zero_add, hlt, ↓reduceDIte]
        exact (hBase0 _ (xs ⟨m' + 1, hlt⟩)).1
    have hSlice := evalSliceFrom_ofFn G' (2 ^ k) c0 xs
    change finToList (evalPrefixCircuit P' serialPrefix k c0 xs).1 = (evalSliceFrom G' c0 (finToList xs)).1 ∧
           G'.final (evalPrefixCircuit P' serialPrefix k c0 xs).2 = (evalSliceFrom G' c0 (finToList xs)).2
    simp only [evalPrefixCircuit, serialPrefix]
    constructor
    · rw [hSlice.1]
      simp only [finToList]
      apply List.map_congr_left
      intro i _
      by_cases hi0 : i.val = 0
      · simp only [hi0, ↓reduceDIte, sliceStateAfter]
        exact (hBase0 c0 (xs i)).2
      · simp only [hi0, ↓reduceDIte]
        have hsub : i.val - 1 + 1 = i.val := by omega
        have hA := hActRange (i.val - 1) (by have := i.isLt; omega)
        rw [hsub] at hA
        rw [hsub, hA]
        exact (hBase0 _ (xs i)).2
    · rw [hSlice.2]
      have hLast := hActRange (2 ^ k - 1) (by have := Nat.two_pow_pos k; omega)
      have hsub : 2 ^ k - 1 + 1 = 2 ^ k := by have := Nat.two_pow_pos k; omega
      rw [hsub] at hLast
      rw [hsub, hLast]
  exact hSerialEq P G hIn hSt hOut cert.valid hPreAll hClosedFn hHomFn hBaseFn c0 xs

-- ============================================================================
-- CONCRETE GATE-LEVEL HARDWARE NETLISTS & CERTIFIED THEOREMS FOR ENGINES 1 & 2
-- ============================================================================

/-- 1-bit Full Adder step `GateNet`: inputs `[c, a, b]` (0=c, 1=a, 2=b), outputs `[cout, sum]`. -/
def rippleAdderStepNet : GateNet :=
  { inW := 3
    gates := [
      .xor 1 2,     -- w3 = a ^ b
      .xor 3 0,     -- w4 = sum = (a ^ b) ^ c
      .and 1 2,     -- w5 = a & b
      .and 0 3,     -- w6 = c & (a ^ b)
      .or  5 6      -- w7 = cout = (a & b) | (c & (a ^ b))
    ]
    outs := [7, 4] }

/-- Reference arbitrary-width Ripple-Carry Adder (`SliceGen`: 1-bit carry, 2-bit input `(a,b)`, 1-bit sum). -/
def rippleAdderGen : SliceGen :=
  { stW := 1, inW := 2, outW := 1, finW := 1
    initSt := 0#1
    stepNet := rippleAdderStepNet
    finNet := id1Net
    hStepIn := rfl, hStepOut := rfl, hFinIn := rfl, hFinOut := rfl }

/-- Dual-Rail Complementary-Carry Adder (`SliceGen`: 2-bit state `[c, ~c]`, 2-bit input `(a,b)`).
    Inputs: 0=q0(c), 1=q1(~c), 2=a, 3=b. Outputs: `[nq0, nq1, sum]`. -/
def dualRailAdderStepNet : GateNet :=
  { inW := 4
    gates := [
      .xor 2 3,     -- w4 = a ^ b
      .xor 4 0,     -- w5 = sum = (a ^ b) ^ q0
      .and 2 3,     -- w6 = a & b
      .and 0 4,     -- w7 = q0 & (a ^ b)
      .or  6 7,     -- w8 = nq0 = (a & b) | (q0 & (a ^ b))
      .nor 2 3,     -- w9 = ~a & ~b
      .and 1 4,     -- w10 = q1 & (a ^ b)
      .or  9 10     -- w11 = nq1 = (~a & ~b) | (q1 & (a ^ b))
    ]
    outs := [8, 11, 5] }

def projLo2Net : GateNet := { inW := 2, gates := [], outs := [0] }

def dualRailAdderGen : SliceGen :=
  { stW := 2, inW := 2, outW := 1, finW := 1
    initSt := 2#2   -- q0 = 0, q1 = 1 (i.e. binary 10 = 2)
    stepNet := dualRailAdderStepNet
    finNet := projLo2Net
    hStepIn := rfl, hStepOut := rfl, hFinIn := rfl, hFinOut := rfl }

/-- Explicit 8-bit finite bisimulation certificate relating 1-bit `c` to 2-bit `(q0, q1) = (c, ~c)`:
    `bvCat q1 q2` has bit0=c, bit1=q0, bit2=q1.
    Valid pairs: (c=0, q0=0, q1=1) → index 4; (c=1, q0=1, q1=0) → index 3.
    Bitmask = 2^3 + 2^4 = 8 + 16 = 24. -/
def dualRailBisimCert : SliceBisimCert 1 2 := ⟨24#8⟩

/-- **Certified Infinite Theorem 1.1**: Ripple-Carry Adder ≡ Dual-Rail Complementary-Carry Adder
    for ALL widths `w : Nat`! Discharged automatically via `decide`. -/
theorem ripple_eq_dualRail_all_w :
    ∀ (xs : List (BitVec 2)), evalSliceGen rippleAdderGen xs = evalSliceGen dualRailAdderGen xs := by
  have hCert : checkSliceBisim rippleAdderGen dualRailAdderGen rfl rfl rfl dualRailBisimCert = true := by
    decide
  intro xs
  have h := slice_bisim_sound rippleAdderGen dualRailAdderGen rfl rfl rfl dualRailBisimCert hCert xs
  rcases h with ⟨h1, h2⟩
  refine Prod.ext ?_ ?_
  · exact h1.trans ((List.map_id' _).trans
      (congrArg (fun l => (evalSliceGen dualRailAdderGen l).1) (List.map_id' _)))
  · exact h2.trans (congrArg (fun l => (evalSliceGen dualRailAdderGen l).2) (List.map_id' _))

/-- 2-Bit Speculative Carry-Select Adder (`Block2Gen`):
    Inputs: 0=cin, 1=a0, 2=b0, 3=a1, 4=b1.
    Computes BOTH `cin=0` and `cin=1` 2-bit sums+carries in parallel, then muxes by `cin`!
    Outputs: `[cout, s0, s1]`. -/
def carrySelect2StepNet : GateNet :=
  { inW := 5
    gates := [
      -- Bit 0 shared propagate/generate
      .xor 1 2,     -- w5  = p0 = a0 ^ b0
      .and 1 2,     -- w6  = g0 = a0 & b0
      -- Bit 1 shared propagate/generate
      .xor 3 4,     -- w7  = p1 = a1 ^ b1
      .and 3 4,     -- w8  = g1 = a1 & b1
      -- Speculative Path 0 (assuming cin = 0):
      --   s0_0 = p0, c0_1 = g0
      --   s1_0 = p1 ^ g0, c0_2 = g1 | (g0 & p1)
      .xor 7 6,     -- w9  = s1_0
      .and 6 7,     -- w10 = g0 & p1
      .or  8 10,    -- w11 = c0_2
      -- Speculative Path 1 (assuming cin = 1):
      --   s0_1 = ~p0, c1_1 = g0 | p0
      --   s1_1 = p1 ^ c1_1, c1_2 = g1 | (c1_1 & p1)
      .not 5,       -- w12 = s0_1
      .or  6 5,     -- w13 = c1_1
      .xor 7 13,    -- w14 = s1_1
      .and 13 7,    -- w15 = c1_1 & p1
      .or  8 15,    -- w16 = c1_2
      -- Final Carry-Select MUX bank (controlled by w0 = cin)
      .mux 0 5 12,  -- w17 = s0
      .mux 0 9 14,  -- w18 = s1
      .mux 0 11 16  -- w19 = cout
    ]
    outs := [19, 17, 18] }

def carrySelect2Gen : Block2Gen :=
  { stW := 1, inW := 2, outW := 1, finW := 1
    initSt := 0#1
    stepNet := carrySelect2StepNet
    finNet := id1Net
    hStepIn := rfl, hStepOut := rfl, hFinIn := rfl, hFinOut := rfl }

/-- Equality bisimulation mask on 1-bit states: `(0,0) → 0`, `(1,1) → 3`, mask = `1 + 8 = 9`. -/
def eq1BisimCert : SliceBisimCert 1 1 := ⟨9#4⟩

/-- **Certified Infinite Theorem 1.2**: 1-Bit Ripple-Carry Adder ≡ 2-Bit Speculative Carry-Select
    Adder for ALL even widths `2n` (`∀ n : Nat`)! Discharged automatically via `decide`. -/
theorem ripple_eq_carrySelect2_all_n :
    ∀ (blocks : List (BitVec 2 × BitVec 2)),
      evalSliceGen rippleAdderGen (flattenPairs blocks) = evalBlock2Gen carrySelect2Gen blocks := by
  have hCert : checkBlock2Bisim rippleAdderGen carrySelect2Gen rfl rfl rfl eq1BisimCert = true := by
    decide
  intro blocks
  have h := block2_bisim_sound rippleAdderGen carrySelect2Gen rfl rfl rfl eq1BisimCert hCert blocks
  rcases h with ⟨h1, h2⟩
  have hId : ∀ {α : Type} (l : List (α × α)), List.map (fun p : α × α => (p.1, p.2)) l = l := by
    intro α l; induction l with
    | nil => rfl
    | cons p ps ih => exact congrArg (p :: ·) ih
  refine Prod.ext ?_ ?_
  · exact h1.trans ((List.map_id' _).trans
      (congrArg (fun l => (evalBlock2Gen carrySelect2Gen l).1) (hId _)))
  · exact h2.trans (congrArg (fun l => (evalBlock2Gen carrySelect2Gen l).2) (hId _))

-- Negative / Mutation Tests for Engine 1:
def brokenCarrySelect2StepNet : GateNet :=
  { carrySelect2StepNet with
    outs := [19, 18, 17] }  -- BUG: swapped s0 and s1 outputs!

def brokenCarrySelect2Gen : Block2Gen :=
  { carrySelect2Gen with stepNet := brokenCarrySelect2StepNet, hStepIn := rfl, hStepOut := rfl }

example : checkBlock2Bisim rippleAdderGen brokenCarrySelect2Gen rfl rfl rfl eq1BisimCert = false := by
  decide

example : checkSliceBisim rippleAdderGen dualRailAdderGen rfl rfl rfl ⟨9#8⟩ = false := by
  decide  -- BUG: wrong bisimulation relation mask rejected!

def prefixAdderBadOrXorSpec : PrefixSpec :=
  { prefixAdderOrPropSpec with opNet := opXorBlackNet, hOpIn := rfl, hOpOut := rfl }

-- Reachable-token masks:
--   XOR-prop valid tokens: {0=(0,0), 1=(1,0), 2=(0,1)} → mask = 2^0 + 2^1 + 2^2 = 7 = 0b0111
--   OR-prop  closure: pre lands in {0,2,3}, and op((0,0),(1,1)) = (1,0), so closure = all 4 states (15 = 0b1111)!
--   Active-low valid tokens: {1=(1,0), 2=(0,1), 3=(1,1)} → mask = 2^1 + 2^2 + 2^3 = 14 = 0b1110
def xorPropCert   : PrefixToSliceCert 2 := ⟨7#4⟩
def orPropCert    : PrefixToSliceCert 2 := ⟨15#4⟩
def activeLowCert : PrefixToSliceCert 2 := ⟨14#4⟩
def allTokensCert : PrefixToSliceCert 2 := ⟨15#4⟩

/-- **Sharpness Witness 2.1**: The don't-care-glitched black cell FAILS global associativity
    (rejected when `validMask = 15#4` = all 4 states), yet PASSES with reachable mask `7#4`! -/
example : checkPrefixToSliceCert prefixAdderGlitchedXorSpec rippleAdderGen rfl rfl rfl allTokensCert = false := by
  decide

example : checkPrefixToSliceCert prefixAdderGlitchedXorSpec rippleAdderGen rfl rfl rfl xorPropCert = true := by
  decide

/-- **Sharpness Witness 2.2**: The XOR-black-cell `(gR ^ (pR & gL), pR & pL)` PASSES on
    XOR-propagate (`7#4`), yet is REJECTED on OR-propagate (both `13#4` and `15#4`)!
    Also `13#4` (missing `(1,0)`) is REJECTED even for standard OR-propagate because
    `op((0,0),(1,1)) = (1,0)` breaks closure! -/
example : checkPrefixToSliceCert prefixAdderXorBlackSpec rippleAdderGen rfl rfl rfl xorPropCert = true := by
  decide

example : checkPrefixToSliceCert prefixAdderBadOrXorSpec rippleAdderGen rfl rfl rfl orPropCert = false := by
  decide

example : checkPrefixToSliceCert prefixAdderOrPropSpec rippleAdderGen rfl rfl rfl ⟨13#4⟩ = false := by
  decide

/-- **Certified Infinite Theorem 2.1 (4-Way Cross-Encoding Parallel-Prefix Adder Equivalence)**:
    For ALL `k : Nat` (width `2^k`), ALL `2^k`-bit inputs `xs`, and ALL carry-in `c0`:
    1. Sklansky Adder (XOR-propagate + don't-care-glitched black cell)
    2. Brent–Kung Adder (OR-propagate + standard black cell)
    3. Kogge–Stone Adder (active-low inverted NAND/XNOR cell)
    4. Sklansky Adder (XOR-propagate + XOR black cell)
    are ALL bit-for-bit identical to each other AND to the serial Ripple-Carry Adder! -/
theorem four_way_prefix_adder_equiv :
    ∀ (k : Nat) (c0 : BitVec 1) (xs : Fin (2 ^ k) → BitVec 2),
      evalPrefixCircuit prefixAdderGlitchedXorSpec sklanskyPrefix k c0 xs =
      evalPrefixCircuit prefixAdderOrPropSpec brentKungPrefix k c0 xs ∧
      evalPrefixCircuit prefixAdderOrPropSpec brentKungPrefix k c0 xs =
      evalPrefixCircuit prefixAdderActiveLowSpec koggeStonePrefix k c0 xs ∧
      evalPrefixCircuit prefixAdderActiveLowSpec koggeStonePrefix k c0 xs =
      evalPrefixCircuit prefixAdderXorBlackSpec sklanskyPrefix k c0 xs := by
  have h1 : checkPrefixToSliceCert prefixAdderGlitchedXorSpec rippleAdderGen rfl rfl rfl xorPropCert = true := by decide
  have h2 : checkPrefixToSliceCert prefixAdderOrPropSpec rippleAdderGen rfl rfl rfl orPropCert = true := by decide
  have h3 : checkPrefixToSliceCert prefixAdderActiveLowSpec rippleAdderGen rfl rfl rfl activeLowCert = true := by decide
  have h4 : checkPrefixToSliceCert prefixAdderXorBlackSpec rippleAdderGen rfl rfl rfl xorPropCert = true := by decide
  intro k c0 xs
  have s1 := prefix_all_topologies_sound prefixAdderGlitchedXorSpec rippleAdderGen rfl rfl rfl xorPropCert h1 k c0 xs
  have s2 := prefix_all_topologies_sound prefixAdderOrPropSpec rippleAdderGen rfl rfl rfl orPropCert h2 k c0 xs
  have s3 := prefix_all_topologies_sound prefixAdderActiveLowSpec rippleAdderGen rfl rfl rfl activeLowCert h3 k c0 xs
  have s4 := prefix_all_topologies_sound prefixAdderXorBlackSpec rippleAdderGen rfl rfl rfl xorPropCert h4 k c0 xs
  -- Helper: equal finToList + equal rippleAdderGen.final (= id) implies equal (outFn, cOut)
  have hExt : ∀ (p q : (Fin (2 ^ k) → BitVec 1) × BitVec 1),
      finToList p.1 = finToList q.1 → rippleAdderGen.final p.2 = rippleAdderGen.final q.2 → p = q := by
    intro ⟨f1, c1⟩ ⟨f2, c2⟩ hL hC
    refine Prod.ext ?_ ?_
    · funext i
      have hget : (finToList f1).getD i.val 0#1 = (finToList f2).getD i.val 0#1 := by
        rw [hL]
      have hfin : ∀ (f : Fin (2 ^ k) → BitVec 1), (finToList f).getD i.val 0#1 = f i := by
        intro f
        simp only [finToList, List.getD_eq_getElem?_getD, List.getElem?_map,
                   List.getElem?_eq_getElem (by simp [i.isLt] : i.val < (List.finRange (2 ^ k)).length),
                   List.getElem_finRange, Option.map_some, Option.getD_some]
        congr 1
      rw [hfin f1, hfin f2] at hget
      exact hget
    · have hcAll : forallBv 1 (fun x : BitVec 1 => (rippleAdderGen.final x).toNat == x.toNat) = true := by
        decide
      have hc1 : (rippleAdderGen.final c1).toNat = c1.toNat := beq_iff_eq.mp (forallBv_sound hcAll c1)
      have hc2 : (rippleAdderGen.final c2).toNat = c2.toNat := beq_iff_eq.mp (forallBv_sound hcAll c2)
      apply BitVec.eq_of_toNat_eq
      rw [← hc1, ← hc2]
      exact congrArg BitVec.toNat hC
  have e12 : evalPrefixCircuit prefixAdderGlitchedXorSpec sklanskyPrefix k c0 xs =
             evalPrefixCircuit prefixAdderOrPropSpec brentKungPrefix k c0 xs := by
    rw [s1.1, s2.2.1]
    exact hExt _ _ (s1.2.2.2.1.trans s2.2.2.2.1.symm) (s1.2.2.2.2.trans s2.2.2.2.2.symm)
  have e23 : evalPrefixCircuit prefixAdderOrPropSpec brentKungPrefix k c0 xs =
             evalPrefixCircuit prefixAdderActiveLowSpec koggeStonePrefix k c0 xs := by
    rw [s2.2.1, s3.2.2.1]
    exact hExt _ _ (s2.2.2.2.1.trans s3.2.2.2.1.symm) (s2.2.2.2.2.trans s3.2.2.2.2.symm)
  have e34 : evalPrefixCircuit prefixAdderActiveLowSpec koggeStonePrefix k c0 xs =
             evalPrefixCircuit prefixAdderXorBlackSpec sklanskyPrefix k c0 xs := by
    rw [s3.2.2.1, s4.1]
    exact hExt _ _ (s3.2.2.2.1.trans s4.2.2.2.1.symm) (s3.2.2.2.2.trans s4.2.2.2.2.symm)
  exact ⟨e12, e23, e34⟩

-- Also discharge a NON-ADDER prefix circuit family: Parallel-Prefix Gray-to-Binary Decoder!
def grayDecodeSliceStepNet : GateNet :=
  { inW := 2, gates := [.xor 0 1], outs := [2, 2] }  -- inputs [st, g] → [st ^ g, st ^ g]

def grayDecodeSliceGen : SliceGen :=
  { stW := 1, inW := 1, outW := 1, finW := 1, initSt := 0#1
    stepNet := grayDecodeSliceStepNet, finNet := id1Net
    hStepIn := rfl, hStepOut := rfl, hFinIn := rfl, hFinOut := rfl }

/-- **Certified Infinite Theorem 2.2 (Parallel-Prefix Gray-to-Binary Decoder Equivalence)**:
    For ALL `k : Nat`, Sklansky ≡ Brent–Kung ≡ Kogge–Stone ≡ Serial XOR-chain Gray-to-Binary
    decoders! Discharged automatically by the exact same Engine 2 compiler via `decide`. -/
theorem parallel_gray_decoder_equiv :
    ∀ (k : Nat) (c0 : BitVec 1) (xs : Fin (2 ^ k) → BitVec 1),
      evalPrefixCircuit grayDecodePrefixSpec sklanskyPrefix k c0 xs =
      evalPrefixCircuit grayDecodePrefixSpec serialPrefix k c0 xs ∧
      evalPrefixCircuit grayDecodePrefixSpec brentKungPrefix k c0 xs =
      evalPrefixCircuit grayDecodePrefixSpec serialPrefix k c0 xs ∧
      evalPrefixCircuit grayDecodePrefixSpec koggeStonePrefix k c0 xs =
      evalPrefixCircuit grayDecodePrefixSpec serialPrefix k c0 xs := by
  have hCert : checkPrefixToSliceCert grayDecodePrefixSpec grayDecodeSliceGen rfl rfl rfl ⟨3#2⟩ = true := by
    decide
  intro k c0 xs
  have h := prefix_all_topologies_sound grayDecodePrefixSpec grayDecodeSliceGen rfl rfl rfl ⟨3#2⟩ hCert k c0 xs
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Decidable finite certificate checker verifying that `M : MuxCell` implements the exact
    2:1 multiplexer `if sel then d1 else d0` across all 8 input combinations. -/
def checkMuxCell (M : MuxCell) : Bool :=
  [false, true].all fun s =>
    [false, true].all fun d0 =>
      [false, true].all fun d1 =>
        M.eval s d0 d1 == (if s then d1 else d0)

theorem checkMuxCell_sound {M : MuxCell} (h : checkMuxCell M = true) :
    ∀ s d0 d1, M.eval s d0 d1 = if s then d1 else d0 := by
  intro s d0 d1
  unfold checkMuxCell at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h
  cases s <;> cases d0 <;> cases d1 <;> simp_all

theorem iterRot_eq_rotBy {w : Nat} : ∀ (s : Nat) (xs : Fin w → Bool), iterRot s xs = rotBy s xs := by
  intro s
  induction s with
  | zero =>
    intro xs; funext i
    simp only [iterRot, rotBy, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  | succ s ih =>
    intro xs; funext i
    simp only [iterRot, ih, rotBy]
    apply congrArg xs
    apply Fin.ext
    have hw : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hmod : ((i.val + 1) % w + s) % w = (i.val + (s + 1)) % w := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1; omega
    exact hmod

/-- **General Soundness Meta-Theorem (Engine 3A)**:
    For ANY width `w : Nat` (including non-powers-of-2!), ANY control width `k : Nat`,
    and ANY concrete gate-level mux cell `M` passing `checkMuxCell`, the logarithmic barrel
    rotator equals the iterated 1-bit rotator by `listToNat ctrls`. -/
theorem barrelRot_eq_iterRot_sound (M : MuxCell) (hM : checkMuxCell M = true) :
    ∀ {w : Nat} (ctrls : List Bool) (xs : Fin w → Bool),
      barrelRot M ctrls xs = iterRot (listToNat ctrls) xs := by
  have hMux := checkMuxCell_sound hM
  have hAux : ∀ {w : Nat} (ctrls : List Bool) (step : Nat) (xs : Fin w → Bool),
      barrelRotAux M step ctrls xs = rotBy (step * listToNat ctrls) xs := by
    intro w ctrls
    induction ctrls with
    | nil =>
      intro step xs; funext i
      simp only [barrelRotAux, listToNat, Nat.mul_zero, rotBy, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
    | cons c cs ih =>
      intro step xs
      simp only [barrelRotAux, listToNat]
      let ys : Fin w → Bool := fun i =>
        M.eval c (xs i) (xs ⟨(i.val + step) % w, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩)
      have hys : ys = rotBy (if c then step else 0) xs := by
        funext i
        simp only [ys, hMux, rotBy]
        cases c <;> simp [Nat.mod_eq_of_lt i.isLt]
      rw [ih (2 * step) ys, hys]
      funext i
      simp only [rotBy]
      apply congrArg xs
      apply Fin.ext
      dsimp only
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1
      have hMul : 2 * step * listToNat cs = step * (2 * listToNat cs) := by
        rw [Nat.mul_comm 2 step, Nat.mul_assoc]
      cases c <;> simp [Nat.mul_add, hMul] <;> omega
  intro w ctrls xs
  rw [iterRot_eq_rotBy]
  simpa [barrelRot, Nat.one_mul] using hAux ctrls 1 xs

/-- **General Soundness Meta-Theorem (Engine 3B)**:
    For ALL `k : Nat` (width `2^k`), ANY two certified gate-level mux cells `M1, M2`,
    the recursive unshuffle-rotate-interleave tree rotator (`M1`), the logarithmic barrel
    rotator (`M2`), and the iterated 1-bit rotator are ALL bit-for-bit identical! -/
theorem recTreeRot_eq_barrel_sound (M1 M2 : MuxCell)
    (hM1 : checkMuxCell M1 = true) (hM2 : checkMuxCell M2 = true) :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      recTreeRot M1 k ctrls xs = barrelRot M2 (finToList ctrls) xs ∧
      recTreeRot M1 k ctrls xs = iterRot (listToNat (finToList ctrls)) xs := by
  have hMux1 := checkMuxCell_sound hM1
  have hRec : ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      recTreeRot M1 k ctrls xs = rotBy (listToNat (finToList ctrls)) xs := by
    intro k
    induction k with
    | zero =>
      intro ctrls xs; funext i
      simp only [recTreeRot, finToList, List.finRange_zero, List.map_nil, listToNat, rotBy,
                 Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
    | succ k ih =>
      intro ctrls xs
      have hFinSucc : finToList ctrls = ctrls ⟨0, Nat.zero_lt_succ k⟩ :: finToList (fun j : Fin k => ctrls j.succ) := by
        simp [finToList, List.finRange_succ, List.map_map, Function.comp_def]
      rw [hFinSucc]
      simp only [recTreeRot, listToNat]
      let c0 := ctrls ⟨0, Nat.zero_lt_succ k⟩
      let ys : Fin (2 ^ (k + 1)) → Bool := fun i =>
        M1.eval c0 (xs i) (xs ⟨(i.val + 1) % 2 ^ (k + 1), Nat.mod_lt _ (Nat.two_pow_pos (k + 1))⟩)
      have hys : ys = rotBy (if c0 then 1 else 0) xs := by
        funext i; simp only [ys, hMux1, rotBy]
        cases c0 <;> simp [Nat.mod_eq_of_lt i.isLt]
      let ev : Fin (2 ^ k) → Bool := fun j => ys ⟨2 * j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩
      let od : Fin (2 ^ k) → Bool := fun j => ys ⟨2 * j.val + 1, by have := j.isLt; simp [Nat.pow_succ]; omega⟩
      let q := listToNat (finToList (fun j : Fin k => ctrls j.succ))
      have ihEv : recTreeRot M1 k (fun j => ctrls j.succ) ev = rotBy q ev := ih _ ev
      have ihOd : recTreeRot M1 k (fun j => ctrls j.succ) od = rotBy q od := ih _ od
      funext i
      -- Show both even and odd branches equal `ys ((i + 2*q) % 2^(k+1))`
      have hStep2 : (if i.val % 2 = 0 then
            recTreeRot M1 k (fun j => ctrls j.succ) ev ⟨i.val / 2, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
          else
            recTreeRot M1 k (fun j => ctrls j.succ) od ⟨i.val / 2, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩) =
          rotBy (2 * q) ys i := by
        rw [ihEv, ihOd]
        simp only [rotBy]
        have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by simp [Nat.pow_succ]; omega
        by_cases hEv : i.val % 2 = 0
        · simp only [hEv, ↓reduceIte, ev]
          apply congrArg ys; apply Fin.ext; dsimp only
          have hmul : 2 * ((i.val / 2 + q) % 2 ^ k) = (2 * (i.val / 2 + q)) % (2 * 2 ^ k) :=
            (Nat.mul_mod_mul_left 2 (i.val / 2 + q) (2 ^ k)).symm
          have hSum : 2 * (i.val / 2 + q) = i.val + 2 * q := by omega
          rw [hmul, hSum]
          exact congrArg ((i.val + 2 * q) % ·) hPow.symm
        · simp only [hEv, ↓reduceIte, od]
          apply congrArg ys; apply Fin.ext; dsimp only
          have hmul : 2 * ((i.val / 2 + q) % 2 ^ k) = (2 * (i.val / 2 + q)) % (2 * 2 ^ k) :=
            (Nat.mul_mod_mul_left 2 (i.val / 2 + q) (2 ^ k)).symm
          have hlt : 2 * ((i.val / 2 + q) % 2 ^ k) + 1 < 2 * 2 ^ k := by
            have := Nat.mod_lt (i.val / 2 + q) (Nat.two_pow_pos k); omega
          have h1lt : 1 < 2 * 2 ^ k := by have := Nat.two_pow_pos k; omega
          have hEq : (2 * (i.val / 2 + q) + 1) % (2 * 2 ^ k) = 2 * ((i.val / 2 + q) % 2 ^ k) + 1 := by
            rw [Nat.add_mod, ← hmul, Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt hlt]
          have hSum : 2 * (i.val / 2 + q) + 1 = i.val + 2 * q := by omega
          rw [← hEq, hSum]
          exact congrArg ((i.val + 2 * q) % ·) hPow.symm
      change (if i.val % 2 = 0 then _ else _) = _
      rw [hStep2, hys]
      simp only [rotBy]
      apply congrArg xs; apply Fin.ext; dsimp only
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1
      dsimp only [c0, q]
      omega
  intro k ctrls xs
  have h1 := hRec k ctrls xs
  have h2 := barrelRot_eq_iterRot_sound M2 hM2 (finToList ctrls) xs
  rw [iterRot_eq_rotBy] at h2 ⊢
  exact ⟨h1.trans h2.symm, h1⟩

-- Concrete gate-level MuxCells (SOP, NAND-only, XOR-AND, and broken mutant)
def sopMuxCell : MuxCell :=
  { net := { inW := 3, gates := [.not 0, .and 3 1, .and 0 2, .or 4 5], outs := [6] }
    hIn := rfl, hOut := rfl }

def brokenMuxCell : MuxCell :=
  { net := { inW := 3, gates := [.not 0, .and 3 2, .and 0 1, .or 4 5], outs := [6] } -- swapped d0/d1!
    hIn := rfl, hOut := rfl }

example : checkMuxCell brokenMuxCell = false := by decide

/-- **Certified Infinite Theorem 3.1 (3-Way Recursive Shifter Equivalence)**:
    For ALL `k : Nat` (width `2^k`), the NAND-only recursive unshuffle-rotate-interleave tree
    rotator, the XOR-AND logarithmic barrel rotator, and the iterated 1-bit rotator are identical! -/
theorem three_way_shifter_equiv :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      recTreeRot nandOnlyMuxCell k ctrls xs = barrelRot xorAndMuxCell (finToList ctrls) xs ∧
      recTreeRot nandOnlyMuxCell k ctrls xs = iterRot (listToNat (finToList ctrls)) xs :=
  recTreeRot_eq_barrel_sound nandOnlyMuxCell xorAndMuxCell (by decide) (by decide)

/-- **Certified Infinite Theorem 3.2 (Arbitrary Non-Power-of-Two Width Barrel Rotator)**:
    For ALL `w : Nat` (even prime/odd widths like `w = 3, 5, 7, 13, ...`), SOP barrel rotator
    ≡ NAND-only barrel rotator ≡ iterated 1-bit rotator! -/
theorem arbitrary_width_barrel_equiv :
    ∀ (w : Nat) (ctrls : List Bool) (xs : Fin w → Bool),
      barrelRot sopMuxCell ctrls xs = barrelRot nandOnlyMuxCell ctrls xs ∧
      barrelRot sopMuxCell ctrls xs = iterRot (listToNat ctrls) xs := by
  intro w ctrls xs
  have h1 := barrelRot_eq_iterRot_sound sopMuxCell (by decide) ctrls xs
  have h2 := barrelRot_eq_iterRot_sound nandOnlyMuxCell (by decide) ctrls xs
  exact ⟨h1.trans h2.symm, h1⟩

/-- Bit-address helpers on `Fin (2^k)`: clear bit `b`, set bit `b`, test bit `b`. -/
def bitAt (x b : Nat) : Bool := (x / 2 ^ b) % 2 == 1

def clearBit (x b : Nat) : Nat := x - ((x / 2 ^ b) % 2) * 2 ^ b

def setBit (x b : Nat) : Nat := clearBit x b + 2 ^ b

theorem clearBit_lt {k b x : Nat} (hx : x < 2 ^ k) : clearBit x b < 2 ^ k := by
  unfold clearBit
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hx

theorem setBit_lt {k b x : Nat} (hb : b < k) (hx : x < 2 ^ k) : setBit x b < 2 ^ k := by
  unfold setBit clearBit
  have hPow : 2 ^ b > 0 := Nat.two_pow_pos b
  have hdiv : x = (x / 2 ^ b) * 2 ^ b + x % 2 ^ b := (Nat.div_add_mod' x (2 ^ b)).symm
  have hrem : x % 2 ^ b < 2 ^ b := Nat.mod_lt x hPow
  have hq : x / 2 ^ b < 2 ^ (k - b) := by
    have hsplit : 2 ^ k = 2 ^ (k - b) * 2 ^ b := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hb)]
    rw [hsplit] at hx
    exact (Nat.div_lt_iff_lt_mul hPow).mpr hx
  have hEven : (x / 2 ^ b) - (x / 2 ^ b) % 2 + 1 < 2 ^ (k - b) := by
    have hEvenPow : 2 ^ (k - b) % 2 = 0 := by
      have hk : k - b = (k - b - 1) + 1 := by omega
      rw [hk, Nat.pow_succ]; omega
    have hAux : ∀ q M : Nat, q < M → M % 2 = 0 → q - q % 2 + 1 < M := by
      intro q M _ _; omega
    exact hAux (x / 2 ^ b) (2 ^ (k - b)) hq hEvenPow
  have hsplit : 2 ^ k = 2 ^ (k - b) * 2 ^ b := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hb)]
  have hSub : x - (x / 2 ^ b) % 2 * 2 ^ b + 2 ^ b =
      ((x / 2 ^ b) - (x / 2 ^ b) % 2 + 1) * 2 ^ b + x % 2 ^ b := by
    have hle : (x / 2 ^ b) % 2 ≤ x / 2 ^ b := Nat.mod_le _ _
    have hmul : (x / 2 ^ b - (x / 2 ^ b) % 2) * 2 ^ b =
        (x / 2 ^ b) * 2 ^ b - (x / 2 ^ b) % 2 * 2 ^ b := Nat.sub_mul _ _ _
    have hmul2 : (x / 2 ^ b) % 2 * 2 ^ b ≤ (x / 2 ^ b) * 2 ^ b := Nat.mul_le_mul_right _ hle
    rw [Nat.add_mul, Nat.one_mul, hmul]
    omega
  rw [hSub, hsplit]
  have hle1 : ((x / 2 ^ b) - (x / 2 ^ b) % 2 + 1 + 1) * 2 ^ b ≤ 2 ^ (k - b) * 2 ^ b :=
    Nat.mul_le_mul_right _ hEven
  have hstep : ((x / 2 ^ b) - (x / 2 ^ b) % 2 + 1) * 2 ^ b + 2 ^ b =
      ((x / 2 ^ b) - (x / 2 ^ b) % 2 + 1 + 1) * 2 ^ b := by
    have hAdd1 : ∀ a d : Nat, a * d + d = (a + 1) * d := fun a d => by rw [Nat.add_mul, Nat.one_mul]
    exact hAdd1 _ _
  omega

/-- Apply a 2-wire cell `C c` across pairs of wires differing in bit `b` (`b < k`). -/
def applyBit (C : Cell2) (c : Bool) {k : Nat} (b : Nat) (hb : b < k)
    (xs : Fin (2 ^ k) → Bool) : Fin (2 ^ k) → Bool :=
  fun i =>
    let a := xs ⟨clearBit i.val b, clearBit_lt i.isLt⟩
    let d := xs ⟨setBit i.val b, setBit_lt hb i.isLt⟩
    if bitAt i.val b then (C.eval c a d).2 else (C.eval c a d).1

-- Finite Binary Certificates for Butterfly Engine 4A:

/-- **Finite 4-Wire Interchange Certificate**: checks `horiz(c0) ∘ vert(c1) = vert(c1) ∘ horiz(c0)`
    across all 64 `(c0, c1, x00, x01, x10, x11)` combinations! -/
def checkInterchange2 (C : Cell2) : Bool :=
  [false, true].all fun c0 =>
  [false, true].all fun c1 =>
  [false, true].all fun x00 =>
  [false, true].all fun x01 =>
  [false, true].all fun x10 =>
  [false, true].all fun x11 =>
    let (v00, v10) := C.eval c1 x00 x10
    let (v01, v11) := C.eval c1 x01 x11
    let (vh00, vh01) := C.eval c0 v00 v01
    let (vh10, vh11) := C.eval c0 v10 v11
    let (h00, h01) := C.eval c0 x00 x01
    let (h10, h11) := C.eval c0 x10 x11
    let (hv00, hv10) := C.eval c1 h00 h10
    let (hv01, hv11) := C.eval c1 h01 h11
    (vh00 == hv00) && (vh01 == hv01) && (vh10 == hv10) && (vh11 == hv11)

/-- **Finite 2-Wire Inverse Certificate**: checks `C2 c (C1 c a b) = (a, b)` for all `c, a, b`. -/
def checkInverse2 (C1 C2 : Cell2) : Bool :=
  [false, true].all fun c =>
  [false, true].all fun a =>
  [false, true].all fun b =>
    let (u, v) := C1.eval c a b
    let (a', b') := C2.eval c u v
    (a' == a) && (b' == b)

/-- **Finite 2-Wire Bisimulation / Equivalence Certificate** between two gate netlists `C1, C2`. -/
def checkCell2Equiv (C1 C2 : Cell2) : Bool :=
  [false, true].all fun c =>
  [false, true].all fun a =>
  [false, true].all fun b =>
    let (u1, v1) := C1.eval c a b
    let (u2, v2) := C2.eval c a b
    (u1 == u2) && (v1 == v2)

theorem checkInterchange2_sound {C : Cell2} (h : checkInterchange2 C = true) :
    ∀ c0 c1 x00 x01 x10 x11,
      let (v00, v10) := C.eval c1 x00 x10
      let (v01, v11) := C.eval c1 x01 x11
      let (vh00, vh01) := C.eval c0 v00 v01
      let (vh10, vh11) := C.eval c0 v10 v11
      let (h00, h01) := C.eval c0 x00 x01
      let (h10, h11) := C.eval c0 x10 x11
      let (hv00, hv10) := C.eval c1 h00 h10
      let (hv01, hv11) := C.eval c1 h01 h11
      vh00 = hv00 ∧ vh01 = hv01 ∧ vh10 = hv10 ∧ vh11 = hv11 := by
  intro c0 c1 x00 x01 x10 x11
  have hmem : ∀ b : Bool, b ∈ [false, true] := fun b => by cases b <;> simp
  unfold checkInterchange2 at h
  have h1 := List.all_eq_true.mp h c0 (hmem c0)
  have h2 := List.all_eq_true.mp h1 c1 (hmem c1)
  have h3 := List.all_eq_true.mp h2 x00 (hmem x00)
  have h4 := List.all_eq_true.mp h3 x01 (hmem x01)
  have h5 := List.all_eq_true.mp h4 x10 (hmem x10)
  have h6 := List.all_eq_true.mp h5 x11 (hmem x11)
  simp only [Bool.and_eq_true, beq_iff_eq] at h6
  exact ⟨h6.1.1.1, h6.1.1.2, h6.1.2, h6.2⟩

theorem checkInverse2_sound {C1 C2 : Cell2} (h : checkInverse2 C1 C2 = true) :
    ∀ c a b, C2.eval c (C1.eval c a b).1 (C1.eval c a b).2 = (a, b) := by
  intro c a b
  unfold checkInverse2 at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h
  cases c <;> cases a <;> cases b <;>
    exact Prod.ext (by simp_all) (by simp_all)

theorem checkCell2Equiv_sound {C1 C2 : Cell2} (h : checkCell2Equiv C1 C2 = true) :
    ∀ c a b, C1.eval c a b = C2.eval c a b := by
  intro c a b
  unfold checkCell2Equiv at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h
  cases c <;> cases a <;> cases b <;>
    exact Prod.ext (by simp_all) (by simp_all)

/-- Key Local-to-Global Lemma (abstracted over any 2-wire function `f` satisfying the 4-wire
    Interchange Law, so `simp` never unfolds `GateNet`!): -/
theorem stride_comm_parHalf_fwd_gen (f : Bool → Bool → Bool → Bool × Bool)
    (h4 : ∀ c0 c1 x00 x01 x10 x11,
      let (v00, v10) := f c1 x00 x10
      let (v01, v11) := f c1 x01 x11
      let (vh00, vh01) := f c0 v00 v01
      let (vh10, vh11) := f c0 v10 v11
      let (h00, h01) := f c0 x00 x01
      let (h10, h11) := f c0 x10 x11
      let (hv00, hv10) := f c1 h00 h10
      let (hv01, hv11) := f c1 h01 h11
      vh00 = hv00 ∧ vh01 = hv01 ∧ vh10 = hv10 ∧ vh11 = hv11)
    (fwd : ∀ (k : Nat), (Fin k → Bool) → (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool))
    (hFwd0 : ∀ ctrls xs, fwd 0 ctrls xs = xs)
    (hFwdS : ∀ k ctrls xs, fwd (k + 1) ctrls xs =
      parHalf (fwd k (fun j => ctrls j.succ)) (strideLayer (f (ctrls ⟨0, Nat.zero_lt_succ k⟩)) xs)) :
    ∀ (k : Nat) (cTop : Bool) (ctrls : Fin k → Bool) (xs : Fin (2 ^ (k + 1)) → Bool),
      parHalf (fwd k ctrls) (strideLayer (f cTop) xs) =
      strideLayer (f cTop) (parHalf (fwd k ctrls) xs) := by
  intro k
  induction k with
  | zero =>
    intro cTop ctrls xs; funext i
    simp only [parHalf, hFwd0, strideLayer]
    have hi : i.val = 0 ∨ i.val = 1 := by have := i.isLt; simp at this; omega
    rcases hi with h0 | h1
    · simp only [h0, Nat.pow_zero, Nat.zero_lt_one, ↓reduceDIte]
      have hnot : ¬ (0 + 1 < 1) := by decide
      simp only [hnot, ↓reduceDIte]
    · simp only [h1, Nat.pow_zero, Nat.lt_irrefl, ↓reduceDIte]
      have hlt : 1 - 1 < 1 := by decide
      simp only [hlt, ↓reduceDIte]
  | succ k ih =>
    intro cTop ctrls xs
    let c0 := ctrls ⟨0, Nat.zero_lt_succ k⟩
    let rest : Fin k → Bool := fun j => ctrls j.succ
    have hLayerComm : ∀ (zs : Fin (2 ^ (k + 2)) → Bool),
        parHalf (strideLayer (f c0)) (strideLayer (f cTop) zs) =
        strideLayer (f cTop) (parHalf (strideLayer (f c0)) zs) := by
      intro zs; funext i
      simp only [parHalf, strideLayer]
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by simp [Nat.pow_succ]; omega
      have h4p : 2 ^ (k + 2) = 4 * 2 ^ k := by simp [Nat.pow_succ]; omega
      by_cases hi1 : i.val < 2 ^ (k + 1)
      · simp only [hi1, ↓reduceDIte]
        by_cases hi0 : i.val < 2 ^ k
        · simp only [hi0, ↓reduceDIte]
          have hq01 : i.val + 2 ^ k < 2 ^ (k + 1) := by omega
          have hq10 : i.val + 2 ^ (k + 1) < 2 ^ (k + 2) := by omega
          have hnot : ¬ (i.val + 2 ^ (k + 1) < 2 ^ (k + 1)) := by omega
          have hq10_sub : i.val + 2 ^ (k + 1) - 2 ^ (k + 1) = i.val := by omega
          simp only [hq01, hnot, hq10_sub, hi0, ↓reduceDIte]
          have hEq := (h4 c0 cTop
            (zs ⟨i.val, i.isLt⟩)
            (zs ⟨i.val + 2 ^ k, by omega⟩)
            (zs ⟨i.val + 2 ^ (k + 1), hq10⟩)
            (zs ⟨i.val + 2 ^ k + 2 ^ (k + 1), by omega⟩)).1
          have hIdx1 : 2 ^ (k + 1) + i.val = i.val + 2 ^ (k + 1) := by omega
          have hIdx2 : 2 ^ (k + 1) + (i.val + 2 ^ k) = i.val + 2 ^ k + 2 ^ (k + 1) := by omega
          simpa [hIdx1, hIdx2] using hEq
        · simp only [hi0, ↓reduceDIte]
          have hq00 : i.val - 2 ^ k < 2 ^ (k + 1) := by omega
          have hnot : ¬ (i.val + 2 ^ (k + 1) < 2 ^ (k + 1)) := by omega
          have hsub : i.val + 2 ^ (k + 1) - 2 ^ (k + 1) = i.val := by omega
          simp only [hq00, hnot, hsub, hi0, ↓reduceDIte]
          have hEq := (h4 c0 cTop
            (zs ⟨i.val - 2 ^ k, by omega⟩)
            (zs ⟨i.val, i.isLt⟩)
            (zs ⟨i.val - 2 ^ k + 2 ^ (k + 1), by omega⟩)
            (zs ⟨i.val + 2 ^ (k + 1), by omega⟩)).2.1
          have hIdx1 : 2 ^ (k + 1) + (i.val - 2 ^ k) = i.val - 2 ^ k + 2 ^ (k + 1) := by omega
          have hIdx2 : 2 ^ (k + 1) + i.val = i.val + 2 ^ (k + 1) := by omega
          simpa [hIdx1, hIdx2] using hEq
      · simp only [hi1, ↓reduceDIte]
        have hsubLt : i.val - 2 ^ (k + 1) < 2 ^ (k + 1) := by have := i.isLt; omega
        by_cases hi0 : i.val - 2 ^ (k + 1) < 2 ^ k
        · simp only [hi0, hsubLt, ↓reduceDIte]
          have hnot1 : ¬ (2 ^ (k + 1) + (i.val - 2 ^ (k + 1)) < 2 ^ (k + 1)) := by omega
          have hnot2 : ¬ (2 ^ (k + 1) + (i.val - 2 ^ (k + 1) + 2 ^ k) < 2 ^ (k + 1)) := by omega
          simp only [hnot1, hnot2, ↓reduceDIte]
          have hEq := (h4 c0 cTop
            (zs ⟨i.val - 2 ^ (k + 1), by omega⟩)
            (zs ⟨i.val - 2 ^ (k + 1) + 2 ^ k, by omega⟩)
            (zs ⟨i.val, i.isLt⟩)
            (zs ⟨i.val + 2 ^ k, by omega⟩)).2.2.1
          have h1 : 2 ^ (k + 1) + (i.val - 2 ^ (k + 1)) - 2 ^ (k + 1) = i.val - 2 ^ (k + 1) := by omega
          have h2' : 2 ^ (k + 1) + (i.val - 2 ^ (k + 1)) = i.val := by omega
          have h3 : 2 ^ (k + 1) + (i.val - 2 ^ (k + 1) + 2 ^ k) - 2 ^ (k + 1) = i.val - 2 ^ (k + 1) + 2 ^ k := by omega
          have h4' : 2 ^ (k + 1) + (i.val - 2 ^ (k + 1) + 2 ^ k) = i.val + 2 ^ k := by omega
          have h5 : i.val + 2 ^ k - 2 ^ (k + 1) = i.val - 2 ^ (k + 1) + 2 ^ k := by omega
          simpa [h1, h2', h3, h4', h5] using hEq
        · simp only [hi0, hsubLt, ↓reduceDIte]
          have hnot1 : ¬ (2 ^ (k + 1) + (i.val - 2 ^ (k + 1) - 2 ^ k) < 2 ^ (k + 1)) := by omega
          have hnot2 : ¬ (2 ^ (k + 1) + (i.val - 2 ^ (k + 1)) < 2 ^ (k + 1)) := by omega
          simp only [hnot1, hnot2, ↓reduceDIte]
          have hEq := (h4 c0 cTop
            (zs ⟨i.val - 2 ^ (k + 1) - 2 ^ k, by omega⟩)
            (zs ⟨i.val - 2 ^ (k + 1), by omega⟩)
            (zs ⟨i.val - 2 ^ k, by omega⟩)
            (zs ⟨i.val, i.isLt⟩)).2.2.2
          have h1 : 2 ^ (k + 1) + (i.val - 2 ^ (k + 1) - 2 ^ k) - 2 ^ (k + 1) = i.val - 2 ^ (k + 1) - 2 ^ k := by omega
          have h2' : 2 ^ (k + 1) + (i.val - 2 ^ (k + 1) - 2 ^ k) = i.val - 2 ^ k := by omega
          have h3 : 2 ^ (k + 1) + (i.val - 2 ^ (k + 1)) - 2 ^ (k + 1) = i.val - 2 ^ (k + 1) := by omega
          have h4' : 2 ^ (k + 1) + (i.val - 2 ^ (k + 1)) = i.val := by omega
          have h5 : i.val - 2 ^ k - 2 ^ (k + 1) = i.val - 2 ^ (k + 1) - 2 ^ k := by omega
          simpa [h1, h2', h3, h4', h5] using hEq
    have hParFwd : ∀ (zs : Fin (2 ^ (k + 2)) → Bool),
        parHalf (fwd (k + 1) ctrls) zs =
        parHalf (parHalf (fwd k rest)) (parHalf (strideLayer (f c0)) zs) := by
      intro zs; funext i
      simp only [parHalf, hFwdS, c0, rest]
      by_cases hi : i.val < 2 ^ (k + 1)
      · simp only [hi, ↓reduceDIte]
        by_cases hi0 : i.val < 2 ^ k <;> simp only [hi0, ↓reduceDIte]
        · congr 1; funext j
          have hj : j.val < 2 ^ (k + 1) := by have := j.isLt; simp [Nat.pow_succ]; omega
          simp [hj]
        · congr 1; funext j
          have hj : 2 ^ k + j.val < 2 ^ (k + 1) := by have := j.isLt; simp [Nat.pow_succ]; omega
          simp [hj]
      · simp only [hi, ↓reduceDIte]
        by_cases hi0 : i.val - 2 ^ (k + 1) < 2 ^ k <;> simp only [hi0, ↓reduceDIte]
        · congr 1; funext j
          have hj : ¬ (2 ^ (k + 1) + j.val < 2 ^ (k + 1)) := by omega
          simp [hj]
        · congr 1; funext j
          have hj : ¬ (2 ^ (k + 1) + (2 ^ k + j.val) < 2 ^ (k + 1)) := by omega
          have hsub : 2 ^ (k + 1) + (2 ^ k + j.val) - 2 ^ (k + 1) = 2 ^ k + j.val := by omega
          simp [hj, hsub]
    rw [hParFwd, hLayerComm, hParFwd]
    let ys := parHalf (strideLayer (f c0)) xs
    let q02 : Fin (2 ^ (k + 1)) → Bool := fun j =>
      if h : j.val < 2 ^ k then ys ⟨j.val, by simp [Nat.pow_succ]; omega⟩
      else ys ⟨2 ^ (k + 1) + (j.val - 2 ^ k), by have := j.isLt; simp [Nat.pow_succ] at *; omega⟩
    let q13 : Fin (2 ^ (k + 1)) → Bool := fun j =>
      if h : j.val < 2 ^ k then ys ⟨2 ^ k + j.val, by simp [Nat.pow_succ]; omega⟩
      else ys ⟨2 ^ (k + 1) + 2 ^ k + (j.val - 2 ^ k), by have := j.isLt; simp [Nat.pow_succ] at *; omega⟩
    have ih02 := ih cTop rest q02
    have ih13 := ih cTop rest q13
    -- Outer-only unfolding helpers for `parHalf` and `strideLayer`!
    have hParLt : ∀ {m : Nat} (g : (Fin (2 ^ m) → Bool) → (Fin (2 ^ m) → Bool))
        (zs : Fin (2 ^ (m + 1)) → Bool) (i : Fin (2 ^ (m + 1))) (hi : i.val < 2 ^ m),
        parHalf g zs i = g (fun j => zs ⟨j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) ⟨i.val, hi⟩ := by
      intro m g zs i hi; simp [parHalf, hi]
    have hParGe : ∀ {m : Nat} (g : (Fin (2 ^ m) → Bool) → (Fin (2 ^ m) → Bool))
        (zs : Fin (2 ^ (m + 1)) → Bool) (i : Fin (2 ^ (m + 1))) (hi : ¬ (i.val < 2 ^ m)),
        parHalf g zs i = g (fun j => zs ⟨2 ^ m + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩)
          ⟨i.val - 2 ^ m, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩ := by
      intro m g zs i hi; simp [parHalf, hi]
    have hStrLt : ∀ {m : Nat} (g : Bool → Bool → Bool × Bool) (zs : Fin (2 ^ (m + 1)) → Bool)
        (i : Fin (2 ^ (m + 1))) (hi : i.val < 2 ^ m),
        strideLayer g zs i = (g (zs ⟨i.val, i.isLt⟩) (zs ⟨i.val + 2 ^ m, by simp [Nat.pow_succ]; omega⟩)).1 := by
      intro m g zs i hi; simp [strideLayer, hi]
    have hStrGe : ∀ {m : Nat} (g : Bool → Bool → Bool × Bool) (zs : Fin (2 ^ (m + 1)) → Bool)
        (i : Fin (2 ^ (m + 1))) (hi : ¬ (i.val < 2 ^ m)),
        strideLayer g zs i = (g (zs ⟨i.val - 2 ^ m, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩)
                                (zs ⟨i.val, i.isLt⟩)).2 := by
      intro m g zs i hi; simp [strideLayer, hi]
    have h02_SL_L : (fun j : Fin (2 ^ k) => strideLayer (f cTop) ys ⟨j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) =
                    (fun j : Fin (2 ^ k) => strideLayer (f cTop) q02 ⟨j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) := by
      funext j
      rw [hStrLt (f cTop) ys _ (by have := j.isLt; simp [Nat.pow_succ]; omega), hStrLt (f cTop) q02 _ j.isLt]
      have h1 : ¬ (j.val + 2 ^ k < 2 ^ k) := by omega
      have h2 : j.val + 2 ^ k - 2 ^ k = j.val := by omega
      have h3 : j.val + 2 ^ (k + 1) = 2 ^ (k + 1) + j.val := by omega
      simp only [q02, j.isLt, h1, h2, h3, ↓reduceDIte]
    have h02_SL_R : (fun j : Fin (2 ^ k) => strideLayer (f cTop) ys ⟨2 ^ (k + 1) + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) =
                    (fun j : Fin (2 ^ k) => strideLayer (f cTop) q02 ⟨2 ^ k + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) := by
      funext j
      rw [hStrGe (f cTop) ys _ (by dsimp only; omega), hStrGe (f cTop) q02 _ (by dsimp only; omega)]
      have h1 : ¬ (2 ^ k + j.val < 2 ^ k) := by omega
      have h2 : 2 ^ k + j.val - 2 ^ k = j.val := by omega
      have h3 : 2 ^ (k + 1) + j.val - 2 ^ (k + 1) = j.val := by omega
      simp only [q02, j.isLt, h1, h2, h3, ↓reduceDIte]
    have h02_L : (fun j : Fin (2 ^ k) => ys ⟨j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) =
                 (fun j : Fin (2 ^ k) => q02 ⟨j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) := by
      funext j; simp [q02, j.isLt]
    have h02_R : (fun j : Fin (2 ^ k) => ys ⟨2 ^ (k + 1) + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) =
                 (fun j : Fin (2 ^ k) => q02 ⟨2 ^ k + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) := by
      funext j
      have hnot : ¬ (2 ^ k + j.val < 2 ^ k) := by omega
      have hsub : 2 ^ k + j.val - 2 ^ k = j.val := by omega
      simp only [q02, hnot, hsub, ↓reduceDIte]
    have h13_SL_L : (fun j : Fin (2 ^ k) => strideLayer (f cTop) ys ⟨2 ^ k + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) =
                    (fun j : Fin (2 ^ k) => strideLayer (f cTop) q13 ⟨j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) := by
      funext j
      rw [hStrLt (f cTop) ys _ (by dsimp only; have := j.isLt; simp [Nat.pow_succ]; omega), hStrLt (f cTop) q13 _ j.isLt]
      have h1 : ¬ (j.val + 2 ^ k < 2 ^ k) := by omega
      have h2 : j.val + 2 ^ k - 2 ^ k = j.val := by omega
      have h3 : 2 ^ k + j.val + 2 ^ (k + 1) = 2 ^ (k + 1) + 2 ^ k + j.val := by omega
      simp only [q13, j.isLt, h1, h2, h3, ↓reduceDIte]
    have h13_SL_R : (fun j : Fin (2 ^ k) => strideLayer (f cTop) ys ⟨2 ^ (k + 1) + (2 ^ k + j.val), by have := j.isLt; simp [Nat.pow_succ]; omega⟩) =
                    (fun j : Fin (2 ^ k) => strideLayer (f cTop) q13 ⟨2 ^ k + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) := by
      funext j
      rw [hStrGe (f cTop) ys _ (by dsimp only; omega), hStrGe (f cTop) q13 _ (by dsimp only; omega)]
      have h1 : ¬ (2 ^ k + j.val < 2 ^ k) := by omega
      have h2 : 2 ^ k + j.val - 2 ^ k = j.val := by omega
      have h4' : 2 ^ (k + 1) + (2 ^ k + j.val) = 2 ^ (k + 1) + 2 ^ k + j.val := by omega
      have h5 : 2 ^ (k + 1) + 2 ^ k + j.val - 2 ^ (k + 1) = 2 ^ k + j.val := by omega
      simp only [q13, j.isLt, h1, h2, h4', h5, ↓reduceDIte]
    have h13_L : (fun j : Fin (2 ^ k) => ys ⟨2 ^ k + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) =
                 (fun j : Fin (2 ^ k) => q13 ⟨j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) := by
      funext j; simp [q13, j.isLt]
    have h13_R : (fun j : Fin (2 ^ k) => ys ⟨2 ^ (k + 1) + (2 ^ k + j.val), by have := j.isLt; simp [Nat.pow_succ]; omega⟩) =
                 (fun j : Fin (2 ^ k) => q13 ⟨2 ^ k + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) := by
      funext j
      have hnot : ¬ (2 ^ k + j.val < 2 ^ k) := by omega
      have hsub : 2 ^ k + j.val - 2 ^ k = j.val := by omega
      have h5 : 2 ^ (k + 1) + (2 ^ k + j.val) = 2 ^ (k + 1) + 2 ^ k + j.val := by omega
      simp only [q13, hnot, hsub, h5, ↓reduceDIte]
    funext i
    by_cases hi1 : i.val < 2 ^ (k + 1)
    · by_cases hi0 : i.val < 2 ^ k
      · have hGoal := congrFun ih02 ⟨i.val, by simp [Nat.pow_succ]; omega⟩
        rw [hParLt _ _ _ hi0, hStrLt _ _ _ hi0, hParLt _ _ _ hi0, hParGe _ _ _ (by dsimp only; omega)] at hGoal
        rw [hParLt _ _ _ hi1, hParLt _ _ _ hi0, hStrLt _ _ _ hi1, hParLt _ _ _ hi1, hParLt _ _ _ hi0,
            hParGe _ _ _ (by dsimp only; omega), hParLt _ _ _ (by dsimp only; omega)]
        have hSub : i.val + 2 ^ (k + 1) - 2 ^ (k + 1) = i.val := by omega
        have hSub2 : i.val + 2 ^ k - 2 ^ k = i.val := by omega
        simp only [hSub] at ⊢
        simp only [hSub2] at hGoal
        rw [h02_SL_L, h02_L, h02_R]
        exact hGoal
      · have hGoal := congrFun ih13 ⟨i.val - 2 ^ k, by simp [Nat.pow_succ] at *; omega⟩
        have hlt1 : i.val - 2 ^ k < 2 ^ k := by simp [Nat.pow_succ] at *; omega
        rw [hParLt _ _ _ hlt1, hStrLt _ _ _ hlt1, hParLt _ _ _ hlt1, hParGe _ _ _ (by dsimp only; omega)] at hGoal
        rw [hParLt _ _ _ hi1, hParGe _ _ _ hi0, hStrLt _ _ _ hi1, hParLt _ _ _ hi1, hParGe _ _ _ hi0,
            hParGe _ _ _ (by dsimp only; omega), hParGe _ _ _ (by dsimp only; omega)]
        have hSub : i.val + 2 ^ (k + 1) - 2 ^ (k + 1) = i.val := by omega
        have hSub2 : i.val - 2 ^ k + 2 ^ k - 2 ^ k = i.val - 2 ^ k := by omega
        simp only [hSub] at ⊢
        simp only [hSub2] at hGoal
        rw [h13_SL_L, h13_L, h13_R]
        exact hGoal
    · by_cases hi0 : i.val - 2 ^ (k + 1) < 2 ^ k
      · have hGoal := congrFun ih02 ⟨2 ^ k + (i.val - 2 ^ (k + 1)), by simp [Nat.pow_succ] at *; omega⟩
        rw [hParGe _ _ _ (by dsimp only; omega), hStrGe _ _ _ (by dsimp only; omega),
            hParLt _ _ _ (by dsimp only; omega), hParGe _ _ _ (by dsimp only; omega)] at hGoal
        rw [hParGe _ _ _ hi1, hParLt _ _ _ hi0, hStrGe _ _ _ hi1,
            hParLt _ _ _ (by dsimp only; have := i.isLt; simp [Nat.pow_succ] at *; omega), hParLt _ _ _ hi0,
            hParGe _ _ _ hi1, hParLt _ _ _ hi0]
        have hSub2 : 2 ^ k + (i.val - 2 ^ (k + 1)) - 2 ^ k = i.val - 2 ^ (k + 1) := by omega
        simp only [hSub2] at hGoal
        rw [h02_SL_R, h02_L, h02_R]
        exact hGoal
      · have hGoal := congrFun ih13 ⟨2 ^ k + (i.val - 2 ^ (k + 1) - 2 ^ k), by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
        have hltSub : i.val - 2 ^ (k + 1) - 2 ^ k < 2 ^ k := by have := i.isLt; simp [Nat.pow_succ] at *; omega
        rw [hParGe _ _ _ (by dsimp only; omega), hStrGe _ _ _ (by dsimp only; omega),
            hParLt _ _ _ (by dsimp only; omega), hParGe _ _ _ (by dsimp only; omega)] at hGoal
        rw [hParGe _ _ _ hi1, hParGe _ _ _ hi0, hStrGe _ _ _ hi1,
            hParLt _ _ _ (by dsimp only; have := i.isLt; simp [Nat.pow_succ] at *; omega), hParGe _ _ _ hi0,
            hParGe _ _ _ hi1, hParGe _ _ _ hi0]
        have hSub2 : 2 ^ k + (i.val - 2 ^ (k + 1) - 2 ^ k) - 2 ^ k = i.val - 2 ^ (k + 1) - 2 ^ k := by omega
        simp only [hSub2] at hGoal
        rw [h13_SL_R, h13_L, h13_R]
        exact hGoal

theorem stride_comm_parHalf_fwd {C : Cell2} (hIC : checkInterchange2 C = true) :
    ∀ (k : Nat) (cTop : Bool) (ctrls : Fin k → Bool) (xs : Fin (2 ^ (k + 1)) → Bool),
      parHalf (fwdButterfly C k ctrls) (strideLayer (C.eval cTop) xs) =
      strideLayer (C.eval cTop) (parHalf (fwdButterfly C k ctrls) xs) :=
  stride_comm_parHalf_fwd_gen C.eval (checkInterchange2_sound hIC) (fwdButterfly C)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

/-- **General Soundness Meta-Theorem (Engine 4A-1: 4-Wire Interchange $\implies$ All-$k$ Stage Commutation)**:
    If a concrete 2-wire gate cell `C` passes the finite 64-case 4-Wire Interchange check, then
    `fwdButterfly C k = bwdButterfly C k` for ALL `k : Nat` (width `2^k`) and ALL controls! -/
theorem butterfly_interchange_sound (C : Cell2) (hIC : checkInterchange2 C = true) :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      fwdButterfly C k ctrls xs = bwdButterfly C k ctrls xs := by
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro ctrls xs
    change parHalf (fwdButterfly C k (fun j => ctrls j.succ))
             (strideLayer (C.eval (ctrls ⟨0, Nat.zero_lt_succ k⟩)) xs) =
           strideLayer (C.eval (ctrls ⟨0, Nat.zero_lt_succ k⟩))
             (parHalf (bwdButterfly C k (fun j => ctrls j.succ)) xs)
    rw [stride_comm_parHalf_fwd hIC]
    have hEq : fwdButterfly C k (fun j => ctrls j.succ) = bwdButterfly C k (fun j => ctrls j.succ) := by
      funext zs; exact ih _ zs
    rw [hEq]

/-- **General Soundness Meta-Theorem (Engine 4A-2: 2-Wire Inverse $\implies$ All-$k$ Exact Butterfly Inversion)**:
    Requires ONLY the 8-case 2-wire inverse certificate (NO 4-Wire Interchange needed!
    Works even for the 8 non-commuting bijective cells like `(a^b, ~b)`!). -/
theorem butterfly_bwd_inverse_sound (C1 C2 : Cell2) (hInv : checkInverse2 C1 C2 = true) :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      bwdButterfly C2 k ctrls (fwdButterfly C1 k ctrls xs) = xs := by
  have h2 := checkInverse2_sound hInv
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro ctrls xs
    change strideLayer (C2.eval (ctrls ⟨0, Nat.zero_lt_succ k⟩))
             (parHalf (bwdButterfly C2 k (fun j => ctrls j.succ))
               (parHalf (fwdButterfly C1 k (fun j => ctrls j.succ))
                 (strideLayer (C1.eval (ctrls ⟨0, Nat.zero_lt_succ k⟩)) xs))) = xs
    have hParCancel : ∀ (zs : Fin (2 ^ (k + 1)) → Bool),
        parHalf (bwdButterfly C2 k (fun j => ctrls j.succ))
          (parHalf (fwdButterfly C1 k (fun j => ctrls j.succ)) zs) = zs := by
      intro zs; funext i
      simp only [parHalf]
      by_cases hi : i.val < 2 ^ k
      · simp only [hi, ↓reduceDIte]
        have hL : (fun j : Fin (2 ^ k) =>
            parHalf (fwdButterfly C1 k (fun m => ctrls m.succ)) zs
              ⟨j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) =
            fwdButterfly C1 k (fun m => ctrls m.succ)
              (fun m => zs ⟨m.val, by have := m.isLt; simp [Nat.pow_succ]; omega⟩) := by
          funext j; simp [parHalf, j.isLt]
        change bwdButterfly C2 k (fun m => ctrls m.succ)
          (fun j : Fin (2 ^ k) => parHalf (fwdButterfly C1 k (fun m => ctrls m.succ)) zs
            ⟨j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) ⟨i.val, hi⟩ = zs i
        rw [hL, ih]
      · simp only [hi, ↓reduceDIte]
        have hR : (fun j : Fin (2 ^ k) =>
            parHalf (fwdButterfly C1 k (fun m => ctrls m.succ)) zs
              ⟨2 ^ k + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩) =
            fwdButterfly C1 k (fun m => ctrls m.succ)
              (fun m => zs ⟨2 ^ k + m.val, by have := m.isLt; simp [Nat.pow_succ]; omega⟩) := by
          funext j
          have hnot : ¬ (2 ^ k + j.val < 2 ^ k) := by omega
          have hsub : 2 ^ k + j.val - 2 ^ k = j.val := by omega
          simp [parHalf, hnot, hsub]
        change bwdButterfly C2 k (fun m => ctrls m.succ)
          (fun j : Fin (2 ^ k) => parHalf (fwdButterfly C1 k (fun m => ctrls m.succ)) zs
            ⟨2 ^ k + j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩)
          ⟨i.val - 2 ^ k, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩ = zs i
        rw [hR, ih]
        congr 1; exact Fin.ext (by dsimp only; omega)
    rw [hParCancel]
    funext i
    simp only [strideLayer]
    by_cases hi : i.val < 2 ^ k
    · simp only [hi, ↓reduceDIte]
      have hnot : ¬ (i.val + 2 ^ k < 2 ^ k) := by omega
      have hsub : i.val + 2 ^ k - 2 ^ k = i.val := by omega
      simp only [hnot, hsub, ↓reduceDIte]
      exact congrArg Prod.fst (h2 _ _ _)
    · simp only [hi, ↓reduceDIte]
      have hlt : i.val - 2 ^ k < 2 ^ k := by have := i.isLt; simp [Nat.pow_succ] at *; omega
      have hadd : i.val - 2 ^ k + 2 ^ k = i.val := by omega
      simp only [hlt, hadd, ↓reduceDIte]
      exact congrArg Prod.snd (h2 _ _ _)

/-- **General Soundness Meta-Theorem (Engine 4A-3: Interchange + Inverse $\implies$ Forward-Forward Cancellation / Self-Inversion)**: -/
theorem butterfly_fwd_inverse_sound (C1 C2 : Cell2)
    (hIC : checkInterchange2 C2 = true) (hInv : checkInverse2 C1 C2 = true) :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      fwdButterfly C2 k ctrls (fwdButterfly C1 k ctrls xs) = xs := by
  intro k ctrls xs
  rw [butterfly_interchange_sound C2 hIC]
  exact butterfly_bwd_inverse_sound C1 C2 hInv k ctrls xs

/-- Top-level helpers for `omega_eq_fwdButterfly_sound` (unfoldable by `simp`). -/
def applyBitsDown (C : Cell2) {k : Nat} :
    (m : Nat) → (hm : m ≤ k) → List Bool → (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool)
  | 0, _, _, xs => xs
  | _, _, [], xs => xs
  | m + 1, hm, c :: cs, xs =>
    applyBitsDown C m (by omega) cs (applyBit C c m (by omega) xs)

def rotRightPow (k : Nat) : Nat → Fin (2 ^ k) → Fin (2 ^ k)
  | 0, i     => i
  | r + 1, i => rotRightIdx k (rotRightPow k r i)

/-- **General Soundness Meta-Theorem (Engine 4A-4: Pease / Omega Constant-Geometry ≡ Forward Butterfly)**:
    For ANY concrete 2-wire gate cell `C : Cell2` (ZERO algebraic hypotheses!),
    the `k`-stage constant-geometry Omega shuffle-exchange network equals `fwdButterfly C k`
    for ALL `k : Nat` (width `2^k`)! -/
theorem omega_eq_fwdButterfly_sound (C : Cell2) :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      omegaNet C k ctrls xs = fwdButterfly C k ctrls xs := by
  have hApplyBitLow : ∀ {k : Nat} (c : Bool) (b : Nat) (hb : b < k) (xs : Fin (2 ^ (k + 1)) → Bool),
      applyBit C c b (by omega) xs = parHalf (applyBit C c b hb) xs := by
    intro k c b hb xs; funext i
    simp only [applyBit, parHalf]
    have hDivMod : ∀ x, x < 2 ^ k →
        clearBit (2 ^ k + x) b = 2 ^ k + clearBit x b ∧
        setBit (2 ^ k + x) b = 2 ^ k + setBit x b ∧
        bitAt (2 ^ k + x) b = bitAt x b := by
      intro x _
      have hsplit : 2 ^ k = 2 ^ b * 2 ^ (k - b) := by
        rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hb)]
      have hEven : 2 ^ (k - b) % 2 = 0 := by
        have hk : k - b = (k - b - 1) + 1 := by omega
        rw [hk, Nat.pow_succ]; omega
      have hq : (2 ^ k + x) / 2 ^ b = 2 ^ (k - b) + x / 2 ^ b := by
        rw [hsplit, Nat.mul_add_div (Nat.two_pow_pos b)]
      have hmod2 : ((2 ^ k + x) / 2 ^ b) % 2 = (x / 2 ^ b) % 2 := by
        rw [hq]; omega
      refine ⟨?_, ?_, ?_⟩
      · unfold clearBit; rw [hmod2]
        have hle : (x / 2 ^ b) % 2 * 2 ^ b ≤ x := by
          have := Nat.mod_le (x / 2 ^ b) 2
          have := Nat.mul_le_mul_right (2 ^ b) this
          have := Nat.div_add_mod' x (2 ^ b)
          omega
        omega
      · unfold setBit clearBit; rw [hmod2]
        have hle : (x / 2 ^ b) % 2 * 2 ^ b ≤ x := by
          have := Nat.mod_le (x / 2 ^ b) 2
          have := Nat.mul_le_mul_right (2 ^ b) this
          have := Nat.div_add_mod' x (2 ^ b)
          omega
        omega
      · unfold bitAt; rw [hmod2]
    by_cases hi : i.val < 2 ^ k
    · simp only [hi, ↓reduceDIte]
    · simp only [hi, ↓reduceDIte]
      have hsub : i.val - 2 ^ k < 2 ^ k := by have := i.isLt; simp [Nat.pow_succ] at *; omega
      have hEq := hDivMod (i.val - 2 ^ k) hsub
      have hadd : 2 ^ k + (i.val - 2 ^ k) = i.val := by omega
      rw [hadd] at hEq
      rcases hEq with ⟨hCl, hSet, hBit⟩
      simp only [hCl, hSet, hBit]
  have hApplyBitTop : ∀ {k : Nat} (c : Bool) (xs : Fin (2 ^ (k + 1)) → Bool),
      applyBit C c k (Nat.lt_succ_self k) xs = strideLayer (C.eval c) xs := by
    intro k c xs; funext i
    simp only [applyBit, strideLayer, bitAt, clearBit, setBit]
    by_cases hi : i.val < 2 ^ k
    · have hdiv : i.val / 2 ^ k = 0 := Nat.div_eq_of_lt hi
      simp only [hi, hdiv, Nat.zero_mod, Nat.zero_mul, Nat.sub_zero, ↓reduceDIte]
      rfl
    · have hiLt : i.val < 2 * 2 ^ k := by have := i.isLt; simp [Nat.pow_succ] at this; omega
      have hdiv : i.val / 2 ^ k = 1 := by
        have hge : i.val / 2 ^ k ≥ 1 := (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mpr (by omega)
        have hlt : i.val / 2 ^ k < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr (by omega)
        omega
      simp only [hi, hdiv, Nat.one_mod, Nat.one_mul, ↓reduceDIte]
      have hadd : i.val - 2 ^ k + 2 ^ k = i.val := by omega
      simp only [hadd, beq_self_eq_true, ↓reduceIte]
  have hParApplyDown : ∀ {k : Nat} (m : Nat) (hm : m ≤ k) (cs : List Bool) (xs : Fin (2 ^ (k + 1)) → Bool),
      applyBitsDown C m (by omega) cs xs = parHalf (applyBitsDown C m hm cs) xs := by
    intro k m
    induction m with
    | zero =>
      intro _ cs xs; funext i
      simp only [applyBitsDown, parHalf]
      by_cases hi : i.val < 2 ^ k
      · simp [hi]
      · simp only [hi, ↓reduceDIte]; congr 1; exact Fin.ext (by dsimp only; omega)
    | succ m ih =>
      intro hm cs xs
      cases cs with
      | nil =>
        funext i; simp only [applyBitsDown, parHalf]
        by_cases hi : i.val < 2 ^ k
        · simp [hi]
        · simp only [hi, ↓reduceDIte]; congr 1; exact Fin.ext (by dsimp only; omega)
      | cons c rest =>
        simp only [applyBitsDown]
        rw [ih (by omega) rest, hApplyBitLow c m (by omega) xs]
        funext i; simp only [parHalf]
        by_cases hi : i.val < 2 ^ k
        · simp only [hi, ↓reduceDIte]
          congr 1; funext j; simp [j.isLt]
        · simp only [hi, ↓reduceDIte]
          congr 1; funext j
          have hnot : ¬ (2 ^ k + j.val < 2 ^ k) := by omega
          have hsub : 2 ^ k + j.val - 2 ^ k = j.val := by omega
          simp [hnot, hsub]
  have hFwdEqDown : ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      fwdButterfly C k ctrls xs = applyBitsDown C k (Nat.le_refl k) (finToList ctrls) xs := by
    intro k
    induction k with
    | zero => intro _ _; rfl
    | succ k ih =>
      intro ctrls xs
      have hFinSucc : finToList ctrls = ctrls ⟨0, Nat.zero_lt_succ k⟩ :: finToList (fun j : Fin k => ctrls j.succ) := by
        simp [finToList, List.finRange_succ, List.map_map, Function.comp_def]
      rw [hFinSucc]
      simp only [applyBitsDown, hApplyBitTop]
      rw [hParApplyDown k (Nat.le_refl k)]
      change parHalf (fwdButterfly C k (fun j => ctrls j.succ)) _ = _
      have hFun : fwdButterfly C k (fun j => ctrls j.succ) =
                  applyBitsDown C k (Nat.le_refl k) (finToList (fun j => ctrls j.succ)) := by
        funext zs; exact ih _ zs
      rw [hFun]
  have hRotPowVal : ∀ {k : Nat} (r : Nat) (hr : r ≤ k + 1) (i : Fin (2 ^ (k + 1))),
      (rotRightPow (k + 1) r i).val = i.val / 2 ^ r + (i.val % 2 ^ r) * 2 ^ (k + 1 - r) := by
    intro k r
    induction r with
    | zero =>
      intro _ i
      simp [rotRightPow, Nat.mod_one]
    | succ r ih =>
      intro hr i
      simp only [rotRightPow, rotRightIdx]
      rw [ih (by omega) i]
      have hkr : k + 1 - r = (k - r) + 1 := by omega
      have hPow2 : 2 ^ (k + 1 - r) = 2 * 2 ^ (k - r) := by rw [hkr, Nat.pow_succ]; omega
      have hDiv : (i.val / 2 ^ r + (i.val % 2 ^ r) * 2 ^ (k + 1 - r)) / 2 =
                  i.val / 2 ^ (r + 1) + (i.val % 2 ^ r) * 2 ^ (k - r) := by
        rw [hPow2]
        have h1 : (i.val % 2 ^ r) * (2 * 2 ^ (k - r)) = ((i.val % 2 ^ r) * 2 ^ (k - r)) * 2 := by
          rw [Nat.mul_left_comm, Nat.mul_comm 2]
        rw [h1, Nat.add_mul_div_right _ _ (by omega : 0 < 2), Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      have hMod : (i.val / 2 ^ r + (i.val % 2 ^ r) * 2 ^ (k + 1 - r)) % 2 = (i.val / 2 ^ r) % 2 := by
        rw [hPow2]
        have h1 : (i.val % 2 ^ r) * (2 * 2 ^ (k - r)) = ((i.val % 2 ^ r) * 2 ^ (k - r)) * 2 := by
          rw [Nat.mul_left_comm, Nat.mul_comm 2]
        rw [h1, Nat.add_mul_mod_self_right]
      rw [hDiv, hMod]
      have hModSucc : i.val % 2 ^ (r + 1) = i.val % 2 ^ r + ((i.val / 2 ^ r) % 2) * 2 ^ r := by
        have hdivmod := Nat.div_add_mod' i.val (2 ^ r)
        have hPowS : 2 ^ (r + 1) = 2 ^ r * 2 := Nat.pow_succ _ _
        have hExp : i.val = (i.val / 2 ^ r / 2) * 2 ^ (r + 1) + (i.val % 2 ^ r + (i.val / 2 ^ r % 2) * 2 ^ r) := by
          rw [hPowS]
          have hA : (i.val / 2 ^ r) * 2 ^ r = (i.val / 2 ^ r / 2 * 2 + i.val / 2 ^ r % 2) * 2 ^ r := by
            congr 1; omega
          rw [Nat.add_mul] at hA
          have hassoc : i.val / 2 ^ r / 2 * 2 * 2 ^ r = i.val / 2 ^ r / 2 * (2 ^ r * 2) := by
            rw [Nat.mul_assoc, Nat.mul_comm 2 (2 ^ r)]
          omega
        have hlt : i.val % 2 ^ r + (i.val / 2 ^ r % 2) * 2 ^ r < 2 ^ (r + 1) := by
          have := Nat.mod_lt i.val (Nat.two_pow_pos r)
          have hm : i.val / 2 ^ r % 2 = 0 ∨ i.val / 2 ^ r % 2 = 1 := by omega
          rcases hm with h | h <;> rw [hPowS] <;> simp [h] <;> omega
        have hStep : ((i.val / 2 ^ r / 2) * 2 ^ (r + 1) + (i.val % 2 ^ r + (i.val / 2 ^ r % 2) * 2 ^ r)) % 2 ^ (r + 1) =
                     i.val % 2 ^ r + (i.val / 2 ^ r % 2) * 2 ^ r := by
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hlt]
        rw [← hExp] at hStep
        exact hStep
      rw [hModSucc, Nat.add_mul]
      have hExpPow : 2 ^ r * 2 ^ (k + 1 - (r + 1)) = 2 ^ k := by
        rw [← Nat.pow_add]; congr 1; omega
      have hSub : k + 1 - (r + 1) = k - r := by omega
      rw [hSub, Nat.mul_assoc, ← hSub, hExpPow, hSub]
      omega
  -- Hence `rotRightPow (k+1) (k+1) i = i`!
  have hRotFull : ∀ {k : Nat} (i : Fin (2 ^ (k + 1))), rotRightPow (k + 1) (k + 1) i = i := by
    intro k i
    apply Fin.ext
    rw [hRotPowVal (k + 1) (Nat.le_refl _) i]
    have hdiv : i.val / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt i.isLt
    have hmod : i.val % 2 ^ (k + 1) = i.val := Nat.mod_eq_of_lt i.isLt
    simp [hdiv, hmod]
  -- Now prove single-stage conjugation:
  -- `omegaStage C c (fun i => xs (rotRightPow (k+1) r i)) =
  --    fun i => applyBit C c (k - r) _ xs (rotRightPow (k+1) (r + 1) i)` for `r ≤ k`!
  have hStageConj : ∀ {k : Nat} (r : Nat) (hr : r ≤ k) (c : Bool) (xs : Fin (2 ^ (k + 1)) → Bool),
      omegaStage C c (fun i => xs (rotRightPow (k + 1) r i)) =
      fun i => applyBit C c (k - r) (by omega) xs (rotRightPow (k + 1) (r + 1) i) := by
    intro k r hr c xs; funext i
    simp only [omegaStage, applyPairs, shuffle, applyBit]
    -- Let y = rotRightPow (k+1) (r+1) i, and check:
    --   rotRightPow r (rotRightIdx (2*(i/2)))   = clearBit y (k - r)
    --   rotRightPow r (rotRightIdx (2*(i/2)+1)) = setBit y (k - r)
    --   (i % 2 = 0) ↔ (bitAt y (k - r) = false)
    have hRotComm : ∀ (t : Nat) (j : Fin (2 ^ (k + 1))),
        rotRightPow (k + 1) t (rotRightIdx (k + 1) j) = rotRightPow (k + 1) (t + 1) j := by
      intro t
      induction t with
      | zero => intro _; rfl
      | succ t' iht => intro j; exact congrArg (rotRightIdx (k + 1)) (iht j)
    let i0 : Fin (2 ^ (k + 1)) := ⟨(i.val / 2) * 2, by have := i.isLt; omega⟩
    let i1 : Fin (2 ^ (k + 1)) := ⟨(i.val / 2) * 2 + 1, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
    rw [hRotComm r i0, hRotComm r i1]
    let y := (rotRightPow (k + 1) (r + 1) i).val
    have hyVal : y = i.val / 2 ^ (r + 1) + (i.val % 2 ^ (r + 1)) * 2 ^ (k - r) := by
      simpa [y, Nat.add_sub_add_right] using hRotPowVal (r + 1) (by omega) i
    have hy0Val : (rotRightPow (k + 1) (r + 1) i0).val =
        i0.val / 2 ^ (r + 1) + (i0.val % 2 ^ (r + 1)) * 2 ^ (k - r) := by
      simpa [Nat.add_sub_add_right] using hRotPowVal (r + 1) (by omega) i0
    have hy1Val : (rotRightPow (k + 1) (r + 1) i1).val =
        i1.val / 2 ^ (r + 1) + (i1.val % 2 ^ (r + 1)) * 2 ^ (k - r) := by
      simpa [Nat.add_sub_add_right] using hRotPowVal (r + 1) (by omega) i1
    -- Notice: i0 = i - i%2, i1 = i0 + 1; since r+1 ≥ 1, 2^(r+1) is even!
    have hPowEven : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ]; omega
    have hi0Div : i0.val / 2 ^ (r + 1) = i.val / 2 ^ (r + 1) := by
      rw [hPowEven, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      have : i0.val / 2 = i.val / 2 := by simp [i0]
      rw [this]
    have hi1Div : i1.val / 2 ^ (r + 1) = i.val / 2 ^ (r + 1) := by
      rw [hPowEven, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      have : i1.val / 2 = i.val / 2 := by simp [i1]; omega
      rw [this]
    have hi0Mod : i0.val % 2 ^ (r + 1) = i.val % 2 ^ (r + 1) - i.val % 2 := by
      have h1 := Nat.div_add_mod' i.val (2 ^ (r + 1))
      have h2 := Nat.div_add_mod' i0.val (2 ^ (r + 1))
      have h3 : i0.val = i.val - i.val % 2 := by simp [i0]; omega
      rw [hi0Div] at h2
      have hge : i.val % 2 ≤ i.val % 2 ^ (r + 1) := by
        have : i.val % 2 = (i.val % 2 ^ (r + 1)) % 2 := by
          rw [hPowEven, Nat.mod_mul_right_mod]
        omega
      omega
    have hi1Mod : i1.val % 2 ^ (r + 1) = i0.val % 2 ^ (r + 1) + 1 := by
      have h1 := Nat.div_add_mod' i0.val (2 ^ (r + 1))
      have h2 := Nat.div_add_mod' i1.val (2 ^ (r + 1))
      rw [hi0Div] at h1; rw [hi1Div] at h2
      have h3 : i1.val = i0.val + 1 := rfl
      omega
    -- And `y / 2^(k - r) = i % 2^(r + 1)` because `i / 2^(r + 1) < 2^(k - r)`!
    have hqLt : i.val / 2 ^ (r + 1) < 2 ^ (k - r) := by
      have hsplit : 2 ^ (k + 1) = 2 ^ (k - r) * 2 ^ (r + 1) := by
        rw [← Nat.pow_add]; congr 1; omega
      have hiLt : i.val < 2 ^ (k - r) * 2 ^ (r + 1) := hsplit ▸ i.isLt
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (r + 1))).mpr hiLt
    have hyDiv : y / 2 ^ (k - r) = i.val % 2 ^ (r + 1) := by
      rw [hyVal, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (k - r)), Nat.div_eq_of_lt hqLt, Nat.zero_add]
    have hyBitMod : (y / 2 ^ (k - r)) % 2 = i.val % 2 := by
      rw [hyDiv, hPowEven, Nat.mod_mul_right_mod]
    have hClEq : clearBit y (k - r) = (rotRightPow (k + 1) (r + 1) i0).val := by
      unfold clearBit
      rw [hyBitMod, hyVal, hy0Val, hi0Div, hi0Mod, Nat.sub_mul]
      have hge : i.val % 2 * 2 ^ (k - r) ≤ i.val % 2 ^ (r + 1) * 2 ^ (k - r) := by
        apply Nat.mul_le_mul_right
        have : i.val % 2 = (i.val % 2 ^ (r + 1)) % 2 := by rw [hPowEven, Nat.mod_mul_right_mod]
        omega
      exact Nat.add_sub_assoc hge _
    have hSetEq : setBit y (k - r) = (rotRightPow (k + 1) (r + 1) i1).val := by
      unfold setBit
      rw [hClEq, hy0Val, hy1Val, hi0Div, hi1Div, hi1Mod, Nat.add_mul, Nat.one_mul]
      omega
    have hBitIff : bitAt y (k - r) = !(i.val % 2 == 0) := by
      unfold bitAt; rw [hyBitMod]
      have hm : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
      rcases hm with h | h <;> simp [h]
    have hFinCl : (⟨clearBit y (k - r), clearBit_lt (rotRightPow (k + 1) (r + 1) i).isLt⟩ : Fin (2 ^ (k + 1))) =
                  rotRightPow (k + 1) (r + 1) i0 := Fin.ext hClEq
    have hFinSet : (⟨setBit y (k - r), setBit_lt (by omega) (rotRightPow (k + 1) (r + 1) i).isLt⟩ : Fin (2 ^ (k + 1))) =
                   rotRightPow (k + 1) (r + 1) i1 := Fin.ext hSetEq
    rw [hFinCl, hFinSet, hBitIff]
    by_cases hEv : i.val % 2 = 0 <;> simp [hEv]
  -- Now finish by induction on remaining stages!
  intro k ctrls xs
  cases k with
  | zero => simp [omegaNet, omegaRun, finToList, List.finRange_zero, fwdButterfly]
  | succ k =>
    rw [hFwdEqDown (k + 1) ctrls xs]
    unfold omegaNet
    have hRun : ∀ (m : Nat) (hm : m ≤ k + 1) (cs : List Bool) (hlen : cs.length = m)
        (zs : Fin (2 ^ (k + 1)) → Bool),
        omegaRun C cs (fun i => zs (rotRightPow (k + 1) (k + 1 - m) i)) =
        fun i => applyBitsDown C m hm cs zs (rotRightPow (k + 1) (k + 1) i) := by
      intro m
      induction m with
      | zero =>
        intro hm cs hlen zs
        cases cs with
        | nil => simp [omegaRun, applyBitsDown]
        | cons _ _ => simp at hlen
      | succ m ih =>
        intro hm cs hlen zs
        cases cs with
        | nil => simp at hlen
        | cons c rest =>
          simp only [omegaRun, applyBitsDown]
          have hr : k + 1 - (m + 1) ≤ k := by omega
          rw [hStageConj (k + 1 - (m + 1)) hr c zs]
          have hSub1 : k - (k + 1 - (m + 1)) = m := by omega
          have hSub2 : k + 1 - (m + 1) + 1 = k + 1 - m := by omega
          have hEq : (fun i => applyBit C c (k - (k + 1 - (m + 1))) (by omega) zs
                        (rotRightPow (k + 1) (k + 1 - (m + 1) + 1) i)) =
                     (fun i => applyBit C c m (by omega) zs (rotRightPow (k + 1) (k + 1 - m) i)) := by
            have hBitEq : ∀ (a b : Nat) (ha : a < k + 1) (hb : b < k + 1), a = b →
                applyBit C c a ha zs = applyBit C c b hb zs := by
              intro a b _ _ h; subst h; rfl
            funext i; rw [hSub2, hBitEq _ _ _ _ hSub1]
          rw [hEq]
          exact ih (by omega) rest (by simp at hlen; omega) (applyBit C c m (by omega) zs)
    have hFull := hRun (k + 1) (Nat.le_refl _) (finToList ctrls) (by simp [finToList]) xs
    have h0 : k + 1 - (k + 1) = 0 := Nat.sub_self _
    rw [h0] at hFull
    change omegaRun C (finToList ctrls) xs =
      fun i => applyBitsDown C (k + 1) (Nat.le_refl _) (finToList ctrls) xs (rotRightPow (k + 1) (k + 1) i) at hFull
    rw [hFull]
    funext i
    rw [hRotFull i]

-- ============================================================================
-- ENGINE 4B: BATCHER BITONIC SORT ≡ BATCHER ODD-EVEN MERGESORT ≡ THRESHOLD SORT
--            + KNUTH 0–1 PRINCIPLE LIFTING TO ARBITRARY TOTAL ORDERS
-- ============================================================================

/-- Finite 2-wire Boolean comparator certificate: verifies `C.eval false a b = (a && b, a || b)`. -/
def checkComparatorCell (C : Cell2) : Bool :=
  [false, true].all fun a =>
  [false, true].all fun b =>
    let (lo, hi) := C.eval false a b
    (lo == (a && b)) && (hi == (a || b))

theorem checkComparatorCell_sound {C : Cell2} (h : checkComparatorCell C = true) :
    ∀ a b, C.eval false a b = (a && b, a || b) := by
  intro a b
  unfold checkComparatorCell at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h
  cases a <;> cases b <;> exact Prod.ext (by simp_all) (by simp_all)

/-- A Boolean vector `xs` is sorted with `z` zeros iff `∀ i, xs i = decide (z ≤ i.val)`. -/
def IsSortedWith {n : Nat} (z : Nat) (xs : Fin n → Bool) : Prop :=
  z ≤ n ∧ ∀ i : Fin n, xs i = decide (z ≤ i.val)

theorem countFalse_of_isSortedWith {n z : Nat} {xs : Fin n → Bool}
    (h : IsSortedWith z xs) : countFalse xs = z := by
  rcases h with ⟨hz, hxs⟩
  unfold countFalse
  have hGen : ∀ (m : Nat) (hm : m ≤ n),
      ((List.finRange m).filter (fun i => !(decide (z ≤ i.val)))).length = min z m := by
    intro m
    induction m with
    | zero => intro _; simp [List.finRange_zero]
    | succ m ih =>
      intro hm
      rw [List.finRange_succ_last, List.filter_append, List.length_append]
      have hMap : (List.map Fin.castSucc (List.finRange m)).filter (fun i : Fin (m + 1) => !(decide (z ≤ i.val))) =
                  ((List.finRange m).filter (fun i : Fin m => !(decide (z ≤ i.val)))).map Fin.castSucc := by
        rw [List.filter_map]; rfl
      rw [hMap, List.length_map, ih (by omega)]
      by_cases hzm : z ≤ m
      · simp only [List.filter_cons, List.filter_nil, Fin.last, hzm, decide_true, Bool.not_true,
                   Bool.false_eq_true, ↓reduceIte, List.length_nil]
        omega
      · simp only [List.filter_cons, List.filter_nil, Fin.last, hzm, decide_false, Bool.not_false,
                   ↓reduceIte, List.length_cons, List.length_nil]
        omega
  have hFilt : (List.finRange n).filter (fun i => !(xs i)) =
               (List.finRange n).filter (fun i => !(decide (z ≤ i.val))) := by
    congr 1; funext i; rw [hxs i]
  rw [hFilt, hGen n (Nat.le_refl n)]
  omega

theorem isSortedWith_eq_threshold {n z : Nat} {xs : Fin n → Bool}
    (h : IsSortedWith z xs) : xs = thresholdSort xs := by
  have hc := countFalse_of_isSortedWith h
  funext i
  rw [h.2 i, thresholdSort, hc]

/-- Count of `false`s is preserved by `strideLayer` of `(a && b, a || b)`! -/
theorem countFalse_split {k : Nat} (xs : Fin (2 ^ (k + 1)) → Bool) :
    countFalse xs =
      countFalse (fun i : Fin (2 ^ k) => xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) +
      countFalse (fun i : Fin (2 ^ k) => xs ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) := by
  -- Prove for general `a + b` via `List.finRange` induction on `b`!
  have hStep : ∀ (m : Nat) (g : Fin (m + 1) → Bool),
      countFalse g = countFalse (fun i : Fin m => g i.castSucc) + (if !(g (Fin.last m)) then 1 else 0) := by
    intro m g
    unfold countFalse
    rw [List.finRange_succ_last, List.filter_append, List.length_append, List.filter_map, List.length_map]
    cases hv : g (Fin.last m) <;> simp [hv, Function.comp_def]
  have hGen : ∀ (a b : Nat) (f : Fin (a + b) → Bool),
      countFalse f =
        countFalse (fun i : Fin a => f ⟨i.val, by omega⟩) +
        countFalse (fun j : Fin b => f ⟨a + j.val, by omega⟩) := by
    intro a b
    induction b with
    | zero =>
      intro f; simp [countFalse, List.finRange_zero]
    | succ b ih =>
      intro f
      have hF := hStep (a + b) f
      have hR := hStep b (fun j : Fin (b + 1) => f ⟨a + j.val, by omega⟩)
      have hLast : (⟨a + (Fin.last b).val, by simp [Fin.last]⟩ : Fin (a + (b + 1))) = Fin.last (a + b) :=
        Fin.ext rfl
      rw [hLast] at hR
      have hTailEq : (fun j : Fin b => f ⟨a + j.castSucc.val, by omega⟩) =
                     (fun j : Fin b => f ⟨a + j.val, by omega⟩) := rfl
      rw [hTailEq] at hR
      have hIH := ih (fun i : Fin (a + b) => f i.castSucc)
      have hLeftEq : (fun i : Fin a => (fun j : Fin (a + b) => f j.castSucc) ⟨i.val, by omega⟩) =
                     (fun i : Fin a => f ⟨i.val, by omega⟩) := rfl
      have hRightEq : (fun j : Fin b => (fun m : Fin (a + b) => f m.castSucc) ⟨a + j.val, by omega⟩) =
                      (fun j : Fin b => f ⟨a + j.val, by omega⟩) := rfl
      rw [hLeftEq, hRightEq] at hIH
      omega
  have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by simp [Nat.pow_succ]; omega
  have hf : countFalse xs = countFalse (fun i : Fin (2 ^ k + 2 ^ k) => xs ⟨i.val, by omega⟩) := by
    have hEqCast : ∀ (m n : Nat) (h : m = n) (g : Fin m → Bool),
        countFalse g = countFalse (fun i : Fin n => g ⟨i.val, by omega⟩) := by
      intro m n h g; subst h; rfl
    exact hEqCast (2 ^ (k + 1)) (2 ^ k + 2 ^ k) h2 xs
  rw [hf, hGen (2 ^ k) (2 ^ k) (fun i => xs ⟨i.val, by omega⟩)]

theorem countFalse_stride_cmp {k : Nat} (xs : Fin (2 ^ (k + 1)) → Bool) :
    countFalse (strideLayer (fun a b => (a && b, a || b)) xs) = countFalse xs := by
  rw [countFalse_split, countFalse_split xs]
  -- Pairwise sum over `Fin (2^k)`: `!(a && b) + !(a || b) = !a + !b`!
  have hPair : ∀ (m : Nat) (f g : Fin m → Bool),
      countFalse (fun i => f i && g i) + countFalse (fun i => f i || g i) =
      countFalse f + countFalse g := by
    intro m
    induction m with
    | zero => intro _ _; simp [countFalse, List.finRange_zero]
    | succ m ih =>
      intro f g
      have hStep : ∀ (h : Fin (m + 1) → Bool),
          countFalse h = countFalse (fun i : Fin m => h i.castSucc) + (if !(h (Fin.last m)) then 1 else 0) := by
        intro h; unfold countFalse
        rw [List.finRange_succ_last, List.filter_append, List.length_append]
        have hM : ((List.map Fin.castSucc (List.finRange m)).filter (fun i => !(h i))).length =
                  ((List.finRange m).filter (fun i => !(h i.castSucc))).length := by
          rw [List.filter_map, List.length_map]; rfl
        rw [hM]; cases hv : h (Fin.last m) <;> simp [hv]
      rw [hStep, hStep, hStep f, hStep g]
      have hRec := ih (fun i => f i.castSucc) (fun i => g i.castSucc)
      cases f (Fin.last m) <;> cases g (Fin.last m) <;> simp <;> omega
  have hL : (fun i : Fin (2 ^ k) => strideLayer (fun a b => (a && b, a || b)) xs
              ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) =
            (fun i : Fin (2 ^ k) => xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩ &&
                                    xs ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) := by
    funext i; simp only [strideLayer, i.isLt, ↓reduceDIte]
    have hadd : i.val + 2 ^ k = 2 ^ k + i.val := Nat.add_comm _ _
    simp [hadd]
  have hR : (fun i : Fin (2 ^ k) => strideLayer (fun a b => (a && b, a || b)) xs
              ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) =
            (fun i : Fin (2 ^ k) => xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩ ||
                                    xs ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) := by
    funext i
    have hnot : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
    have hsub : 2 ^ k + i.val - 2 ^ k = i.val := by omega
    simp [strideLayer, hnot, hsub]
  rw [hL, hR]
  exact hPair (2 ^ k) _ _

/-- 0-1 Bitonicity predicate on `Fin n → Bool`: either a single contiguous block of `1`s
    (`0* 1* 0*`) or a single contiguous block of `0`s (`1* 0* 1*`). -/
def IsBitonic {n : Nat} (xs : Fin n → Bool) : Prop :=
  ∃ a b : Nat, a ≤ b ∧ b ≤ n ∧
    ((∀ i : Fin n, xs i = decide (a ≤ i.val ∧ i.val < b)) ∨
     (∀ i : Fin n, xs i = decide (i.val < a ∨ b ≤ i.val)))

/-- **Clean-Half Lemma for 0-1 Bitonic Sequences**:
    Applying a comparator `strideLayer` to any 0-1 bitonic vector of length `2^(k+1)` produces
    two 0-1 bitonic halves `(lo, hi)` where EITHER `lo` is all-`false` OR `hi` is all-`true`! -/
theorem bitonic_clean_half {k : Nat} {xs : Fin (2 ^ (k + 1)) → Bool} (hB : IsBitonic xs) :
    let ys := strideLayer (fun a b => (a && b, a || b)) xs
    let lo : Fin (2 ^ k) → Bool := fun i => ys ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩
    let hi : Fin (2 ^ k) → Bool := fun i => ys ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩
    IsBitonic lo ∧ IsBitonic hi ∧ ((∀ i, lo i = false) ∨ (∀ i, hi i = true)) := by
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by simp [Nat.pow_succ]; omega
  rcases hB with ⟨a, b, hab, hbn, hCase⟩
  have hLoVal : ∀ i : Fin (2 ^ k), strideLayer (fun a b => (a && b, a || b)) xs
      ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩ =
      (xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩ &&
       xs ⟨i.val + 2 ^ k, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) := by
    intro i; simp [strideLayer, i.isLt]
  have hHiVal : ∀ i : Fin (2 ^ k), strideLayer (fun a b => (a && b, a || b)) xs
      ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩ =
      (xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩ ||
       xs ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) := by
    intro i
    have hnot : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
    have hsub : 2 ^ k + i.val - 2 ^ k = i.val := by omega
    simp [strideLayer, hnot, hsub]
  rcases hCase with hOnes | hZeros
  · -- Case 1: single block of 1s in `[a, b)`
    by_cases hLen : b - a ≤ 2 ^ k
    · have hLoFalse : ∀ i : Fin (2 ^ k), strideLayer (fun a b => (a && b, a || b)) xs
          ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩ = false := by
        intro i; rw [hLoVal, hOnes, hOnes]
        cases h1 : decide (a ≤ i.val ∧ i.val < b) <;> cases h2' : decide (a ≤ i.val + 2 ^ k ∧ i.val + 2 ^ k < b) <;> simp_all <;> omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le _, Or.inl (fun i => by dsimp only; rw [hLoFalse i]; simp)⟩, ?_, Or.inl hLoFalse⟩
      by_cases hbh : b ≤ 2 ^ k
      · refine ⟨a, b, hab, hbh, Or.inl fun i => ?_⟩
        dsimp only; rw [hHiVal, hOnes, hOnes]
        by_cases hc : a ≤ i.val ∧ i.val < b
        · simp [hc]
        · have hc2 : ¬ (a ≤ 2 ^ k + i.val ∧ 2 ^ k + i.val < b) := by omega
          simp [hc, hc2]
      · by_cases hah : 2 ^ k ≤ a
        · refine ⟨a - 2 ^ k, b - 2 ^ k, by omega, by omega, Or.inl fun i => ?_⟩
          dsimp only; rw [hHiVal, hOnes, hOnes]
          have := i.isLt
          cases h1 : decide (a ≤ i.val ∧ i.val < b) <;>
          cases h2' : decide (a ≤ 2 ^ k + i.val ∧ 2 ^ k + i.val < b) <;>
          cases h3 : decide (a - 2 ^ k ≤ i.val ∧ i.val < b - 2 ^ k) <;> simp_all <;> omega
        · refine ⟨b - 2 ^ k, a, by omega, by omega, Or.inr fun i => ?_⟩
          dsimp only; rw [hHiVal, hOnes, hOnes]
          have := i.isLt
          cases h1 : decide (a ≤ i.val ∧ i.val < b) <;>
          cases h2' : decide (a ≤ 2 ^ k + i.val ∧ 2 ^ k + i.val < b) <;>
          cases h3 : decide (i.val < b - 2 ^ k ∨ a ≤ i.val) <;> simp_all <;> omega
    · have hHiTrue : ∀ i : Fin (2 ^ k), strideLayer (fun a b => (a && b, a || b)) xs
          ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩ = true := by
        intro i; rw [hHiVal, hOnes, hOnes]
        by_cases hc1 : a ≤ i.val ∧ i.val < b
        · simp [hc1]
        · have hc2 : a ≤ 2 ^ k + i.val ∧ 2 ^ k + i.val < b := by have := i.isLt; omega
          simp [hc2]
      refine ⟨?_, ⟨0, 0, Nat.le_refl 0, Nat.zero_le _, Or.inr (fun i => by dsimp only; rw [hHiTrue i]; simp)⟩, Or.inr hHiTrue⟩
      refine ⟨a, b - 2 ^ k, by omega, by omega, Or.inl fun i => ?_⟩
      dsimp only; rw [hLoVal, hOnes, hOnes]
      by_cases hc : a ≤ i.val ∧ i.val < b - 2 ^ k
      · have h1 : a ≤ i.val ∧ i.val < b := by omega
        have h2' : a ≤ i.val + 2 ^ k ∧ i.val + 2 ^ k < b := by omega
        simp [hc, h1, h2']
      · cases h1 : decide (a ≤ i.val ∧ i.val < b) <;>
        cases h2' : decide (a ≤ i.val + 2 ^ k ∧ i.val + 2 ^ k < b) <;> simp_all <;> omega
  · -- Case 2: single block of 0s in `[a, b)` (exact dual!)
    by_cases hLen : b - a ≤ 2 ^ k
    · have hHiTrue : ∀ i : Fin (2 ^ k), strideLayer (fun a b => (a && b, a || b)) xs
          ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩ = true := by
        intro i; rw [hHiVal, hZeros, hZeros]
        cases h1 : decide (i.val < a ∨ b ≤ i.val) <;> cases h2' : decide (2 ^ k + i.val < a ∨ b ≤ 2 ^ k + i.val) <;> simp_all <;> omega
      refine ⟨?_, ⟨0, 0, Nat.le_refl 0, Nat.zero_le _, Or.inr (fun i => by dsimp only; rw [hHiTrue i]; simp)⟩, Or.inr hHiTrue⟩
      by_cases hbh : b ≤ 2 ^ k
      · refine ⟨a, b, hab, hbh, Or.inr fun i => ?_⟩
        dsimp only; rw [hLoVal, hZeros, hZeros]
        have hc2 : i.val + 2 ^ k < a ∨ b ≤ i.val + 2 ^ k := Or.inr (by omega)
        simp [hc2]
      · by_cases hah : 2 ^ k ≤ a
        · refine ⟨a - 2 ^ k, b - 2 ^ k, by omega, by omega, Or.inr fun i => ?_⟩
          dsimp only; rw [hLoVal, hZeros, hZeros]
          have := i.isLt
          cases h1 : decide (i.val < a ∨ b ≤ i.val) <;>
          cases h2' : decide (i.val + 2 ^ k < a ∨ b ≤ i.val + 2 ^ k) <;>
          cases h3 : decide (i.val < a - 2 ^ k ∨ b - 2 ^ k ≤ i.val) <;> simp_all <;> omega
        · refine ⟨b - 2 ^ k, a, by omega, by omega, Or.inl fun i => ?_⟩
          dsimp only; rw [hLoVal, hZeros, hZeros]
          have := i.isLt
          cases h1 : decide (i.val < a ∨ b ≤ i.val) <;>
          cases h2' : decide (i.val + 2 ^ k < a ∨ b ≤ i.val + 2 ^ k) <;>
          cases h3 : decide (b - 2 ^ k ≤ i.val ∧ i.val < a) <;> simp_all <;> omega
    · have hLoFalse : ∀ i : Fin (2 ^ k), strideLayer (fun a b => (a && b, a || b)) xs
          ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩ = false := by
        intro i; rw [hLoVal, hZeros, hZeros]
        cases h1 : decide (i.val < a ∨ b ≤ i.val) <;> cases h2' : decide (i.val + 2 ^ k < a ∨ b ≤ i.val + 2 ^ k) <;> simp_all <;> omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le _, Or.inl (fun i => by dsimp only; rw [hLoFalse i]; simp)⟩, ?_, Or.inl hLoFalse⟩
      refine ⟨a, b - 2 ^ k, by omega, by omega, Or.inr fun i => ?_⟩
      dsimp only; rw [hHiVal, hZeros, hZeros]
      have := i.isLt
      cases h1 : decide (i.val < a ∨ b ≤ i.val) <;>
      cases h2' : decide (2 ^ k + i.val < a ∨ b ≤ 2 ^ k + i.val) <;>
      cases h3 : decide (i.val < a ∨ b - 2 ^ k ≤ i.val) <;> simp_all <;> omega

/-- **Bitonic Merge Correctness ($\forall k \in \mathbb{N}$)**:
    For ANY certified comparator cell `C`, `bitonicMerge C k` preserves `countFalse` AND sorts
    every 0-1 bitonic sequence! -/
theorem bitonicMerge_sound (C : Cell2) (hC : checkComparatorCell C = true) :
    ∀ (k : Nat) (xs : Fin (2 ^ k) → Bool),
      countFalse (bitonicMerge C k xs) = countFalse xs ∧
      (IsBitonic xs → bitonicMerge C k xs = thresholdSort xs) := by
  have hCmp : C.eval false = fun a b => (a && b, a || b) := by
    funext a b; exact checkComparatorCell_sound hC a b
  intro k
  induction k with
  | zero =>
    intro xs
    refine ⟨rfl, fun _ => ?_⟩
    have hSort : IsSortedWith (if xs ⟨0, by decide⟩ then 0 else 1) xs := by
      refine ⟨by cases xs ⟨0, by decide⟩ <;> decide, fun i => ?_⟩
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; simp at this; omega)
      subst hi; cases xs ⟨0, by decide⟩ <;> decide
    exact isSortedWith_eq_threshold hSort
  | succ k ih =>
    intro xs
    simp only [bitonicMerge, hCmp]
    let ys := strideLayer (fun a b => (a && b, a || b)) xs
    let lo : Fin (2 ^ k) → Bool := fun i => ys ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩
    let hi : Fin (2 ^ k) → Bool := fun i => ys ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩
    have ihLo := ih lo
    have ihHi := ih hi
    have hCount : countFalse (parHalf (bitonicMerge C k) ys) = countFalse xs := by
      rw [countFalse_split]
      have hL : (fun i : Fin (2 ^ k) => parHalf (bitonicMerge C k) ys ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) =
                bitonicMerge C k lo := by funext i; simp [parHalf, lo, i.isLt]
      have hR : (fun i : Fin (2 ^ k) => parHalf (bitonicMerge C k) ys ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) =
                bitonicMerge C k hi := by
        funext i
        have hnot : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
        have hsub : 2 ^ k + i.val - 2 ^ k = i.val := by omega
        simp [parHalf, hi, hnot, hsub]
      rw [hL, hR, ihLo.1, ihHi.1, ← countFalse_split ys]
      exact countFalse_stride_cmp xs
    refine ⟨hCount, fun hB => ?_⟩
    have ⟨hBLo, hBHi, hClean⟩ := bitonic_clean_half hB
    have hLoSort := ihLo.2 hBLo
    have hHiSort := ihHi.2 hBHi
    -- Prove `parHalf (bitonicMerge C k) ys` is sorted with `countFalse xs` zeros!
    have hOutSort : IsSortedWith (countFalse lo + countFalse hi) (parHalf (bitonicMerge C k) ys) := by
      have hLoLe : countFalse lo ≤ 2 ^ k := by
        unfold countFalse
        exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      have hHiLe : countFalse hi ≤ 2 ^ k := by
        unfold countFalse
        exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      refine ⟨by simp [Nat.pow_succ]; omega, fun i => ?_⟩
      simp only [parHalf]
      rcases hClean with hAllF | hAllT
      · have hCountLo : countFalse lo = 2 ^ k := by
          have : IsSortedWith (2 ^ k) lo :=
            ⟨Nat.le_refl _, fun j => by
              have hj := hAllF j; dsimp only [lo, ys] at hj ⊢; rw [hj]; have := j.isLt; simp [this]⟩
          exact countFalse_of_isSortedWith this
        by_cases hlt : i.val < 2 ^ k
        · simp only [hlt, ↓reduceDIte]
          rw [hLoSort, thresholdSort, hCountLo]
          have h1 : ¬ (2 ^ k ≤ i.val) := by omega
          have h2 : ¬ (2 ^ k + countFalse hi ≤ i.val) := by omega
          simp [h1, h2]
        · simp only [hlt, ↓reduceDIte]
          rw [hHiSort, thresholdSort, hCountLo]
          by_cases hc : countFalse hi ≤ i.val - 2 ^ k
          · have : 2 ^ k + countFalse hi ≤ i.val := by omega
            simp [hc, this]
          · have : ¬ (2 ^ k + countFalse hi ≤ i.val) := by omega
            simp [hc, this]
      · have hCountHi : countFalse hi = 0 := by
          have : IsSortedWith 0 hi :=
            ⟨Nat.zero_le _, fun j => by
              have hj := hAllT j; dsimp only [hi, ys] at hj ⊢; rw [hj]; simp⟩
          exact countFalse_of_isSortedWith this
        by_cases hlt : i.val < 2 ^ k
        · simp only [hlt, ↓reduceDIte]
          rw [hLoSort, thresholdSort, hCountHi]
          simp
        · simp only [hlt, ↓reduceDIte]
          rw [hHiSort, thresholdSort, hCountHi]
          have : countFalse lo ≤ i.val := by omega
          simp [this]
    have hEq := isSortedWith_eq_threshold hOutSort
    have hT : thresholdSort (parHalf (bitonicMerge C k) ys) = thresholdSort xs := by
      funext i; simp only [thresholdSort, hCount]
    exact hEq.trans hT

/-- **Bitonic Sort Correctness ($\forall k \in \mathbb{N}$)**:
    For ANY certified comparator cell `C`, `bitonicSort C k xs = thresholdSort xs`! -/
theorem bitonicSort_sound (C : Cell2) (hC : checkComparatorCell C = true) :
    ∀ (k : Nat) (xs : Fin (2 ^ k) → Bool), bitonicSort C k xs = thresholdSort xs := by
  intro k
  induction k with
  | zero =>
    intro xs
    have hSort : IsSortedWith (if xs ⟨0, by decide⟩ then 0 else 1) xs := by
      refine ⟨by cases xs ⟨0, by decide⟩ <;> decide, fun i => ?_⟩
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; simp at this; omega)
      subst hi; cases xs ⟨0, by decide⟩ <;> decide
    exact isSortedWith_eq_threshold hSort
  | succ k ih =>
    intro xs
    simp only [bitonicSort]
    let xsL : Fin (2 ^ k) → Bool := fun i => xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩
    let xsR : Fin (2 ^ k) → Bool := fun i => xs ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩
    let L := bitonicSort C k xsL
    let R := bitonicSort C k xsR
    let merged : Fin (2 ^ (k + 1)) → Bool := fun i =>
      if h : i.val < 2 ^ k then L ⟨i.val, h⟩
      else R ⟨2 ^ k - 1 - (i.val - 2 ^ k), by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
    have hL : L = thresholdSort xsL := ih xsL
    have hR : R = thresholdSort xsR := ih xsR
    have hLeL : countFalse xsL ≤ 2 ^ k := by unfold countFalse; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    have hLeR : countFalse xsR ≤ 2 ^ k := by unfold countFalse; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    -- `merged` is `0^{zL} 1^{2^k - zL} 1^{2^k - zR} 0^{zR}` → a single contiguous block of `1`s!
    have hBit : IsBitonic merged := by
      refine ⟨countFalse xsL, 2 ^ (k + 1) - countFalse xsR, by simp [Nat.pow_succ]; omega,
              Nat.sub_le _ _, Or.inl fun i => ?_⟩
      simp only [merged, hL, hR, thresholdSort]
      by_cases hlt : i.val < 2 ^ k
      · simp only [hlt, ↓reduceDIte]
        have hlt2 : i.val < 2 ^ (k + 1) - countFalse xsR := by simp [Nat.pow_succ]; omega
        simp [hlt2]
      · simp only [hlt, ↓reduceDIte]
        have hge : countFalse xsL ≤ i.val := by omega
        by_cases hc : countFalse xsR ≤ 2 ^ k - 1 - (i.val - 2 ^ k)
        · have : i.val < 2 ^ (k + 1) - countFalse xsR := by simp [Nat.pow_succ]; omega
          simp [hge, hc, this]
        · have : ¬ (i.val < 2 ^ (k + 1) - countFalse xsR) := by simp [Nat.pow_succ]; omega
          simp [hge, hc, this]
    -- And `countFalse merged = countFalse xs`!
    have hCnt : countFalse merged = countFalse xs := by
      rw [countFalse_split merged, countFalse_split xs]
      have hCntL : countFalse (fun i : Fin (2 ^ k) => merged ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) =
                   countFalse xsL := by
        have hEq : (fun i : Fin (2 ^ k) => merged ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) =
                   thresholdSort xsL := by funext i; simp [merged, hL, i.isLt]
        rw [hEq]
        exact countFalse_of_isSortedWith ⟨hLeL, fun _ => rfl⟩
      have hCntR : countFalse (fun i : Fin (2 ^ k) => merged ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) =
                   countFalse xsR := by
        -- `merged (2^k + i) = decide (countFalse xsR ≤ 2^k - 1 - i) = decide (i < 2^k - countFalse xsR)`
        -- countFalse of `1^{2^k - zR} 0^{zR}` equals `zR`.
        have hRevCnt : ∀ (m z : Nat), z ≤ m →
            countFalse (fun i : Fin m => decide (z ≤ m - 1 - i.val)) = z := by
          intro m z hz
          have hGen : ∀ (t : Nat), t ≤ m →
              ((List.finRange t).filter (fun i => !(decide (z ≤ m - 1 - i.val)))).length =
              t - min t (m - z) := by
            intro t
            induction t with
            | zero => intro _; simp [List.finRange_zero]
            | succ t iht =>
              intro ht
              rw [List.finRange_succ_last, List.filter_append, List.length_append]
              have hM : ((List.map Fin.castSucc (List.finRange t)).filter (fun i : Fin (t + 1) => !(decide (z ≤ m - 1 - i.val)))).length =
                        ((List.finRange t).filter (fun i : Fin t => !(decide (z ≤ m - 1 - i.val)))).length := by
                rw [List.filter_map, List.length_map]; rfl
              rw [hM, iht (by omega)]
              by_cases hcond : z ≤ m - 1 - t
              · simp [Fin.last, hcond]; omega
              · simp [Fin.last, hcond]; omega
          unfold countFalse
          rw [hGen m (Nat.le_refl m)]; omega
        have hEq : (fun i : Fin (2 ^ k) => merged ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩) =
                   (fun i : Fin (2 ^ k) => decide (countFalse xsR ≤ 2 ^ k - 1 - i.val)) := by
          funext i
          have hnot : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
          have hsub : 2 ^ k + i.val - 2 ^ k = i.val := by omega
          simp [merged, hR, thresholdSort, hnot, hsub]
        rw [hEq]
        exact hRevCnt (2 ^ k) (countFalse xsR) hLeR
      rw [hCntL, hCntR]
    have hM := (bitonicMerge_sound C hC (k + 1) merged).2 hBit
    rw [hM]
    funext i; simp only [thresholdSort, hCnt]

/-- **Batcher Odd-Even Merge Correctness ($\forall k \ge 1$)**:
    If `xs` consists of two sorted halves with `p` and `q` zeros respectively, then
    `oddEvenMerge C k xs` is sorted with `p + q` zeros! -/
theorem oddEvenMerge_sound (C : Cell2) (hC : checkComparatorCell C = true) :
    ∀ (k : Nat) (p q : Nat) (xs : Fin (2 ^ (k + 1)) → Bool),
      p ≤ 2 ^ k → q ≤ 2 ^ k →
      (∀ i : Fin (2 ^ (k + 1)),
        xs i = if i.val < 2 ^ k then decide (p ≤ i.val) else decide (q ≤ i.val - 2 ^ k)) →
      IsSortedWith (p + q) (oddEvenMerge C (k + 1) xs) := by
  have hCmp : C.eval false = fun a b => (a && b, a || b) := by
    funext a b; exact checkComparatorCell_sound hC a b
  intro k
  induction k with
  | zero =>
    intro p q xs hp hq hxs
    refine ⟨by simp at *; omega, fun i => ?_⟩
    simp only [oddEvenMerge, hCmp]
    have h0 := hxs ⟨0, by decide⟩
    have h1 := hxs ⟨1, by decide⟩
    have hi : i.val = 0 ∨ i.val = 1 := by have := i.isLt; simp at this; omega
    have hp01 : p = 0 ∨ p = 1 := by simp at hp; omega
    have hq01 : q = 0 ∨ q = 1 := by simp at hq; omega
    rcases hi with h0i | h1i
    · simp only [h0i, ↓reduceIte, h0, h1]
      rcases hp01 with rfl | rfl <;> rcases hq01 with rfl | rfl <;> decide
    · simp only [h1i, Nat.one_ne_zero, ↓reduceIte, h0, h1]
      rcases hp01 with rfl | rfl <;> rcases hq01 with rfl | rfl <;> decide
  | succ k ih =>
    intro p q xs hp hq hxs
    simp only [oddEvenMerge, hCmp]
    let ev : Fin (2 ^ (k + 1)) → Bool := fun j => xs ⟨2 * j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩
    let od : Fin (2 ^ (k + 1)) → Bool := fun j => xs ⟨2 * j.val + 1, by have := j.isLt; simp [Nat.pow_succ]; omega⟩
    have hEvSpec : ∀ j : Fin (2 ^ (k + 1)),
        ev j = if j.val < 2 ^ k then decide ((p + 1) / 2 ≤ j.val) else decide ((q + 1) / 2 ≤ j.val - 2 ^ k) := by
      intro j
      simp only [ev, hxs]
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by simp [Nat.pow_succ]; omega
      by_cases hj : j.val < 2 ^ k
      · have h2j : 2 * j.val < 2 ^ (k + 1) := by omega
        simp only [hj, h2j, ↓reduceIte]
        by_cases hc : p ≤ 2 * j.val <;> simp [hc] <;> omega
      · have h2j : ¬ (2 * j.val < 2 ^ (k + 1)) := by omega
        simp only [hj, h2j, ↓reduceIte]
        by_cases hc : q ≤ 2 * j.val - 2 ^ (k + 1) <;> simp [hc] <;> omega
    have hOdSpec : ∀ j : Fin (2 ^ (k + 1)),
        od j = if j.val < 2 ^ k then decide (p / 2 ≤ j.val) else decide (q / 2 ≤ j.val - 2 ^ k) := by
      intro j
      simp only [od, hxs]
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by simp [Nat.pow_succ]; omega
      by_cases hj : j.val < 2 ^ k
      · have h2j : 2 * j.val + 1 < 2 ^ (k + 1) := by omega
        simp only [hj, h2j, ↓reduceIte]
        by_cases hc : p ≤ 2 * j.val + 1 <;> simp [hc] <;> omega
      · have h2j : ¬ (2 * j.val + 1 < 2 ^ (k + 1)) := by omega
        simp only [hj, h2j, ↓reduceIte]
        by_cases hc : q ≤ 2 * j.val + 1 - 2 ^ (k + 1) <;> simp [hc] <;> omega
    have hEvSort := ih ((p + 1) / 2) ((q + 1) / 2) ev (by simp [Nat.pow_succ] at hp; omega)
                      (by simp [Nat.pow_succ] at hq; omega) hEvSpec
    have hOdSort := ih (p / 2) (q / 2) od (by simp [Nat.pow_succ] at hp; omega)
                      (by simp [Nat.pow_succ] at hq; omega) hOdSpec
    let zEv := (p + 1) / 2 + (q + 1) / 2
    let zOd := p / 2 + q / 2
    have hPow4 : 2 ^ (k + 2) = 4 * 2 ^ k := by simp [Nat.pow_succ]; omega
    have hPow2 : 2 ^ (k + 1) = 2 * 2 ^ k := by simp [Nat.pow_succ]; omega
    refine ⟨by omega, fun i => ?_⟩
    simp only [oddEvenSwapLayer]
    have hEvVal := hEvSort.2
    have hOdVal := hOdSort.2
    by_cases h0 : i.val = 0
    · simp only [h0, ↓reduceDIte, Nat.zero_mod, Nat.zero_div, ↓reduceIte]
      change oddEvenMerge C (k + 1) ev ⟨0, Nat.two_pow_pos (k + 1)⟩ = decide (p + q ≤ 0)
      rw [hEvVal]
      dsimp only
      by_cases hc : (p + 1) / 2 + (q + 1) / 2 ≤ 0 <;> by_cases hpq : p + q ≤ 0 <;> simp [hc, hpq] <;> omega
    · simp only [h0, ↓reduceDIte]
      by_cases hLast : i.val + 1 = 2 ^ (k + 2) ∧ i.val % 2 = 1
      · simp only [hLast, and_self, ↓reduceDIte, Nat.one_ne_zero, ↓reduceIte]
        change oddEvenMerge C (k + 1) od ⟨i.val / 2, by have := i.isLt; omega⟩ = decide (p + q ≤ i.val)
        rw [hOdVal]
        dsimp only
        by_cases hc : p / 2 + q / 2 ≤ i.val / 2 <;> simp [hc] <;> omega
      · simp only [hLast, ↓reduceDIte]
        by_cases hOdd : i.val % 2 = 1
        · simp only [hOdd, ↓reduceDIte]
          have hNextEv : (i.val + 1) % 2 = 0 := by omega
          simp only [Nat.one_ne_zero, hNextEv, ↓reduceIte]
          change (oddEvenMerge C (k + 1) od ⟨i.val / 2, by have := i.isLt; omega⟩ &&
                  oddEvenMerge C (k + 1) ev ⟨(i.val + 1) / 2, by have := i.isLt; omega⟩) = decide (p + q ≤ i.val)
          rw [hOdVal, hEvVal]
          dsimp only
          by_cases c1 : p / 2 + q / 2 ≤ i.val / 2 <;> by_cases c2 : (p + 1) / 2 + (q + 1) / 2 ≤ (i.val + 1) / 2 <;>
            simp [c1, c2] <;> omega
        · simp only [hOdd, ↓reduceDIte]
          have hEv : i.val % 2 = 0 := by omega
          have hPrevOdd : (i.val - 1) % 2 = 1 := by omega
          simp only [hEv, hPrevOdd, Nat.one_ne_zero, ↓reduceIte]
          change (oddEvenMerge C (k + 1) od ⟨(i.val - 1) / 2, by have := i.isLt; omega⟩ ||
                  oddEvenMerge C (k + 1) ev ⟨i.val / 2, by have := i.isLt; omega⟩) = decide (p + q ≤ i.val)
          rw [hOdVal, hEvVal]
          dsimp only
          by_cases c1 : p / 2 + q / 2 ≤ (i.val - 1) / 2 <;> by_cases c2 : (p + 1) / 2 + (q + 1) / 2 ≤ i.val / 2 <;>
            simp [c1, c2] <;> omega

/-- **Batcher Odd-Even Mergesort Correctness ($\forall k \in \mathbb{N}$)**:
    For ANY certified comparator cell `C`, `oddEvenSort C k xs = thresholdSort xs`! -/
theorem oddEvenSort_sound (C : Cell2) (hC : checkComparatorCell C = true) :
    ∀ (k : Nat) (xs : Fin (2 ^ k) → Bool), oddEvenSort C k xs = thresholdSort xs := by
  intro k
  induction k with
  | zero =>
    intro xs
    have hSort : IsSortedWith (if xs ⟨0, by decide⟩ then 0 else 1) xs := by
      refine ⟨by cases xs ⟨0, by decide⟩ <;> decide, fun i => ?_⟩
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; simp at this; omega)
      subst hi; cases xs ⟨0, by decide⟩ <;> decide
    exact isSortedWith_eq_threshold hSort
  | succ k ih =>
    intro xs
    simp only [oddEvenSort]
    let xsL : Fin (2 ^ k) → Bool := fun i => xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩
    let xsR : Fin (2 ^ k) → Bool := fun i => xs ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩
    have hL : oddEvenSort C k xsL = thresholdSort xsL := ih xsL
    have hR : oddEvenSort C k xsR = thresholdSort xsR := ih xsR
    have hLeL : countFalse xsL ≤ 2 ^ k := by unfold countFalse; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    have hLeR : countFalse xsR ≤ 2 ^ k := by unfold countFalse; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    have hM := oddEvenMerge_sound C hC k (countFalse xsL) (countFalse xsR)
      (fun i => if h : i.val < 2 ^ k then oddEvenSort C k xsL ⟨i.val, h⟩
                else oddEvenSort C k xsR ⟨i.val - 2 ^ k, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩)
      hLeL hLeR (fun i => by
        by_cases hlt : i.val < 2 ^ k
        · simp [hlt, hL, thresholdSort]
        · simp [hlt, hR, thresholdSort])
    have hCnt : countFalse xs = countFalse xsL + countFalse xsR := countFalse_split xs
    funext i
    rw [hM.2 i, thresholdSort, hCnt]

/-- **General Soundness Meta-Theorem (Engine 4B: Bitonic Sort ≡ Odd-Even Mergesort ≡ Threshold Sort)**:
    For ANY two concrete gate-level comparator cells `C1, C2` passing `checkComparatorCell`,
    Batcher's Bitonic Sorter (`C1`) and Batcher's Odd-Even Mergesort (`C2`) are bit-for-bit
    equivalent AND equal to `thresholdSort` for ALL `k : Nat` (width `2^k`)! -/
theorem bitonic_eq_oddEven_sound (C1 C2 : Cell2)
    (h1 : checkComparatorCell C1 = true) (h2 : checkComparatorCell C2 = true) :
    ∀ (k : Nat) (xs : Fin (2 ^ k) → Bool),
      bitonicSort C1 k xs = oddEvenSort C2 k xs ∧
      bitonicSort C1 k xs = thresholdSort xs := by
  intro k xs
  have hb := bitonicSort_sound C1 h1 k xs
  have ho := oddEvenSort_sound C2 h2 k xs
  exact ⟨hb.trans ho.symm, hb⟩

-- ============================================================================
-- KNUTH 0–1 PRINCIPLE META-THEOREM (LIFTING BOOLEAN SORTING TO TOTAL ORDERS)
-- ============================================================================

/-- An oblivious compare-exchange sorting network on `n` wires: a list of `(i, j)` comparators
    placing `min(v i, v j)` at `i` and `max(v i, v j)` at `j`. -/
abbrev CompNet (n : Nat) := List (Fin n × Fin n)

def evalCompGateOrd {α : Type} (le : α → α → Bool) {n : Nat}
    (p : Fin n × Fin n) (v : Fin n → α) : Fin n → α :=
  let a := v p.1
  let b := v p.2
  let lo := if le a b then a else b
  let hi := if le a b then b else a
  fun k => if k = p.1 then lo else if k = p.2 then hi else v k

def evalCompNetOrd {α : Type} (le : α → α → Bool) {n : Nat} :
    CompNet n → (Fin n → α) → (Fin n → α)
  | [], v      => v
  | p :: ps, v => evalCompNetOrd le ps (evalCompGateOrd le p v)

def evalCompNetBool {n : Nat} (net : CompNet n) (v : Fin n → Bool) : Fin n → Bool :=
  evalCompNetOrd (fun a b => !a || b) net v

/-- **Knuth 0–1 Principle Meta-Theorem**:
    For ANY oblivious compare-exchange network `net : CompNet n` and ANY total preorder `(α, le)`,
    if `evalCompNetBool net` sorts all Boolean vectors `Fin n → Bool`, then `evalCompNetOrd le net`
    sorts ALL `α`-vectors `Fin n → α`! -/
theorem zero_one_principle {α : Type} (le : α → α → Bool)
    (hRefl : ∀ x, le x x = true)
    (hTrans : ∀ x y z, le x y = true → le y z = true → le x z = true)
    (hTotal : ∀ x y, le x y = true ∨ le y x = true)
    {n : Nat} (net : CompNet n)
    (hBool : ∀ (v : Fin n → Bool) (i j : Fin n),
      i.val ≤ j.val → evalCompNetBool net v i = true → evalCompNetBool net v j = true) :
    ∀ (v : Fin n → α) (i j : Fin n),
      i.val ≤ j.val → le (evalCompNetOrd le net v i) (evalCompNetOrd le net v j) = true := by
  -- Monotone threshold projection `proj t x := le t x` commutes with every compare-exchange gate!
  have hGateComm : ∀ (t : α) (p : Fin n × Fin n) (v : Fin n → α),
      (fun k => le t (evalCompGateOrd le p v k)) =
      evalCompGateOrd (fun a b => !a || b) p (fun k => le t (v k)) := by
    intro t p v; funext k
    simp only [evalCompGateOrd]
    by_cases hk1 : k = p.1
    · simp only [hk1, ↓reduceIte]
      by_cases hab : le (v p.1) (v p.2) = true
      · simp only [hab, ↓reduceIte]
        cases hta : le t (v p.1) <;> cases htb : le t (v p.2) <;> simp
        · exact absurd (hTrans t (v p.1) (v p.2) hta hab) (by simp [htb])
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        have hba : le (v p.2) (v p.1) = true := (hTotal _ _).resolve_left hab
        cases hta : le t (v p.1) <;> cases htb : le t (v p.2) <;> simp
        · exact absurd (hTrans t (v p.2) (v p.1) htb hba) (by simp [hta])
    · simp only [hk1, ↓reduceIte]
      by_cases hk2 : k = p.2
      · simp only [hk2, ↓reduceIte]
        by_cases hab : le (v p.1) (v p.2) = true
        · simp only [hab, ↓reduceIte]
          cases hta : le t (v p.1) <;> cases htb : le t (v p.2) <;> simp
          · exact absurd (hTrans t (v p.1) (v p.2) hta hab) (by simp [htb])
        · simp only [hab, Bool.false_eq_true, ↓reduceIte]
          have hba : le (v p.2) (v p.1) = true := (hTotal _ _).resolve_left hab
          cases hta : le t (v p.1) <;> cases htb : le t (v p.2) <;> simp
          · exact absurd (hTrans t (v p.2) (v p.1) htb hba) (by simp [hta])
      · simp [hk2]
  have hNetComm : ∀ (t : α) (ns : CompNet n) (v : Fin n → α),
      (fun k => le t (evalCompNetOrd le ns v k)) =
      evalCompNetBool ns (fun k => le t (v k)) := by
    intro t ns
    induction ns with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro v
      simp only [evalCompNetOrd, evalCompNetBool]
      rw [ih, hGateComm t p v]
      rfl
  intro v i j hij
  let t := evalCompNetOrd le net v i
  have hti : evalCompNetBool net (fun k => le t (v k)) i = true := by
    have := congrFun (hNetComm t net v) i
    rw [← this]; exact hRefl t
  have htj := hBool (fun k => le t (v k)) i j hij hti
  have := congrFun (hNetComm t net v) j
  rw [this]; exact htj

/-- Controlled-Swap Butterfly XOR-Permuter cell: `c ? (b, a) : (a, b)`. -/
def condSwapCell : Cell2 :=
  { net := { inW := 3, gates := [.mux 0 1 2, .mux 0 2 1], outs := [3, 4] }, hIn := rfl, hOut := rfl }

/-- One of the 8 bijective 2-wire Boolean cells that FAILS 4-Wire Interchange:
    `affineNonCommCell(a, b) = (a ^ b, ~b)` with inverse `(~(a ^ b), ~b)`! -/
def affineNonCommCell : Cell2 :=
  { net := { inW := 3, gates := [.xor 1 2, .not 2], outs := [3, 4] }, hIn := rfl, hOut := rfl }

def affineNonCommInvCell : Cell2 :=
  { net := { inW := 3, gates := [.xnor 1 2, .not 2], outs := [3, 4] }, hIn := rfl, hOut := rfl }

def brokenCmpCell : Cell2 :=
  { net := { inW := 3, gates := [.or 1 2, .and 1 2], outs := [3, 4] }, hIn := rfl, hOut := rfl }

/-- **Certified Infinite Theorem 4.1 (Fast Reed–Muller / ANF Butterfly Self-Inversion & Omega Equivalence)**:
    For ALL `k : Nat` (width `2^k`), the gate-level Reed–Muller ANF Butterfly network is:
    1. Bit-for-bit identical to the constant-geometry Pease/Omega network,
    2. Stage-order independent (`fwdButterfly = bwdButterfly`), and
    3. Strictly self-inverse (`fwdButterfly ∘ fwdButterfly = id`)! -/
theorem reed_muller_anf_butterfly_all_k :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      omegaNet anfCell k ctrls xs = fwdButterfly anfCell k ctrls xs ∧
      fwdButterfly anfCell k ctrls xs = bwdButterfly anfCell k ctrls xs ∧
      fwdButterfly anfCell k ctrls (fwdButterfly anfCell k ctrls xs) = xs := by
  intro k ctrls xs
  exact ⟨omega_eq_fwdButterfly_sound anfCell k ctrls xs,
         butterfly_interchange_sound anfCell (by decide) k ctrls xs,
         butterfly_fwd_inverse_sound anfCell anfCell (by decide) (by decide) k ctrls xs⟩

/-- **Certified Infinite Theorem 4.2 (Non-Involutive Order-3 GF(4) Butterfly Exact Cancellation)**:
    For ALL `k : Nat` (width `2^k`), `fwdButterfly gf4InvCell ∘ fwdButterfly gf4FwdCell = id`
    AND `omegaNet gf4FwdCell = fwdButterfly gf4FwdCell = bwdButterfly gf4FwdCell`! -/
theorem gf4_butterfly_inverse_all_k :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      fwdButterfly gf4InvCell k ctrls (fwdButterfly gf4FwdCell k ctrls xs) = xs ∧
      omegaNet gf4FwdCell k ctrls xs = bwdButterfly gf4FwdCell k ctrls xs := by
  intro k ctrls xs
  exact ⟨butterfly_fwd_inverse_sound gf4FwdCell gf4InvCell (by decide) (by decide) k ctrls xs,
         (omega_eq_fwdButterfly_sound gf4FwdCell k ctrls xs).trans
           (butterfly_interchange_sound gf4FwdCell (by decide) k ctrls xs)⟩

/-- **Certified Infinite Theorem 4.3 (Sharp Separation: Non-Commuting Bijective Butterfly Inversion)**:
    `affineNonCommCell = (a ^ b, ~b)` FAILS 4-Wire Interchange (`checkInterchange2 = false`),
    yet STILL satisfies exact backward-inverse cancellation `bwdButterfly inv ∘ fwdButterfly = id`
    AND `omegaNet = fwdButterfly` for ALL `k : Nat`! -/
theorem noncomm_bijective_butterfly_inverse_all_k :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      bwdButterfly affineNonCommInvCell k ctrls (fwdButterfly affineNonCommCell k ctrls xs) = xs ∧
      omegaNet affineNonCommCell k ctrls xs = fwdButterfly affineNonCommCell k ctrls xs := by
  intro k ctrls xs
  exact ⟨butterfly_bwd_inverse_sound affineNonCommCell affineNonCommInvCell (by decide) k ctrls xs,
         omega_eq_fwdButterfly_sound affineNonCommCell k ctrls xs⟩

/-- **Certified Infinite Theorem 4.4 (Controlled-Swap Butterfly XOR-Permuter Self-Inversion & Omega Equiv)**: -/
theorem condSwap_butterfly_all_k :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      omegaNet condSwapCell k ctrls xs = fwdButterfly condSwapCell k ctrls xs ∧
      fwdButterfly condSwapCell k ctrls (fwdButterfly condSwapCell k ctrls xs) = xs := by
  intro k ctrls xs
  exact ⟨omega_eq_fwdButterfly_sound condSwapCell k ctrls xs,
         butterfly_fwd_inverse_sound condSwapCell condSwapCell (by decide) (by decide) k ctrls xs⟩

/-- **Certified Infinite Theorem 4.5 (Batcher Bitonic Sort ≡ Batcher Odd-Even Mergesort ≡ Threshold Sort)**:
    For ALL `k : Nat` (width `2^k`), the AND/OR Bitonic Sorter and the NAND-only Odd-Even
    Mergesorter are bit-for-bit identical AND equal to the canonical Threshold Sorter! -/
theorem bitonic_andOr_eq_oddEven_nand_all_k :
    ∀ (k : Nat) (xs : Fin (2 ^ k) → Bool),
      bitonicSort andOrCmpCell k xs = oddEvenSort nandOnlyCmpCell k xs ∧
      bitonicSort andOrCmpCell k xs = thresholdSort xs :=
  bitonic_eq_oddEven_sound andOrCmpCell nandOnlyCmpCell (by decide) (by decide)

-- ============================================================================
-- NEGATIVE / SHARPNESS / MUTATION TESTS & CONSTRUCTIVE NON-VACUITY WITNESSES
-- ============================================================================

-- Negative tests proving broken / non-commuting / mutated cells are strictly rejected:
example : checkInterchange2 andOrCmpCell = false := by decide
example : checkInterchange2 affineNonCommCell = false := by decide
example : checkInverse2 gf4FwdCell gf4FwdCell = false := by decide   -- gf4FwdCell is NOT an involution!
example : checkComparatorCell brokenCmpCell = false := by decide
example : checkCell2Equiv andOrCmpCell brokenCmpCell = false := by decide

-- Constructive non-vacuity witnesses confirming every meta-theorem's hypotheses are inhabited:
example : Nonempty { cert : SliceBisimCert 1 2 //
    checkSliceBisim rippleAdderGen dualRailAdderGen rfl rfl rfl cert = true } :=
  ⟨⟨dualRailBisimCert, by decide⟩⟩

example : Nonempty { cert : PrefixToSliceCert 2 //
    checkPrefixToSliceCert prefixAdderGlitchedXorSpec rippleAdderGen rfl rfl rfl cert = true } :=
  ⟨⟨xorPropCert, by decide⟩⟩

example : Nonempty { M : MuxCell // checkMuxCell M = true } :=
  ⟨⟨nandOnlyMuxCell, by decide⟩⟩

example : Nonempty { C : Cell2 // checkInterchange2 C = true ∧ checkInverse2 C C = true } :=
  ⟨⟨anfCell, by decide, by decide⟩⟩

example : Nonempty { C : Cell2 // checkComparatorCell C = true } :=
  ⟨⟨nandOnlyCmpCell, by decide⟩⟩

-- Concrete 4-bit (k = 2) width witness demonstrating non-triviality of `affineNonCommCell`
-- failing stage commutation at k = 2 on all-zeros `(F, F, F, F)`!
example : fwdButterfly affineNonCommCell 2 (fun _ => false) (fun _ => false) ⟨1, by decide⟩ ≠
          bwdButterfly affineNonCommCell 2 (fun _ => false) (fun _ => false) ⟨1, by decide⟩ := by
  decide

end SiliconBisim

-- ============================================================================
-- AXIOM AUDIT (`#print axioms` on EVERY meta-theorem & certified infinite theorem)
-- ============================================================================



