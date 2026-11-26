/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`ring-attention-kulisch-bounds`)

Pure-`Init` (zero Mathlib) exact definitions for:
1. Exact online-softmax monoid over positive rational weights `(w, l, o)`.
2. Exact IEEE-754 Round-to-Nearest-Even (RNE) integer and dyadic-grid rounding.
3. Sequential (`L2R`/`DESC`) and balanced binary tree (`TREE`) attention-sink accumulators.
4. Descending-`m_i` vs ascending-`m_i` online-softmax merge models and rescale counters.
5. Exponent-aligned fixed-point / Kulisch accumulation, binary reduction trees, list permutations,
   and exact bit-width bounds `W_inv(k, p)` and `W_kulisch(k, eMax, eMin, M)`.
-/

namespace RingAttnKulisch

/-- Exact `2^n` as a rational. -/
def pow2Rat (n : Nat) : Rat :=
  ((2 ^ n : Nat) : Rat)

/-- Exact `2^{-n}` as a rational. -/
def invPow2Rat (n : Nat) : Rat :=
  1 / ((2 ^ n : Nat) : Rat)

/-- Exact integer-exponent power of two `2^z` as a rational. -/
def exp2Int (z : Int) : Rat :=
  if 0 ≤ z then pow2Rat z.toNat else invPow2Rat (-z).toNat

/-- Rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if 0 ≤ x then x else -x

/-! ### 1. Exact Online-Softmax Monoid State -/

/-- Exact online-softmax chunk state `(w, l, o)` where `w > 0` is the positive
    scale factor `exp(m)` (or `2^m`), `l` is the local unnormalized denominator,
    and `o` is the local unnormalized numerator/output. -/
structure OnlineSoftmaxState where
  w : Rat
  l : Rat
  o : Rat
  deriving DecidableEq

/-- Exact online-softmax merge operation `(w_1, l_1, o_1) ⊕ (w_2, l_2, o_2)`
    anchored at `m = max(w_1, w_2)`. -/
def onlineMerge (s₁ s₂ : OnlineSoftmaxState) : OnlineSoftmaxState :=
  let m := if s₁.w ≤ s₂.w then s₂.w else s₁.w
  let α₁ := s₁.w / m
  let α₂ := s₂.w / m
  { w := m
    l := α₁ * s₁.l + α₂ * s₂.l
    o := α₁ * s₁.o + α₂ * s₂.o }

/-- Global unnormalized denominator invariant `w * l`. -/
def totalDenom (s : OnlineSoftmaxState) : Rat :=
  s.w * s.l

/-- Global unnormalized numerator invariant `w * o`. -/
def totalNum (s : OnlineSoftmaxState) : Rat :=
  s.w * s.o

/-- Exact normalized attention output `o / l`. -/
def normOutput (s : OnlineSoftmaxState) : Rat :=
  s.o / s.l

/-! ### 2. Exact IEEE-754 Round-to-Nearest-Even (RNE) Rounding -/

/-- Exact IEEE-754 Round-to-Nearest-Even integer rounding of a rational `y`.
    Ties (`y = n + 1/2`) round to the even integer. -/
def rneInt (y : Rat) : Int :=
  let d : Int := (y.den : Int)
  let q : Int := y.num.ediv d
  let r : Int := y.num.emod d
  if 2 * r < d then q
  else if d < 2 * r then q + 1
  else if q % 2 == 0 then q else q + 1

/-- Exact `p`-bit IEEE-754 RNE rounding to the unit binade grid `ulp_p(1) = 2^{-(p - 1)}`. -/
def rneGrid (p : Nat) (x : Rat) : Rat :=
  (rneInt (x * pow2Rat (p - 1)) : Rat) * invPow2Rat (p - 1)

/-! ### 3. Attention-Sink Sequential (`L2R`/`DESC`) and Tree (`TREE`) Accumulators -/

/-- True collective denominator for 1 sink chunk (weight `1`) and `P - 1` bulk chunks
    each of weight `2^{-Δ}`. -/
def trueSinkDenom (Δ P : Nat) : Rat :=
  1 + ((P - 1 : Nat) : Rat) * invPow2Rat Δ

/-- Sequential `L2R` / `DESC` accumulator starting from the sink (`l = 1`) and
    sequentially adding `n` bulk chunks each of weight `2^{-Δ}` under `p`-bit RNE. -/
def l2rSinkAccum (p Δ : Nat) : Nat → Rat
  | 0 => 1
  | n + 1 => rneGrid p (l2rSinkAccum p Δ n + invPow2Rat Δ)

/-- Exact relative error `|true - approx| / true` for the sink denominator. -/
def sinkRelErr (Δ P : Nat) (approx : Rat) : Rat :=
  ratAbs (trueSinkDenom Δ P - approx) / trueSinkDenom Δ P

/-- Balanced binary tree accumulator of depth `k` (`P = 2^k` chunks: 1 sink at leaf 0
    and `2^k - 1` bulk chunks at leaves `1 .. 2^k - 1`). At tree level `j`, the
    sibling subtree of `2^j` pure bulk chunks merges exactly to mass `2^j` before
    rescaling by `2^{-Δ}` and merging into the sink path. -/
def treeSinkAccum (p Δ : Nat) : Nat → Rat
  | 0 => 1
  | k + 1 => rneGrid p (treeSinkAccum p Δ k + pow2Rat k * invPow2Rat Δ)

/-- Subnormal underflow floor `-(e_min - M) + 1` where `2^{-Δ}` underflows to zero. -/
def subnormalFloor (eMin M : Int) : Int :=
  -(eMin - M) + 1

/-- Exact balanced binary tree attention-sink vanishing threshold:
    `Δ_vanish^TREE(2^k, p, eMin, M) = min(p + k - 1, -(eMin - M) + 1)`. -/
def deltaVanishTree (k p : Nat) (eMin M : Int) : Int :=
  let ideal : Int := ((p + k - 1 : Nat) : Int)
  let sub : Int := subnormalFloor eMin M
  if ideal ≤ sub then ideal else sub

/-! ### 4. Descending-`m_i` vs Ascending-`m_i` Merge Models -/

/-- Count the number of running-maximum accumulator rescales along a sequence of
    chunk scale weights `ws`. -/
def rescaleCountAux (curMax : Rat) : List Rat → Nat
  | [] => 0
  | w :: ws =>
      if curMax < w then 1 + rescaleCountAux w ws
      else rescaleCountAux curMax ws

/-- Total accumulator rescale count for a non-empty sequence of chunk weights. -/
def rescaleCount : List Rat → Nat
  | [] => 0
  | w :: ws => rescaleCountAux w ws

/-- Predicate that a list of chunk weights is non-increasing (`DESC` order). -/
def isNonIncreasing : List Rat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b ≤ a ∧ isNonIncreasing (b :: rest)

/-- Predicate that a list of chunk weights is strictly increasing (`ASC` order). -/
def isStrictlyIncreasing : List Rat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a < b ∧ isStrictlyIncreasing (b :: rest)

/-- Sequential `p`-bit RNE online-softmax denominator merge over `(w_i, l_i)` pairs. -/
def seqMergeDenomAux (p : Nat) (curW curL : Rat) : List (Rat × Rat) → Rat
  | [] => curL
  | (w, l) :: rest =>
      if curW ≤ w then
        let rescaled := rneGrid p ((curW / w) * curL)
        seqMergeDenomAux p w (rneGrid p (rescaled + l)) rest
      else
        let rescaled := rneGrid p ((w / curW) * l)
        seqMergeDenomAux p curW (rneGrid p (curL + rescaled)) rest

/-- Sequential `p`-bit RNE online-softmax denominator merge from a non-empty chunk list. -/
def seqMergeDenom (p : Nat) : List (Rat × Rat) → Rat
  | [] => 0
  | (w, l) :: rest => seqMergeDenomAux p w l rest

/-- Exact Regime I ascending staircase chunks `[(49/64, 5/8), (7/8, 1/8), (1, 1/2)]`. -/
def regimeIChunksAsc : List (Rat × Rat) :=
  [(49 / 64, 5 / 8), (7 / 8, 1 / 8), (1, 1 / 2)]

/-- Exact Regime I descending (max-first) chunks `[(1, 1/2), (7/8, 1/8), (49/64, 5/8)]`. -/
def regimeIChunksDesc : List (Rat × Rat) :=
  [(1, 1 / 2), (7 / 8, 1 / 8), (49 / 64, 5 / 8)]

/-! ### 5. Exponent-Aligned Fixed-Point / Kulisch Accumulation & Width Bounds -/

/-- Exact integer fixed-point sum of aligned chunk contributions. -/
def fixptSum (xs : List Int) : Int :=
  xs.foldl (· + ·) 0

/-- Arbitrary binary reduction tree over values of type `α`. -/
inductive BinTree (α : Type) where
  | leaf (a : α) : BinTree α
  | node (l r : BinTree α) : BinTree α
  deriving DecidableEq

/-- Evaluate a binary reduction tree of signed integers via exact addition. -/
def BinTree.evalInt : BinTree Int → Int
  | .leaf a => a
  | .node l r => l.evalInt + r.evalInt

/-- Left-to-right fringe of a binary reduction tree. -/
def BinTree.toList : BinTree α → List α
  | .leaf a => [a]
  | .node l r => l.toList ++ r.toList

/-- Elementary list permutation relation (pure `Init`, zero Mathlib). -/
inductive ListPerm {α : Type} : List α → List α → Prop where
  | nil : ListPerm [] []
  | cons (x : α) {l₁ l₂ : List α} : ListPerm l₁ l₂ → ListPerm (x :: l₁) (x :: l₂)
  | swap (x y : α) (l : List α) : ListPerm (x :: y :: l) (y :: x :: l)
  | trans {l₁ l₂ l₃ : List α} : ListPerm l₁ l₂ → ListPerm l₂ l₃ → ListPerm l₁ l₃

/-- No-swamping + Context-Parallel invariant accumulator bit-width:
    `W_inv(k, p) = 1 (sign) + k (carry) + 1 (unit) + (p + k + 2) (frac + guard) = p + 2k + 4`,
    where `k = ceil(log_2 P)`. -/
def wInvBits (k p : Nat) : Nat :=
  1 + k + 1 + (p + k + 2)

/-- Full-span exact Kulisch accumulator bit-width across the entire finite dynamic range
    `[e_min - M, e_max]` for `P ≤ 2^k` chunks:
    `W_Kulisch(k, eMax, eMin, M) = 1 + k + (eMax - (eMin - M) + 1)`. -/
def wKulischBits (k : Nat) (eMax eMin M : Int) : Int :=
  1 + (k : Int) + (eMax - (eMin - M) + 1)

/-! ### 6. Fixed-Point Attention-Sink Quantizer & Cliff Threshold -/

/-- Quantized integer weight of a single bulk chunk `2^{-Δ}` in a `Q(F)` fixed-point
    accumulator anchored at the sink (`m_max = Δ`). -/
def fixptBulkTerm (F Δ : Nat) : Int :=
  rneInt (invPow2Rat Δ * pow2Rat F)

/-- Total fixed-point integer denominator for 1 sink chunk (`2^F`) and `2^k - 1` bulk chunks. -/
def fixptSinkIntSum (F Δ k : Nat) : Int :=
  ((2 ^ F : Nat) : Int) + ((2 ^ k - 1 : Nat) : Int) * fixptBulkTerm F Δ

/-- Reconstructed rational denominator `fixptSinkIntSum / 2^F` before final `p`-bit RNE cast. -/
def fixptSinkDenom (F Δ k : Nat) : Rat :=
  (fixptSinkIntSum F Δ k : Rat) * invPow2Rat F

/-- Final `p`-bit IEEE-754 RNE output of fixed-point sink accumulation. -/
def fixptSinkOut (p F Δ k : Nat) : Rat :=
  rneGrid p (fixptSinkDenom F Δ k)

end RingAttnKulisch
