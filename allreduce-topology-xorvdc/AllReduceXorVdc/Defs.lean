/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`allreduce-topology-xorvdc`)

Pure-`Init` (zero Mathlib) exact rational, integer, and bitwise definitions for:
1. Exact Round-to-Nearest-Even (`rneInt`, `rneGrid`, `rneAdd`) and collective topologies
   (`ringReduceFn`, `treeReduce`, `directReduce`).
2. Sub-ULP adversarial drift across Ring, Binary-Tree, and Direct All-Reduce.
3. Swamping arithmetic (`swampAdd`) and exact combinatorial catastrophic-cancellation wipeout
   counts and probabilities over all `TP * (TP - 1)` ordered `( +M, -M )` placements.
4. Zero-communication cross-rank XOR-VDC stochastic rounding thresholds, top-`K` bit extraction,
   exact stratified rank sum, discrete bias, discrete MSE, and continuous-limit MSE laws.
5. BF16 residual-stream freeze depth `L_freeze(p) = 2^(15 - 2p)` and sequential RNE accumulation.
6. 2-word compensated Kahan residual accumulation (`kahanStep`, `kahanAccum`).
7. Fixed-scale ternary quantization (`ternaryQuant`, `ternaryAdd`) and saturation barrier.
-/

namespace AllReduceXorVdc

/-! ### 1. Finite Sums, Counts, and Rational Utilities -/

def absRat (x : Rat) : Rat :=
  if x < 0 then -x else x

def sumRange : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

def sumNatRange : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumNatRange n f + f n

def countRange : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, p => countRange n p + if p n then 1 else 0

def sumListRat : List Rat → Rat
  | [] => 0
  | x :: xs => x + sumListRat xs

def discreteMean (N : Nat) (f : Nat → Rat) : Rat :=
  sumRange N f / (N : Rat)

/-! ### 2. Exact Round-to-Nearest-Even (RNE) and Collective Reduction Topologies -/

/-- Exact IEEE-754 Round-to-Nearest-Even of a rational number to the nearest integer.
    Ties (`y = n + 1/2`) round to the even integer. -/
def rneInt (y : Rat) : Int :=
  let d : Int := (y.den : Int)
  let q : Int := y.num / d
  let r : Int := y.num % d
  if 2 * r < d then q
  else if d < 2 * r then q + 1
  else if q % 2 == 0 then q else q + 1

/-- Exact RNE rounding to an integer multiple of grid spacing `u > 0`. -/
def rneGrid (u x : Rat) : Rat :=
  (rneInt (x / u) : Rat) * u

/-- Quantized RNE binary addition on grid spacing `u`. -/
def rneAdd (u a b : Rat) : Rat :=
  rneGrid u (a + b)

/-- Sequential left-to-right Ring All-Reduce over `n` ranks `f 0, ..., f (n - 1)`. -/
def ringReduceFn (op : Rat → Rat → Rat) : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | 1, f => f 0
  | n + 1, f => op (ringReduceFn op n f) (f n)

/-- Balanced Binary-Tree All-Reduce over `2^k` ranks `f 0, ..., f (2^k - 1)`. -/
def treeReduce (op : Rat → Rat → Rat) : Nat → (Nat → Rat) → Rat
  | 0, f => f 0
  | k + 1, f => op (treeReduce op k f) (treeReduce op k (fun i => f (i + 2 ^ k)))

/-- Direct 1-shot exact accumulation followed by a single final quantization `q`. -/
def directReduce (q : Rat → Rat) (n : Nat) (f : Nat → Rat) : Rat :=
  q (sumRange n f)

/-! ### 3. Pillar 1A — Adversarial Sub-ULP Drift -/

/-- Dyadic ULP `2^(-p)` on `[1, 2)` for `p` explicit mantissa bits (`p = 7` BF16, `p = 3` FP8-E4M3). -/
def dyadicUlp (p : Nat) : Rat :=
  (1 : Rat) / ((2 ^ p : Nat) : Rat)

/-- Adversarial sub-ULP drift input: rank `0` holds `1`, ranks `1..TP-1` hold `u / 2`. -/
def subUlpInput (u : Rat) (r : Nat) : Rat :=
  if r = 0 then 1 else u / 2

def exactSubUlpSum (p tp : Nat) : Rat :=
  sumRange tp (subUlpInput (dyadicUlp p))

def ringSubUlpOut (p tp : Nat) : Rat :=
  ringReduceFn (rneAdd (dyadicUlp p)) tp (subUlpInput (dyadicUlp p))

def treeSubUlpOut (p k : Nat) : Rat :=
  treeReduce (rneAdd (dyadicUlp p)) k (subUlpInput (dyadicUlp p))

def directSubUlpOut (p tp : Nat) : Rat :=
  directReduce (rneGrid (dyadicUlp p)) tp (subUlpInput (dyadicUlp p))

def ringSubUlpErr (p tp : Nat) : Rat :=
  absRat (ringSubUlpOut p tp - exactSubUlpSum p tp)

def treeSubUlpErr (p k : Nat) : Rat :=
  absRat (treeSubUlpOut p k - exactSubUlpSum p (2 ^ k))

def directSubUlpErr (p tp : Nat) : Rat :=
  absRat (directSubUlpOut p tp - exactSubUlpSum p tp)

/-! ### 4. Pillar 1B — Catastrophic Cancellation & Combinatorial Wipeout Law -/

/-- Swamping floating-point addition where `±M` absorbs any summand with `|s| ≤ bound`,
    while `+M + (-M) = 0` and small signals add normally. -/
def swampAdd (M bound a b : Rat) : Rat :=
  if a = M ∧ absRat b ≤ bound then M
  else if b = M ∧ absRat a ≤ bound then M
  else if a = -M ∧ absRat b ≤ bound then -M
  else if b = -M ∧ absRat a ≤ bound then -M
  else a + b

/-- Cancel-Swamp rank input: rank `i` holds `+M`, rank `j` holds `-M`, all other ranks hold `+δ`. -/
def cancelInput (M δ : Rat) (i j r : Nat) : Rat :=
  if r = i then M else if r = j then -M else δ

def ringCancelOut (M bound δ : Rat) (tp i j : Nat) : Rat :=
  ringReduceFn (swampAdd M bound) tp (cancelInput M δ i j)

def treeCancelOut (M bound δ : Rat) (k i j : Nat) : Rat :=
  treeReduce (swampAdd M bound) k (cancelInput M δ i j)

def directCancelOut (M δ : Rat) (tp i j : Nat) : Rat :=
  sumRange tp (cancelInput M δ i j)

/-- Number of ordered pairs `(i, j) ∈ {0, ..., n - 1}^2` with `i ≠ j` satisfying `P i j`. -/
def countOrderedPairs (n : Nat) (P : Nat → Nat → Bool) : Nat :=
  sumNatRange n (fun i => countRange n (fun j => decide (i ≠ j) && P i j))

/-- Extremal Ring wipeout predicate: `i = tp - 1 ∨ j = tp - 1`. -/
def ringWipeoutPred (tp i j : Nat) : Bool :=
  decide (i = tp - 1 ∨ j = tp - 1)

/-- Opposite-halves Tree wipeout predicate for `tp = 2 * h`: one in `[0, h)` and one in `[h, 2h)`. -/
def treeOppositeHalvesPred (h i j : Nat) : Bool :=
  decide ((i < h ∧ h ≤ j) ∨ (j < h ∧ h ≤ i))

def ringWipeoutCount (tp : Nat) : Nat :=
  countOrderedPairs tp (ringWipeoutPred tp)

def treeWipeoutCount (h : Nat) : Nat :=
  countOrderedPairs (2 * h) (treeOppositeHalvesPred h)

def directWipeoutCount (tp : Nat) : Nat :=
  countOrderedPairs tp (fun _ _ => false)

def ringWipeoutProb (tp : Nat) : Rat :=
  (ringWipeoutCount tp : Rat) / ((tp * (tp - 1) : Nat) : Rat)

def treeWipeoutProb (h : Nat) : Rat :=
  (treeWipeoutCount h : Rat) / (((2 * h) * (2 * h - 1) : Nat) : Rat)

def directWipeoutProb (tp : Nat) : Rat :=
  (directWipeoutCount tp : Rat) / ((tp * (tp - 1) : Nat) : Rat)

/-! ### 5. Pillar 2 — Cross-Rank Zero-Communication XOR-VDC Stochastic Rounding -/

/-- `k`-bit reversal of `x mod 2^k`. -/
def bitrev : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => (x % 2) * 2 ^ k + bitrev k (x / 2)

/-- Zero-communication cross-rank XOR-VDC threshold `u_r = u_0 ^^^ (bitrev_K(r) << (M - K))`. -/
def xorVdcThreshold (M K r u0 : Nat) : Nat :=
  u0 ^^^ (bitrev K r <<< (M - K))

/-- Top `K` bits of an `M`-bit integer `u`: `u / 2^(M - K)`. -/
def topBits (M K u : Nat) : Nat :=
  u / 2 ^ (M - K)

/-- Per-rank fractional SR rounding bit `1[u_r < f]`. -/
def xorVdcRankBit (M K f r u0 : Nat) : Rat :=
  if xorVdcThreshold M K r u0 < f then 1 else 0

/-- Sum of `TP = 2^K` quantized copies of fractional part `f / 2^M` under shared seed `u0`. -/
def xorVdcRankSum (M K f u0 : Nat) : Rat :=
  sumRange (2 ^ K) (fun r => xorVdcRankBit M K f r u0)

/-- Exact discrete bias of `xorVdcRankSum` over uniform `u0 ∈ {0, ..., 2^M - 1}`. -/
def xorVdcBias (M K f : Nat) : Rat :=
  discreteMean (2 ^ M) (fun u0 => xorVdcRankSum M K f u0) -
    ((2 ^ K * f : Nat) : Rat) / ((2 ^ M : Nat) : Rat)

/-- Exact discrete averaged MSE of cross-rank XOR-VDC over uniform `(f, u0) ∈ {0, ..., 2^M - 1}^2`. -/
def xorVdcDiscreteMse (M K : Nat) : Rat :=
  discreteMean (2 ^ M) (fun f =>
    discreteMean (2 ^ M) (fun u0 =>
      let e := xorVdcRankSum M K f u0 - ((2 ^ K * f : Nat) : Rat) / ((2 ^ M : Nat) : Rat)
      e * e))

/-- Exact discrete averaged MSE of independent SR across `2^K` ranks on an `M`-bit grid. -/
def indSrDiscreteMse (M K : Nat) : Rat :=
  ((2 ^ K : Nat) : Rat) *
    discreteMean (2 ^ M) (fun f =>
      let p := (f : Rat) / ((2 ^ M : Nat) : Rat)
      p * (1 - p))

/-- Exact continuous-limit averaged MSE laws on uniform `f ∈ [0, 1]`. -/
def mseRne (tp : Nat) : Rat := ((tp : Rat) * (tp : Rat)) / 12
def mseIndSr (tp : Nat) : Rat := (tp : Rat) / 6
def mseAntithetic (tp : Nat) : Rat := (tp : Rat) / 12
def mseXorVdc : Rat := 1 / 6

/-! ### 6. Pillar 3A — BF16 Residual-Stream Freeze Depth -/

/-- BF16 ULP on `[1, 2)`: `2^(-7) = 1/128`. -/
def bf16Ulp : Rat := (1 : Rat) / 128

/-- BF16 half-ULP on `[1, 2)`: `2^(-8) = 1/256`. -/
def bf16HalfUlp : Rat := (1 : Rat) / 256

/-- Exact BF16 residual-stream freeze depth `L_freeze(p) = 2^(15 - 2p)`. -/
def bf16FreezeDepth (p : Nat) : Nat :=
  2 ^ (15 - 2 * p)

/-- Sequential BF16 RNE residual stream `x_{l+1} = fl_BF16(x_l + δ)` over `L` layers. -/
def bf16ResidualAccum (x0 δ : Rat) : Nat → Rat
  | 0 => x0
  | L + 1 => rneAdd bf16Ulp (bf16ResidualAccum x0 δ L) δ

/-! ### 7. Pillar 3B — 2-Word Compensated Kahan Residual Summation -/

/-- Single 2-word Kahan step on primary grid `u` (in `+c` compensation convention):
    `y = x + c`, `t = rneGrid u (s + y)`, `c' = y - (t - s)`. -/
def kahanStep (u : Rat) (st : Rat × Rat) (x : Rat) : Rat × Rat :=
  let y := x + st.2
  let t := rneGrid u (st.1 + y)
  (t, y - (t - st.1))

/-- 2-word Kahan compensated accumulation over an arbitrary list of residual updates. -/
def kahanAccum (u s0 : Rat) (xs : List Rat) : Rat × Rat :=
  xs.foldl (kahanStep u) (s0, 0)

/-! ### 8. Pillar 1C — Fixed-Scale Ternary Saturation Barrier -/

/-- Fixed-scale ternary quantizer onto `{-S, 0, +S}` with thresholds `±S/2`. -/
def ternaryQuant (S x : Rat) : Rat :=
  if S / 2 ≤ x then S
  else if x ≤ -(S / 2) then -S
  else 0

/-- Quantized ternary binary addition. -/
def ternaryAdd (S a b : Rat) : Rat :=
  ternaryQuant S (a + b)

/-- Positive fixed-scale ternary drift input: rank `0` holds `S`, ranks `1..TP-1` hold `S / 2`. -/
def ternaryDriftInput (S : Rat) (r : Nat) : Rat :=
  if r = 0 then S else S / 2

/-- Negative fixed-scale ternary drift input: rank `0` holds `-S`, ranks `1..TP-1` hold `-S / 2`. -/
def ternaryNegDriftInput (S : Rat) (r : Nat) : Rat :=
  if r = 0 then -S else -(S / 2)

end AllReduceXorVdc
