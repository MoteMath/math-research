/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for the CA Torsion / Lyapunov Flux Compiler (`ca-torsion-lyapunov-flux-compiler`)

Pure-`Init` (zero Mathlib) definitions: periodic bitrings `BitVec w`, sliding windows, the
one-dimensional binary cellular-automaton step `caStep k off rule` and its iterate `caIter`,
the pure-data potential/flux certificate `CACert` with its kernel-decidable verifiers
(`checkConservation`, `checkModConservation`, `checkLyapunov`, `checkStrictLyapunov`),
the ring potential `ringPotential`, and the nine concrete certificates used by the
headline theorems.
-/

namespace CAFluxCompiler

/-- Pack the first `w` bits of `f : Nat → Bool` into a `Nat < 2^w`. -/
def packBits (w : Nat) (f : Nat → Bool) : Nat :=
  match w with
  | 0 => 0
  | w' + 1 => packBits w' f + if f w' then 2 ^ w' else 0

/-- Construct a `BitVec w` from a bit predicate `f : Nat → Bool`. -/
def bvOfFn (w : Nat) (f : Nat → Bool) : BitVec w :=
  BitVec.ofNat w (packBits w f)

/-- Bit at arbitrary position `i : Nat` on a periodic bitring `x : BitVec w`. -/
def ringBit {w : Nat} (x : BitVec w) (i : Nat) : Bool :=
  x.getLsbD (i % w)

/-- Cyclic left rotation by `s` cells: `(ringRot s x)_i = x_{i + s}`. -/
def ringRot (s : Nat) {w : Nat} (x : BitVec w) : BitVec w :=
  bvOfFn w (fun i => ringBit x (i + s))

/-- LSB-first `m`-bit sliding window starting at ring position `i`:
    `window m x i = ∑_{j=0}^{m-1} (ringBit x (i+j)) * 2^j`. -/
def window (m : Nat) {w : Nat} (x : BitVec w) (i : Nat) : Nat :=
  match m with
  | 0 => 0
  | m' + 1 => (if ringBit x i then 1 else 0) + 2 * window m' x (i + 1)

/-- Pure-silicon bit-slice extraction: `p` bits starting at offset `a`. -/
def subWin (u a p : Nat) : Nat :=
  (u / (2 ^ a)) % (2 ^ p)

/-- One synchronous CA step with stencil width `k`, center offset `off`, and
    `2^k`-bit rule lookup table `rule : Nat`.
    Cell `i` reads the `k`-bit window starting at `i - off (mod w)`. -/
def caStep (k off rule : Nat) {w : Nat} (x : BitVec w) : BitVec w :=
  bvOfFn w (fun i => rule.testBit (window k x (i + w - (off % w))))

/-- Iterated CA evolution `T^t(x)`. -/
def caIter (k off rule : Nat) : Nat → {w : Nat} → BitVec w → BitVec w
  | 0, _, x => x
  | t + 1, _, x => caStep k off rule (caIter k off rule t x)

/-- Pure finite function computing the `p`-bit next window from a `(p + k - 1)`-bit input word `u`. -/
def nextWindowAux (k rule : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | p' + 1, j, u =>
    (if rule.testBit (subWin u j k) then 1 else 0) + 2 * nextWindowAux k rule p' (j + 1) u

def nextWindow (k rule p u : Nat) : Nat :=
  nextWindowAux k rule p 0 u

/-- Pure-silicon 2-step rule compiler: composes a `k=3` CA rule with itself into a `k=5` rule. -/
def compose2Rule (rule : Nat) : Nat :=
  packBits 32 (fun u => rule.testBit (nextWindow 3 rule 3 u))

/-- Exact integer sum `∑_{i=0}^{n-1} f(i)`. -/
def sumRange (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | n' + 1 => sumRange n' f + f n'

/-- Minimum and maximum of a table `f : Nat → Int` on `{0, ..., n-1}`. -/
def rangeMin (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | m + 1 => if m == 0 then f 0 else min (rangeMin m f) (f m)

def rangeMax (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | m + 1 => if m == 0 then f 0 else max (rangeMax m f) (f m)

/-- Pure-data sliding-window potential-flux certificate (ZERO `Prop` fields!).
    - `k`, `off`, `rule`: CA stencil width, center offset, and `2^k`-bit truth table
    - `p`, `align`, `phi`: potential width, alignment offset, and `2^p`-entry integer table
    - `q`, `psi`: flux/gauge width and `2^q`-entry integer table
    - `M`: verification window width satisfying `M ≥ max(p + k - 1, q + 1, k, align + p)` -/
structure CACert where
  k     : Nat
  off   : Nat
  rule  : Nat
  p     : Nat
  align : Nat
  phi   : List Int
  q     : Nat
  psi   : List Int
  M     : Nat
  deriving Repr, DecidableEq

/-- Lookup table entry with total default `0`. -/
def tableAt (tbl : List Int) (u : Nat) : Int :=
  tbl.getD u 0

/-- Potential summed over an open segment `[0, n)` starting at `start`. -/
def segPotential (p : Nat) (phi : List Int) {w : Nat} (x : BitVec w) (start n : Nat) : Int :=
  sumRange n (fun i => tableAt phi (window p x (i + start)))

/-- Global potential `Φ(x) = ∑_{i=0}^{w-1} φ(W_p(x, i))` on a periodic bitring of length `w`. -/
def ringPotential (p : Nat) (phi : List Int) {w : Nat} (x : BitVec w) : Int :=
  sumRange w (fun i => tableAt phi (window p x i))

/-- Shifted Hamming distance `d_H(rot_off(y), rot_cmp(x))` counted across the `w` ring cells. -/
def shiftHammingDist (off cmp : Nat) {w : Nat} (y x : BitVec w) : Nat :=
  (sumRange w (fun i => if ringBit y (i + off) != ringBit x (i + cmp) then 1 else 0)).toNat

/-- Shifted equality predicate: `rot_off(y) = rot_cmp(x)`.
    When `cmp = off`, this is equivalent to `y = x`.
    When `cmp = off + s`, `y = ringRot s x` (left-moving traveling wave of speed `s`). -/
def shiftEq (off cmp : Nat) {w : Nat} (y x : BitVec w) : Prop :=
  ringRot off y = ringRot cmp x

/-- Pointwise local defect `Δ(u) = φ(next(u)) - φ(old(u)) + ψ(u[1..q]) - ψ(u[0..q-1])`. -/
def localDelta (cert : CACert) (u : Nat) : Int :=
  let nw   := nextWindow cert.k cert.rule cert.p u
  let ow   := subWin u cert.align cert.p
  let psi1 := tableAt cert.psi (subWin u 1 cert.q)
  let psi0 := tableAt cert.psi (subWin u 0 cert.q)
  tableAt cert.phi nw - tableAt cert.phi ow + psi1 - psi0

/-- Structural well-formedness check on window widths (purely Boolean). -/
def checkWidths (cert : CACert) : Bool :=
  (cert.k ≥ 1) && (cert.p ≥ 1) && (cert.q ≥ 1) &&
  (cert.p + cert.k ≤ cert.M + 1) &&
  (cert.q + 1 ≤ cert.M) &&
  (cert.align + cert.p ≤ cert.M) &&
  (cert.k ≤ cert.M)

/-- Exhaustive bounded loop checker for `∀ u < n, pred u = true`. -/
def checkAll (n : Nat) (pred : Nat → Bool) : Bool :=
  match n with
  | 0 => true
  | n' + 1 => checkAll n' pred && pred n'

/-- Mode A verifier: exact integer conservation (`Δ(u) = 0` for all `2^M` windows). -/
def checkConservation (cert : CACert) : Bool :=
  checkWidths cert &&
  checkAll (2 ^ cert.M) (fun u => localDelta cert u == 0)

/-- Mode B verifier: exact modular `Z/dZ` torsion conservation (`Δ(u) % d = 0`). -/
def checkModConservation (cert : CACert) (d : Nat) : Bool :=
  checkWidths cert && (d ≥ 1) &&
  checkAll (2 ^ cert.M) (fun u => (localDelta cert u) % (d : Int) == 0)

/-- Mode C verifier: monotonic Lyapunov inequality (`Δ(u) ≤ 0`). -/
def checkLyapunov (cert : CACert) : Bool :=
  checkWidths cert &&
  checkAll (2 ^ cert.M) (fun u => decide (localDelta cert u ≤ 0))

/-- Mode D verifier: strict shift-equivariant Hamming-dissipation certificate.
    Checks `-Δ(u) ≥ c` whenever the next bit `f(u[0..k-1])` differs from `u[cmp]`,
    and `-Δ(u) ≥ 0` otherwise. -/
def checkStrictLyapunov (cert : CACert) (cmp c : Nat) : Bool :=
  checkWidths cert && (cmp < cert.M) && (c ≥ 1) &&
  checkAll (2 ^ cert.M) (fun u =>
    let changed := cert.rule.testBit (subWin u 0 cert.k) != u.testBit cmp
    let req : Int := if changed then (c : Int) else 0
    decide (-localDelta cert u ≥ req))

/-- Potential spread `max(φ) - min(φ)` computed finitely from `cert`. -/
def phiSpread (cert : CACert) : Nat :=
  (rangeMax (2 ^ cert.p) (tableAt cert.phi) -
   rangeMin (2 ^ cert.p) (tableAt cert.phi)).toNat

/-- Linear convergence time bound `N_max(w) = (spread * w) / c`. -/
def maxTransient (cert : CACert) (c w : Nat) : Nat :=
  (phiSpread cert * w) / c

def cert_pat101_0xac8c : CACert := {
  k     := 4
  off   := 1
  rule  := 0xac8c
  p     := 3
  align := 1
  phi   := [0, 0, 0, 0, 0, 1, 0, 0]
  q     := 4
  psi   := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
  M     := 6
}

def cert_walls_0x04ce : CACert := {
  k     := 4
  off   := 1
  rule  := 0x04ce
  p     := 2
  align := 1
  phi   := [0, 1, 1, 0]
  q     := 4
  psi   := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1]
  M     := 5
}

def cert_strict_fp_0x2c48 : CACert := {
  k     := 4
  off   := 1
  rule  := 0x2c48
  p     := 2
  align := 1
  phi   := [0, 3, 4, 3]
  q     := 3
  psi   := [0, 0, 0, 0, 0, 0, 0, 2]
  M     := 5
}

def cert_tw_rule152 : CACert := {
  k     := 3
  off   := 1
  rule  := 152
  p     := 2
  align := 1
  phi   := [0, 1, 0, 3]
  q     := 2
  psi   := [0, 0, -1, 1]
  M     := 4
}

def cert_micro_cons_0xf0e0 : CACert := {
  k     := 4
  off   := 1
  rule  := 0xf0e0
  p     := 2
  align := 1
  phi   := [0, 0, 0, 1]
  q     := 3
  psi   := [0, 0, 0, 0, 0, 0, -1, -1]
  M     := 5
}

def cert_micro_lyap_0xf0e0 : CACert := {
  k     := 4
  off   := 1
  rule  := 0xf0e0
  p     := 2
  align := 1
  phi   := [0, 1, 0, 0]
  q     := 3
  psi   := [0, 0, -1, -1, 0, 0, 0, 0]
  M     := 5
}

def cert_blinker_rule108 : CACert := {
  k     := 5
  off   := 2
  rule  := compose2Rule 108
  p     := 2
  align := 2
  phi   := [0, 1, 0, 1]
  q     := 1
  psi   := [0, 0]
  M     := 6
}

def cert_mod3_0xb0f0 : CACert := {
  k     := 4
  off   := 1
  rule  := 0xb0f0
  p     := 2
  align := 1
  phi   := [0, 1, 0, 2]
  q     := 4
  psi   := [0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 2, 1]
  M     := 5
}

def cert_mod2_0x83bc : CACert := {
  k     := 4
  off   := 1
  rule  := 0x83bc
  p     := 2
  align := 1
  phi   := [0, 1, 0, 1]
  q     := 3
  psi   := [0, 0, 0, 0, 1, 1, 1, 0]
  M     := 5
}

end CAFluxCompiler
