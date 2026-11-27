/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Hilbert-Moore Corner-Glue Locality & 3-Smooth Orbits (`hilbert-moore-corner-glue-locality`)

Pure-`Init` (zero Mathlib) definitions of `BitBlockTransducer`, finite certificates (`StepBijectionCert`, `CornerGlueCert`, `MirrorSymCert`, `ClosedLoopRootCert`), `hilbert2D`, `d4Hilbert`, `hilbert3D`, `fib`, `valBase`, and `sumFin`.
-/

namespace SiliconHilbert

/-- Bitwise Hamming weight (popcount) of a natural number. -/
def popcount : Nat → Nat
  | 0 => 0
  | n + 1 => ((n + 1) % 2) + popcount ((n + 1) / 2)

/-- Exact integer absolute difference on `Nat`. -/
def natDist (a b : Nat) : Nat :=
  if a ≥ b then a - b else b - a

/-- Base-`B` trailing-zero valuation `valBase B n` (for `B ≥ 2`, `n ≥ 1`). -/
def valBase (B : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if h : B ≥ 2 ∧ (n + 1) % B = 0 then
      1 + valBase B ((n + 1) / B)
    else
      0
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) (by omega)

/-- Extract bit `i` of `n` as `0` or `1`. -/
def bitAt (n i : Nat) : Nat := (n >>> i) &&& 1

/-- Sum of `f i` for `i = 0, ..., n - 1`. -/
def sumFin (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => sumFin k f + f k

/-- An MSB-first finite-state bit-block Mealy transducer over `d`-bit blocks (`0 .. 2^d - 1`). -/
structure BitBlockTransducer (d : Nat) (S : Type) where
  delta : S → Nat → S
  omega : S → Nat → Nat
  omega_lt : ∀ s q, q < 2 ^ d → omega s q < 2 ^ d


variable {d : Nat} {S : Type}

namespace BitBlockTransducer

/-- MSB-first evaluation on width `w` returning the Morton-interleaved integer in `[0, 2^(d*w))`. -/
def evalInterleaved (T : BitBlockTransducer d S) : (w : Nat) → S → Nat → Nat
  | 0, _, _ => 0
  | w + 1, s, t =>
    let q := t / 2 ^ (d * w)
    let r := t % 2 ^ (d * w)
    T.omega s q * 2 ^ (d * w) + T.evalInterleaved w (T.delta s q) r

/-- MSB-first evaluation on width `w` returning the `i`-th coordinate in `[0, 2^w)` (`i < d`). -/
def evalCoord (T : BitBlockTransducer d S) : (w : Nat) → S → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | w + 1, s, t, i =>
    let q := t / 2 ^ (d * w)
    let r := t % 2 ^ (d * w)
    bitAt (T.omega s q) i * 2 ^ w + T.evalCoord w (T.delta s q) r i

/-- Exact `BitVec (d * w)` wrapper of `evalInterleaved`. -/
def evalBV (T : BitBlockTransducer d S) (w : Nat) (s : S) (t : BitVec (d * w)) : BitVec (d * w) :=
  BitVec.ofNat (d * w) (T.evalInterleaved w s t.toNat)

/-- `L1` distance between two points evaluated by `T`. -/
def l1Dist (T : BitBlockTransducer d S) (w : Nat) (s : S) (u v : Nat) : Nat :=
  sumFin d (fun i => natDist (T.evalCoord w s u i) (T.evalCoord w s v i))

/-- Total bitwise Hamming transition cost (popcount of coordinate-wise XOR) between `u` and `v`. -/
def hammingDist (T : BitBlockTransducer d S) (w : Nat) (s : S) (u v : Nat) : Nat :=
  sumFin d (fun i => popcount (T.evalCoord w s u i ^^^ T.evalCoord w s v i))

/-! ### Lift 1: Finite Per-State Bijection Certificate → Infinite-Width Inverse Transducer -/

structure StepBijectionCert (T : BitBlockTransducer d S) where
  omegaInv : S → Nat → Nat
  omegaInv_lt : ∀ s y, y < 2 ^ d → omegaInv s y < 2 ^ d
  left_inv : ∀ s q, q < 2 ^ d → omegaInv s (T.omega s q) = q
  right_inv : ∀ s y, y < 2 ^ d → T.omega s (omegaInv s y) = y

def invEvalInterleaved (T : BitBlockTransducer d S) (C : StepBijectionCert T) :
    (w : Nat) → S → Nat → Nat
  | 0, _, _ => 0
  | w + 1, s, y =>
    let top := y / 2 ^ (d * w)
    let lo := y % 2 ^ (d * w)
    let q := C.omegaInv s top
    q * 2 ^ (d * w) + T.invEvalInterleaved C w (T.delta s q) lo

def invEvalBV (T : BitBlockTransducer d S) (C : StepBijectionCert T) (w : Nat) (s : S)
    (y : BitVec (d * w)) : BitVec (d * w) :=
  BitVec.ofNat (d * w) (T.invEvalInterleaved C w s y.toNat)

structure CornerGlueCert (T : BitBlockTransducer d S) where
  entry : S → Nat
  exit  : S → Nat
  entry_omega : ∀ s, T.omega s 0 = entry s
  entry_delta : ∀ s, entry (T.delta s 0) = entry s
  exit_omega  : ∀ s, T.omega s (2 ^ d - 1) = exit s
  exit_delta  : ∀ s, exit (T.delta s (2 ^ d - 1)) = exit s
  /-- Unique changing coordinate axis `axis s q < d` for transition `q → q + 1`. -/
  axis : S → Nat → Nat
  axis_lt : ∀ s q, q + 1 < 2 ^ d → axis s q < d
  axis_diff : ∀ s q, q + 1 < 2 ^ d →
    bitAt (T.omega s q) (axis s q) ≠ bitAt (T.omega s (q + 1)) (axis s q)
  axis_eq_other : ∀ s q i, q + 1 < 2 ^ d → i < d → i ≠ axis s q →
    bitAt (T.omega s q) i = bitAt (T.omega s (q + 1)) i
  /-- Exact binary carry-cancellation equation: `b_i + en_i = a_i + ex_i`. -/
  glue_eq : ∀ s q i, q + 1 < 2 ^ d → i < d →
    bitAt (T.omega s (q + 1)) i + bitAt (entry (T.delta s (q + 1))) i =
    bitAt (T.omega s q) i + bitAt (exit (T.delta s q)) i

/-- Exact number of fixed points of `evalInterleaved T w s` on `[0, 2^(d*w))`. -/
def fixCount (T : BitBlockTransducer d S) (w : Nat) (s : S) : Nat :=
  sumFin (2 ^ (d * w)) (fun t => if T.evalInterleaved w s t = t then 1 else 0)

/-- Exact number of fixed points of the composition `Pi_{w, s2} ∘ Pi_{w, s1}` on `[0, 2^(d*w))`. -/
def fixCount2 (T : BitBlockTransducer d S) (w : Nat) (s1 s2 : S) : Nat :=
  sumFin (2 ^ (d * w)) (fun t => if T.evalInterleaved w s2 (T.evalInterleaved w s1 t) = t then 1 else 0)

/-- Exact number of strict 2-cycle points (`Pi^2(t) = t ∧ Pi(t) ≠ t`, i.e., `2 * #(2-cycles)`). -/
def twoCyclePts (T : BitBlockTransducer d S) (w : Nat) (s : S) : Nat :=
  sumFin (2 ^ (d * w)) (fun t =>
    if T.evalInterleaved w s (T.evalInterleaved w s t) = t ∧ T.evalInterleaved w s t ≠ t then 1 else 0)

/-- Exact `k`-fold function iteration. -/
def iter (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => iter f k (f x)

/-- A one-level root wrapper around a corner-glue transducer `T` that closes the path into a
    bijective cyclic `L1`-adjacent Hamiltonian cycle on `[0, 2^w)^d` for all `w ≥ 1`. -/
structure ClosedLoopRootCert (T : BitBlockTransducer d S) (G : CornerGlueCert T) where
  rootOmega : Nat → Nat
  rootOmegaInv : Nat → Nat
  rootDelta : Nat → S
  rootOmega_lt : ∀ q, q < 2 ^ d → rootOmega q < 2 ^ d
  rootOmegaInv_lt : ∀ y, y < 2 ^ d → rootOmegaInv y < 2 ^ d
  root_left_inv : ∀ q, q < 2 ^ d → rootOmegaInv (rootOmega q) = q
  root_right_inv : ∀ y, y < 2 ^ d → rootOmega (rootOmegaInv y) = y
  /-- Cyclic step axis for `q → (q + 1) % 2^d` (includes wrap-around `2^d - 1 → 0`!). -/
  rootAxis : Nat → Nat
  rootAxis_lt : ∀ q, q < 2 ^ d → rootAxis q < d
  rootAxis_diff : ∀ q, q < 2 ^ d →
    bitAt (rootOmega q) (rootAxis q) ≠ bitAt (rootOmega ((q + 1) % 2 ^ d)) (rootAxis q)
  rootAxis_eq_other : ∀ q i, q < 2 ^ d → i < d → i ≠ rootAxis q →
    bitAt (rootOmega q) i = bitAt (rootOmega ((q + 1) % 2 ^ d)) i
  rootGlue_eq : ∀ q i, q < 2 ^ d → i < d →
    bitAt (rootOmega ((q + 1) % 2 ^ d)) i + bitAt (G.entry (rootDelta ((q + 1) % 2 ^ d))) i =
    bitAt (rootOmega q) i + bitAt (G.exit (rootDelta q)) i

/-- Root-wrapped coordinate evaluation for width `w + 1` (`w ≥ 0`, i.e., total width `≥ 1`). -/
def evalRootCoord (T : BitBlockTransducer d S) (G : CornerGlueCert T)
    (R : ClosedLoopRootCert T G) (w : Nat) (t i : Nat) : Nat :=
  let q := t / 2 ^ (d * w)
  let r := t % 2 ^ (d * w)
  bitAt (R.rootOmega q) i * 2 ^ w + T.evalCoord w (R.rootDelta q) r i

def evalRootInterleaved (T : BitBlockTransducer d S) (G : CornerGlueCert T)
    (R : ClosedLoopRootCert T G) (w : Nat) (t : Nat) : Nat :=
  let q := t / 2 ^ (d * w)
  let r := t % 2 ^ (d * w)
  R.rootOmega q * 2 ^ (d * w) + T.evalInterleaved w (R.rootDelta q) r

def invRootInterleaved (T : BitBlockTransducer d S) (C : StepBijectionCert T)
    (G : CornerGlueCert T) (R : ClosedLoopRootCert T G) (w : Nat) (y : Nat) : Nat :=
  let top := y / 2 ^ (d * w)
  let lo := y % 2 ^ (d * w)
  let q := R.rootOmegaInv top
  q * 2 ^ (d * w) + T.invEvalInterleaved C w (R.rootDelta q) lo

def l1RootDist (T : BitBlockTransducer d S) (G : CornerGlueCert T)
    (R : ClosedLoopRootCert T G) (w u v : Nat) : Nat :=
  sumFin d (fun i => natDist (T.evalRootCoord G R w u i) (T.evalRootCoord G R w v i))

end BitBlockTransducer

/-- Standard Fibonacci sequence (`fib 0 = 0, fib 1 = 1, fib 2 = 1, fib 3 = 2, fib 4 = 3, ...`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-! ### Instantiation A: The 2D Hilbert Curve (`Fin 4` Klein-4 Automaton, `d = 2`) -/

def h2BaseOut (q : Nat) : Nat :=
  match q with
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | _ => 1

def h2ApplyV4 (s y : Nat) : Nat :=
  let inv := s / 2
  let sw := s % 2
  let bx := y % 2
  let by_ := y / 2
  let bx1 := if sw = 1 then by_ else bx
  let by1 := if sw = 1 then bx else by_
  let bx2 := if inv = 1 then 1 - bx1 else bx1
  let by2 := if inv = 1 then 1 - by1 else by1
  bx2 + 2 * by2

def h2Omega (s : Fin 4) (q : Nat) : Nat :=
  h2ApplyV4 s.val (h2BaseOut q)

def h2Delta (s : Fin 4) (q : Nat) : Fin 4 :=
  let inv := s.val / 2
  let sw := s.val % 2
  match q with
  | 0 => ⟨inv * 2 + (1 - sw), by omega⟩
  | 3 => ⟨(1 - inv) * 2 + (1 - sw), by omega⟩
  | _ => s

/-- Generic bounded `List.all` reflection helper for `Fin n`. -/
def checkFin (n : Nat) (P : Fin n → Bool) : Bool :=
  (List.finRange n).all P

theorem of_checkFin (n : Nat) (P : Fin n → Bool) (h : checkFin n P = true) :
    ∀ s : Fin n, P s = true := by
  intro s; unfold checkFin at h; rw [List.all_eq_true] at h; exact h s (List.mem_finRange s)

def checkFinNat (n m : Nat) (P : Fin n → Nat → Bool) : Bool :=
  (List.finRange n).all fun s => (List.range m).all fun q => P s q

theorem of_checkFinNat (n m : Nat) (P : Fin n → Nat → Bool) (h : checkFinNat n m P = true) :
    ∀ (s : Fin n) (q : Nat), q < m → P s q = true := by
  intro s q hq; unfold checkFinNat at h; rw [List.all_eq_true] at h
  have hs := h s (List.mem_finRange s); rw [List.all_eq_true] at hs
  exact hs q (List.mem_range.mpr hq)

def checkFinNat2 (n m k : Nat) (P : Fin n → Nat → Nat → Bool) : Bool :=
  (List.finRange n).all fun s => (List.range m).all fun q => (List.range k).all fun i => P s q i

theorem of_checkFinNat2 (n m k : Nat) (P : Fin n → Nat → Nat → Bool) (h : checkFinNat2 n m k P = true) :
    ∀ (s : Fin n) (q i : Nat), q < m → i < k → P s q i = true := by
  intro s q i hq hi; unfold checkFinNat2 at h; rw [List.all_eq_true] at h
  have hs := h s (List.mem_finRange s); rw [List.all_eq_true] at hs
  have hsq := hs q (List.mem_range.mpr hq); rw [List.all_eq_true] at hsq
  exact hsq i (List.mem_range.mpr hi)

def hilbert2D : BitBlockTransducer 2 (Fin 4) where
  delta := h2Delta
  omega := h2Omega
  omega_lt := fun s q hq =>
    of_decide_eq_true (of_checkFinNat 4 4 (fun s q => decide (h2Omega s q < 4)) (by decide) s q hq)

/-- Finite bijection certificate for 2D Hilbert (kernel-checked by `decide`). -/
def h2OmegaInv (s : Fin 4) (y : Nat) : Nat :=
  let y0 := h2ApplyV4 s.val y
  match y0 with
  | 0 => 0
  | 2 => 1
  | 3 => 2
  | _ => 3

def hilbert2D_bijCert : hilbert2D.StepBijectionCert where
  omegaInv := h2OmegaInv
  omegaInv_lt := fun s y hy =>
    of_decide_eq_true (of_checkFinNat 4 4 (fun s y => decide (h2OmegaInv s y < 4)) (by decide) s y hy)
  left_inv := fun s q hq =>
    of_decide_eq_true (of_checkFinNat 4 4 (fun s q => decide (h2OmegaInv s (h2Omega s q) = q)) (by decide) s q hq)
  right_inv := fun s y hy =>
    of_decide_eq_true (of_checkFinNat 4 4 (fun s y => decide (h2Omega s (h2OmegaInv s y) = y)) (by decide) s y hy)

def d4Apply (s y : Nat) : Nat :=
  let fx := s / 4
  let fy := (s / 2) % 2
  let sw := s % 2
  let bx := y % 2
  let by_ := y / 2
  let bx1 := if sw = 1 then by_ else bx
  let by1 := if sw = 1 then bx else by_
  let bx2 := if fx = 1 then 1 - bx1 else bx1
  let by2 := if fy = 1 then 1 - by1 else by1
  bx2 + 2 * by2

def d4Omega (s : Fin 8) (q : Nat) : Nat :=
  d4Apply s.val (h2BaseOut q)

def d4Delta (s : Fin 8) (q : Nat) : Fin 8 :=
  let fx := s.val / 4
  let fy := (s.val / 2) % 2
  let sw := s.val % 2
  match q with
  | 0 => ⟨fx * 4 + fy * 2 + (1 - sw), by omega⟩
  | 3 => ⟨(1 - fx) * 4 + (1 - fy) * 2 + (1 - sw), by omega⟩
  | _ => s

def d4Hilbert : BitBlockTransducer 2 (Fin 8) where
  delta := d4Delta
  omega := d4Omega
  omega_lt := fun s q hq =>
    of_decide_eq_true (of_checkFinNat 8 4 (fun s q => decide (d4Omega s q < 4)) (by decide) s q hq)

def d4OmegaInv (s : Fin 8) (y : Nat) : Nat :=
  let fx := s.val / 4
  let fy := (s.val / 2) % 2
  let sw := s.val % 2
  let bx := y % 2
  let by_ := y / 2
  let bx1 := if fx = 1 then 1 - bx else bx
  let by1 := if fy = 1 then 1 - by_ else by_
  let bx2 := if sw = 1 then by1 else bx1
  let by2 := if sw = 1 then bx1 else by1
  match bx2 + 2 * by2 with
  | 0 => 0
  | 2 => 1
  | 3 => 2
  | _ => 3

def d4Hilbert_bijCert : d4Hilbert.StepBijectionCert where
  omegaInv := d4OmegaInv
  omegaInv_lt := fun s y hy =>
    of_decide_eq_true (of_checkFinNat 8 4 (fun s y => decide (d4OmegaInv s y < 4)) (by decide) s y hy)
  left_inv := fun s q hq =>
    of_decide_eq_true (of_checkFinNat 8 4 (fun s q => decide (d4OmegaInv s (d4Omega s q) = q)) (by decide) s q hq)
  right_inv := fun s y hy =>
    of_decide_eq_true (of_checkFinNat 8 4 (fun s y => decide (d4Omega s (d4OmegaInv s y) = y)) (by decide) s y hy)

def d4Axis (s : Fin 8) (q : Nat) : Nat :=
  let sw := s.val % 2
  match q with
  | 1 => if sw = 1 then 1 else 0
  | _ => if sw = 1 then 0 else 1

def d4Hilbert_glueCert : d4Hilbert.CornerGlueCert where
  entry := fun s => d4Omega s 0
  exit := fun s => d4Omega s 3
  entry_omega := fun _ => rfl
  entry_delta := fun s =>
    of_decide_eq_true (of_checkFin 8 (fun s => decide (d4Omega (d4Delta s 0) 0 = d4Omega s 0)) (by decide) s)
  exit_omega := fun _ => rfl
  exit_delta := fun s =>
    of_decide_eq_true (of_checkFin 8 (fun s => decide (d4Omega (d4Delta s 3) 3 = d4Omega s 3)) (by decide) s)
  axis := d4Axis
  axis_lt := fun s q hq =>
    of_decide_eq_true (of_checkFinNat 8 3 (fun s q => decide (d4Axis s q < 2)) (by decide) s q (by omega))
  axis_diff := fun s q hq =>
    of_decide_eq_true (of_checkFinNat 8 3
      (fun s q => decide (bitAt (d4Omega s q) (d4Axis s q) ≠ bitAt (d4Omega s (q + 1)) (d4Axis s q)))
      (by decide) s q (by omega))
  axis_eq_other := fun s q i hq hi hne =>
    of_decide_eq_true (of_checkFinNat2 8 3 2
      (fun s q i => decide (i = d4Axis s q ∨ bitAt (d4Omega s q) i = bitAt (d4Omega s (q + 1)) i))
      (by decide) s q i (by omega) hi) |>.resolve_left hne
  glue_eq := fun s q i hq hi =>
    of_decide_eq_true (of_checkFinNat2 8 3 2
      (fun s q i => decide (bitAt (d4Omega s (q + 1)) i + bitAt (d4Omega (d4Delta s (q + 1)) 0) i =
                            bitAt (d4Omega s q) i + bitAt (d4Omega (d4Delta s q) 3) i))
      (by decide) s q i (by omega) hi)

def moore2D_rootCert : d4Hilbert.ClosedLoopRootCert d4Hilbert_glueCert where
  rootOmega := h2BaseOut
  rootOmegaInv := fun y => match y with | 0 => 0 | 2 => 1 | 3 => 2 | _ => 3
  rootDelta := fun q => match q with | 0 => ⟨5, by decide⟩ | 1 => ⟨5, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨3, by decide⟩
  rootOmega_lt := by intro q hq; rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> decide
  rootOmegaInv_lt := by intro y hy; rcases (by omega : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3) with rfl | rfl | rfl | rfl <;> decide
  root_left_inv := by intro q hq; rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> decide
  root_right_inv := by intro y hy; rcases (by omega : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3) with rfl | rfl | rfl | rfl <;> decide
  rootAxis := fun q => match q with | 0 => 1 | 1 => 0 | 2 => 1 | _ => 0
  rootAxis_lt := by intro q hq; rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> decide
  rootAxis_diff := by intro q hq; rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> decide
  rootAxis_eq_other := by
    intro q i hq hi hne
    rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp_all [h2BaseOut, bitAt]
  rootGlue_eq := by
    intro q i hq hi
    rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide

def rotl3 (x r : Nat) : Nat :=
  let r' := r % 3
  (((x <<< r') ||| (x >>> (3 - r'))) &&& 7)

def gray3 (q : Nat) : Nat := q ^^^ (q >>> 1)

def h3EntrySub (q : Nat) : Nat :=
  match q with
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 3
  | 4 => 3 | 5 => 6 | 6 => 6 | _ => 5

def h3RotSub (q : Nat) : Nat :=
  match q with
  | 0 => 1 | 1 => 2 | 2 => 2 | 3 => 0
  | 4 => 0 | 5 => 2 | 6 => 2 | _ => 1

def h3Omega (s : Fin 24) (q : Nat) : Nat :=
  let e := s.val / 3
  let r := s.val % 3
  rotl3 (gray3 q) r ^^^ e

def h3Delta (s : Fin 24) (q : Nat) : Fin 24 :=
  let e := s.val / 3
  let r := s.val % 3
  let ne := e ^^^ rotl3 (h3EntrySub q) r
  let nr := (r + h3RotSub q) % 3
  ⟨(ne &&& 7) * 3 + nr, by
    have h1 : (ne &&& 7) < 8 := by
      have : ne &&& 7 ≤ 7 := Nat.and_le_right
      omega
    have h2 : nr < 3 := Nat.mod_lt _ (by omega)
    omega⟩

/-- Helper to discharge `∀ s : Fin 24, ∀ q < 8, P s q` cleanly via bounded `Nat` reflection. -/
def checkAll24x8 (P : Fin 24 → Nat → Bool) : Bool :=
  (List.finRange 24).all fun s => (List.range 8).all fun q => P s q

theorem of_checkAll24x8 (P : Fin 24 → Nat → Bool) (h : checkAll24x8 P = true) :
    ∀ (s : Fin 24) (q : Nat), q < 8 → P s q = true := by
  intro s q hq
  unfold checkAll24x8 at h
  rw [List.all_eq_true] at h
  have hs := h s (List.mem_finRange s)
  rw [List.all_eq_true] at hs
  exact hs q (List.mem_range.mpr hq)

def hilbert3D : BitBlockTransducer 3 (Fin 24) where
  delta := h3Delta
  omega := h3Omega
  omega_lt := by
    intro s q hq
    have hc := of_checkAll24x8 (fun s q => decide (h3Omega s q < 8)) (by decide) s q hq
    exact of_decide_eq_true hc

end SiliconHilbert
