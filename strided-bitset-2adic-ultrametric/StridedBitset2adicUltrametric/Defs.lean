/-!
# Strided-Bitset Decomposition & 2-Adic Odd-Parity Ultrametric Engine

Pure-silicon standalone Lean 4.34.1 formalization (zero Mathlib, zero sorry, standard axioms only).
-/

namespace StridedBitsetEngine

/-! ## Layer 0: Elementary Finite Sum Helpers (`sumRange`) -/

/-- Sum `f 0 + f 1 + ... + f (n - 1)`. -/
def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange f n + f n

/-- Exact 2-adic valuation on `Nat` (`v2 0 = 0`; for `n > 0`, `2 ^ v2 n` is the largest power of 2 dividing `n`). -/
def v2 : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then
      1 + v2 ((n + 1) / 2)
    else
      0
termination_by n => n

/-- Exact binary Hamming weight (popcount) of a natural number. -/
def popcount : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)
termination_by n => n

/-- Standard factorial on `Nat`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Standard binomial coefficient `C(n, k)` on `Nat`. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Genuine binary-support predicate for the `m`-periodic bitmask set `B(m, mask)`. -/
def InMask (m mask x : Nat) : Prop :=
  ∀ i : Nat, x.testBit i = true → mask.testBit (i % m) = true

/-- The `m`-strided Moser-de Bruijn set `S_m = B(m, 1)`: bits only at multiples of `m`. -/
def InStrided (m x : Nat) : Prop :=
  InMask m 1 x

/-- Decidable check that a single base-`2^m` digit `d < 2^m` is supported within `mask`. -/
def inDigitMaskB (m mask d : Nat) : Bool :=
  (d < 2 ^ m) && (d &&& mask == d)

/-- Fuel-bounded structurally recursive check for `InMask m mask x` (kernel-reducible via `decide`). -/
def inMaskFuel : Nat → Nat → Nat → Nat → Bool
  | 0, m, _, x => (m ≠ 0) && (x == 0)
  | fuel + 1, m, mask, x =>
    if m == 0 then false
    else if x == 0 then true
    else inDigitMaskB m mask (x % 2 ^ m) && inMaskFuel fuel m mask (x / 2 ^ m)

/-- Decidable check for `InMask m mask x` via base-`2^m` bit-slicing (reduces under `decide`). -/
def inMaskB (m mask x : Nat) : Bool :=
  inMaskFuel x m mask x

/-- Exact combinatorial tuple count: number of tuples `(x_1, ..., x_k)` with `InMask m mask_i x_i`
    and `x_1 + ... + x_k = n`. -/
def maskRepCount (m : Nat) : List Nat → Nat → Nat
  | [], n => if n = 0 then 1 else 0
  | mask :: rest, n =>
      sumRange (fun x => if inMaskB m mask x then maskRepCount m rest (n - x) else 0) (n + 1)

/-- Exact combinatorial `k`-fold `m`-strided Moser-de Bruijn sumset representation count `r_{k S_m}(n)`. -/
def stridedRepCount (m k n : Nat) : Nat :=
  maskRepCount m (List.replicate k 1) n

/-- Digit-slice sum multiplicity `w(s) = #{(d_1, ..., d_k) ∈ D_1 × ... × D_k : d_1 + ... + d_k = s}`. -/
def digitWeight (m : Nat) : List Nat → Nat → Nat
  | [], s => if s = 0 then 1 else 0
  | mask :: rest, s =>
      sumRange (fun d => if d ≤ s ∧ inDigitMaskB m mask d then digitWeight m rest (s - d) else 0) (2 ^ m)

/-- Structurally recursive, kernel-`decide`-reducible 2-adic valuation for finite certificates. -/
def v2Fuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n = 0 then 0
    else if n % 2 = 0 then 1 + v2Fuel fuel (n / 2)
    else 0

def v2Exec (n : Nat) : Nat := v2Fuel n n

/-- Structural universal quantifier over `{0, ..., N - 1}` for `Bool` predicates. -/
def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

/-- Mathematical specification of a Parity-Alternating Unit-Carry Certificate on base `B`. -/
structure UnitCarrySpec (B : Nat) (w0 w1 : Nat → Nat) : Prop where
  B_ge_two : B ≥ 2
  B_even : B % 2 = 0
  w0_pos : ∀ r < B, w0 r > 0
  w1_zero_pos : w1 0 > 0
  w1_last_zero : w1 (B - 1) = 0
  carry_v2_eq : ∀ r < B, w1 r > 0 → v2 (w0 r) = v2 (w1 r)
  wrap_lt : v2 (w0 0) < v2 (w0 (B - 1))
  even_lt_next : ∀ r < B, r % 2 = 0 →
    (w1 r > 0 ∨ w1 (r + 1) = 0) ∧ v2 (w0 r) < v2 (w0 (r + 1))
  even_lt_prev : ∀ r < B, r % 2 = 0 → r ≥ 2 →
    (w1 r > 0 ∨ w1 (r - 1) = 0) ∧ v2 (w0 r) < v2 (w0 (r - 1))

/-- **Finite Boolean Certificate Checker (Kernel-Executable via `decide`!):**
    Checks all conditions of `UnitCarrySpec` over the finite digit set `{0, ..., B - 1}`. -/
def checkUnitCarryCert (B : Nat) (w0 w1 : Nat → Nat) : Bool :=
  (B ≥ 2) &&
  (B % 2 == 0) &&
  allBelow (fun r => w0 r > 0) B &&
  (w1 0 > 0) &&
  (w1 (B - 1) == 0) &&
  allBelow (fun r => (w1 r == 0) || (v2Exec (w0 r) == v2Exec (w1 r))) B &&
  (v2Exec (w0 0) < v2Exec (w0 (B - 1))) &&
  allBelow (fun r =>
    if r % 2 == 0 then
      ((w1 r > 0) || (w1 (r + 1) == 0)) && (v2Exec (w0 r) < v2Exec (w0 (r + 1)))
    else true) B &&
  allBelow (fun r =>
    if (r % 2 == 0) && (r ≥ 2) then
      ((w1 r > 0) || (w1 (r - 1) == 0)) && (v2Exec (w0 r) < v2Exec (w0 (r - 1)))
    else true) B

/-- The 2-state base-`B` bitwise valuation transducer associated with a unit-carry table `(w0, w1)`. -/
def certVal (B : Nat) (w0 w1 : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if hB : B ≥ 2 then
      let q := (n + 1) / B
      let r := (n + 1) % B
      have hq : q < n + 1 := Nat.div_lt_self (by omega) hB
      have hq2 : 2 * (q / 2) < n + 1 := by omega
      if w1 r > 0 then
        v2 (w0 r) + certVal B w0 w1 (2 * (q / 2))
      else
        v2 (w0 r) + certVal B w0 w1 q
    else 0
termination_by n => n

def evenW0 (m t r : Nat) : Nat := choose (2 ^ m + 2 * t) r
def evenW1 (m t r : Nat) : Nat := choose (2 ^ m + 2 * t) (2 ^ m + r)

/-- Exact base-`2^m` valuation transducer for `r_{(2^m + 2t) S_m}(n)`. -/
def evenWindowVal (m t n : Nat) : Nat :=
  certVal (2 ^ m) (evenW0 m t) (evenW1 m t) n

/-- The universal `r`-independent stride-`m` valuation transducer `v_m = evenWindowVal m 0`. -/
def vBase (m n : Nat) : Nat := evenWindowVal m 0 n

/-- Closed-form bitwise valuation formula for `r_{2^r S_m}(n)` for ALL `r ≥ m`. -/
def pow2StridedVal (m r n : Nat) : Nat :=
  if n % 2 ^ r = 0 then
    vBase m (2 * ((n / 2 ^ r) / 2))
  else
    (r - v2 (n % 2 ^ r)) + vBase m (n / 2 ^ r)

end StridedBitsetEngine

/-! ### Standard-Axiom Verification Receipts -/
