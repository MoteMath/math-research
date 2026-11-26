/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Public Definitions for `moe-bias-placement-codes`

Pure-`Init` (zero Mathlib) definitions for:
1. Finite sums over `Fin n` (`sumFinNat`, `sumFinRat`, `countBool`, `sumFinRatSubset`).
2. DeepSeek-V3 aux-loss-free sign-bias dynamics (`meanLoad`, `signBiasDelta`, `meanCenteredDelta`).
3. Intra-GPU co-located pair counts (`twiceIntraPairs`).
4. Explicit finite fields `GF(4) = GF(2)[x]/(x^2 + x + 1)` and `GF(8) = GF(2)[x]/(x^3 + x + 1)`
   and Resolvable Affine Plane `AG(2, 4)` / `AG(2, 8)` expert-to-GPU placement maps.
-/

namespace MoeBiasPlacement

/-- Exact sum of a `Nat`-valued function over `Fin n`. -/
def sumFinNat : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumFinNat (fun i : Fin n => f i.castSucc) + f (Fin.last n)

/-- Exact sum of a `Rat`-valued function over `Fin n`. -/
def sumFinRat : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumFinRat (fun i : Fin n => f i.castSucc) + f (Fin.last n)

/-- Cardinality of a decidable subset `S : Fin n → Bool`. -/
def countBool {n : Nat} (S : Fin n → Bool) : Nat :=
  sumFinNat (fun i => if S i then 1 else 0)

/-- Sum of `w i` over indices `i` with `S i = true`. -/
def sumFinRatSubset {n : Nat} (S : Fin n → Bool) (w : Fin n → Rat) : Rat :=
  sumFinRat (fun i => if S i then w i else 0)

/-- Sum of `c i` over indices `i` with `S i = true`. -/
def sumFinNatSubset {n : Nat} (S : Fin n → Bool) (c : Fin n → Nat) : Nat :=
  sumFinNat (fun i => if S i then c i else 0)

/-- Rational mean load `(∑ i, L i) / E`. -/
def meanLoad {E : Nat} (L : Fin E → Rat) : Rat :=
  sumFinRat L / (E : Rat)

/-- DeepSeek-V3 aux-loss-free sign-bias update step for expert `i`. -/
def signBiasDelta {E : Nat} (γ : Rat) (L : Fin E → Rat) (i : Fin E) : Rat :=
  let Lbar := meanLoad L
  if L i < Lbar then γ else if Lbar < L i then -γ else 0

/-- Mean-centered sign-bias update step preserving `∑ delta = 0` and all pairwise differences. -/
def meanCenteredDelta {E : Nat} (γ : Rat) (L : Fin E → Rat) (i : Fin E) : Rat :=
  signBiasDelta γ L i - sumFinRat (signBiasDelta γ L) / (E : Rat)

/-- Twice the total intra-GPU co-located expert pair count `∑ g, c g * (c g - 1) = 2 * ∑ C(c g, 2)`. -/
def twiceIntraPairs {f : Nat} (c : Fin f → Nat) : Nat :=
  sumFinNat (fun g => c g * (c g - 1))

/-! ## Finite Fields `GF(4)` and `GF(8)` and Affine Planes `AG(2, 4)`, `AG(2, 8)` -/

/-- Addition in `GF(4) = GF(2)[x]/(x^2 + x + 1)` (bitwise XOR on 2-bit polynomials). -/
def gf4Add (a b : Fin 4) : Fin 4 :=
  ⟨(a.val ^^^ b.val) % 4, Nat.mod_lt _ (by decide)⟩

/-- Multiplication in `GF(4) = GF(2)[x]/(x^2 + x + 1)`. -/
def gf4Mul (a b : Fin 4) : Fin 4 :=
  match a.val, b.val with
  | 0, _ | _, 0 => ⟨0, by decide⟩
  | 1, y => ⟨y % 4, Nat.mod_lt _ (by decide)⟩
  | x, 1 => ⟨x % 4, Nat.mod_lt _ (by decide)⟩
  | 2, 2 => ⟨3, by decide⟩
  | 2, 3 => ⟨1, by decide⟩
  | 3, 2 => ⟨1, by decide⟩
  | 3, 3 => ⟨2, by decide⟩
  | _, _ => ⟨0, by decide⟩

/-- Addition in `GF(8) = GF(2)[x]/(x^3 + x + 1)` (bitwise XOR on 3-bit polynomials). -/
def gf8Add (a b : Fin 8) : Fin 8 :=
  ⟨(a.val ^^^ b.val) % 8, Nat.mod_lt _ (by decide)⟩

/-- Carryless polynomial multiplication mod `x^3 + x + 1` (`0b1011 = 11`) in `GF(8)`. -/
def gf8Mul (a b : Fin 8) : Fin 8 :=
  let step := fun (acc : Nat) (bit : Nat) =>
    let shifted := acc <<< 1
    let reduced := if shifted &&& 8 != 0 then shifted ^^^ 11 else shifted
    if (b.val >>> bit) &&& 1 != 0 then reduced ^^^ a.val else reduced
  let r2 := step 0 2
  let r1 := step r2 1
  let r0 := step r1 0
  ⟨r0 % 8, Nat.mod_lt _ (by decide)⟩

/-- `AG(2, 4)` expert-to-GPU placement map: expert `(x, y) ∈ GF(4)^2` maps to GPU `x ∈ Fin 4`. -/
def ag24Gpu (p : Fin 4 × Fin 4) : Fin 4 := p.1

/-- `AG(2, 4)` vertical line `x = c` (`4` experts). -/
def ag24VerticalLine (c : Fin 4) (y : Fin 4) : Fin 4 × Fin 4 := (c, y)

/-- `AG(2, 4)` non-vertical (transverse) affine line `y = m * x + b` (`4` experts). -/
def ag24TransverseLine (m b : Fin 4) (x : Fin 4) : Fin 4 × Fin 4 :=
  (x, gf4Add (gf4Mul m x) b)

/-- `AG(2, 8)` expert-to-GPU placement map: expert `(x, y) ∈ GF(8)^2` maps to GPU `x ∈ Fin 8`. -/
def ag28Gpu (p : Fin 8 × Fin 8) : Fin 8 := p.1

/-- `AG(2, 8)` vertical line `x = c` (`8` experts). -/
def ag28VerticalLine (c : Fin 8) (y : Fin 8) : Fin 8 × Fin 8 := (c, y)

/-- `AG(2, 8)` non-vertical (transverse) affine line `y = m * x + b` (`8` experts). -/
def ag28TransverseLine (m b : Fin 8) (x : Fin 8) : Fin 8 × Fin 8 :=
  (x, gf8Add (gf8Mul m x) b)

end MoeBiasPlacement
