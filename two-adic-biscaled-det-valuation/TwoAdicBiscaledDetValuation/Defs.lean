/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`two-adic-biscaled-det-valuation`)

Exact 2-Adic Valuation Biscaled Elimination Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace SpecMat12


/-! ## Section 1: Exact Finite Sums, Products, and Integer Matrix Determinants -/

abbrev Mat (n : Nat) := Fin n → Fin n → Int

def sumFin : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n)

def prodFin : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 1
  | n + 1, f => prodFin (fun i : Fin n => f i.castSucc) * f (Fin.last n)

def sumNat : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumNat (fun i : Fin n => f i.castSucc) + f (Fin.last n)

def skipIdx {n : Nat} (c : Fin (n + 1)) (j : Fin n) : Fin (n + 1) :=
  if h : j.val < c.val then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩

def skipPair {n : Nat} (c₁ c₂ : Fin (n + 2)) (k : Fin n) : Fin (n + 2) :=
  let lo := min c₁.val c₂.val
  let hi := max c₁.val c₂.val
  if h1 : k.val < lo then ⟨k.val, by omega⟩
  else if h2 : k.val + 1 < hi then ⟨k.val + 1, by omega⟩
  else ⟨k.val + 2, by omega⟩

def idMat (n : Nat) : Mat n := fun i j => if i = j then 1 else 0

def matMul {n : Nat} (A B : Mat n) : Mat n :=
  fun i j => sumFin (fun k => A i k * B k j)

def matAdd {n : Nat} (A B : Mat n) : Mat n :=
  fun i j => A i j + B i j

def transpose {n : Nat} (A : Mat n) : Mat n :=
  fun i j => A j i

def setRow {n : Nat} (A : Mat n) (r : Fin n) (v : Fin n → Int) : Mat n :=
  fun i j => if i = r then v j else A i j

def swapRows {n : Nat} (A : Mat n) (r₁ r₂ : Fin n) : Mat n :=
  fun i j => if i = r₁ then A r₂ j else if i = r₂ then A r₁ j else A i j

def signNat (k : Nat) : Int := if k % 2 = 0 then 1 else -1

def minorLast {n : Nat} (A : Mat (n + 1)) (c : Fin (n + 1)) : Mat n :=
  fun i j => A i.castSucc (skipIdx c j)

def det : {n : Nat} → Mat n → Int
  | 0, _ => 1
  | n + 1, A =>
    sumFin (fun j : Fin (n + 1) =>
      signNat (n + j.val) * A (Fin.last n) j * det (minorLast A j))

def scaleCol {n : Nat} (A : Mat n) (k : Fin n) (c : Int) : Mat n :=
  fun i j => if j = k then c * A i j else A i j

def stdBasis {n : Nat} (c : Fin n) : Fin n → Int :=
  fun j => if j = c then 1 else 0

def basisMat {n : Nat} (f : Fin n → Fin n) : Mat n :=
  fun i => stdBasis (f i)

def biScale {n : Nat} (a b : Fin n → Nat) (Ω : Mat n) : Mat n :=
  fun i j => (2 : Int) ^ (a i + b j) * Ω i j

def HasV2 (x : Int) (v : Nat) : Prop :=
  ∃ u : Int, u % 2 = 1 ∧ x = (2 : Int) ^ v * u


def popFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else n % 2 + popFuel fuel (n / 2)

def pop (n : Nat) : Nat := popFuel n n

/-- Exact 2-adic valuation `v_2(x + 1)` = number of trailing `1`-bits of `x` (structurally reducible!). -/
def v2SuccFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n % 2 = 1 then 1 + v2SuccFuel fuel (n / 2) else 0

def v2Succ (n : Nat) : Nat := v2SuccFuel n n

/-- Bitwise submask relation: `u ⊆ i` iff `(u &&& i) = u`. -/
def submask (u i : Nat) : Bool := (u &&& i) == u

/-- Bitwise set difference `v \ u = v &&& ~u = v ^^^ (u &&& v)` (width-independent on `Nat`). -/
def bitDiff (v u : Nat) : Nat := v ^^^ (u &&& v)

def mobCoeff (i u : Nat) : Int :=
  if submask u i then signNat (pop (i ^^^ u)) else 0

def mobMat (n : Nat) : Mat n :=
  fun i u => mobCoeff i.val u.val

/-- Exact finite sum `∑_{u=0}^{m-1} f u` on `Nat`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | m + 1, f => sumRange m f + f m

/-- Width-independent 1D Möbius sum `mob1 g i = ∑_{u ≤ i} mobCoeff i u * g u`. -/
def mob1 (g : Nat → Int) (i : Nat) : Int :=
  sumRange (i + 1) (fun u => mobCoeff i u * g u)

/-- Width-independent 2D Möbius transform `mob2 F i j`. -/
def mob2 (F : Nat → Nat → Int) (i j : Nat) : Int :=
  mob1 (fun u => mob1 (fun v => F u v) j) i

/-- Closed-form Möbius transform `WKernel a i j` of `a^{v_2((u ^^^ v) + 1)}`. -/
def WKernel (a : Int) (i j : Nat) : Int :=
  if i = 0 ∧ j = 0 then 1
  else
    let m := i ||| j
    if ((m + 1) &&& m) = 0 then
      (a - 1) * a ^ (pop m - 1) * (-2 : Int) ^ (pop (i &&& j))
    else 0


/-! ### Matrix Families, Binary Weight Sum `popSum`, and Bi-Scaling Profiles -/

def popSum (n : Nat) : Nat := sumNat (fun i : Fin n => pop i.val)

def rowExp (e i : Nat) : Nat := if i ≤ 1 then 0 else (e * pop i) / 2

def colExp (e j : Nat) : Nat := if j ≤ 1 then 0 else (e * pop j + 1) / 2

/-- Pure Hybrid Ultrametric–Bitwise Matrix:
    `N_n(a, q)_{i,j} = a^{v_2((i ^^^ j) + 1)} + q^{pop(i &&& j)}`. -/
def hybridMat (a q : Int) (n : Nat) : Mat n :=
  fun i j => a ^ v2Succ (i.val ^^^ j.val) + q ^ pop (i.val &&& j.val)

/-- Asymmetric Dense 2-Adically Dominated Bitwise Perturbation:
    `Δ_n(λ, c, d)_{i,j} = 2 * λ * c^{pop(j \ i)} * d^{pop(i &&& j)}`. -/
def asymPertMat (lam c d : Int) (n : Nat) : Mat n :=
  fun i j => (2 * lam) * (c ^ pop (bitDiff j.val i.val) * d ^ pop (i.val &&& j.val))

/-- Full 5-Parameter Non-Symmetric Bitwise Matrix Family: `M_n = N_n + Δ_n`. -/
def fullHybridMat (a q lam c d : Int) (n : Nat) : Mat n :=
  matAdd (hybridMat a q n) (asymPertMat lam c d n)

/-! ### Mask-Size & Parity Helper Lemmas -/

/-- Exact quotient entry `Ω_{e,r}(u_a, u_q, i, j)` satisfying
    `(mobMat * hybridMat (2^r * u_a) (1 + 2^e * u_q) * mobMat^T)_{i,j} = 2^(rowExp e i + colExp e j) * Ω`. -/
def omegaEntry (e r : Nat) (u_a u_q : Int) (i j : Nat) : Int :=
  let a : Int := (2 : Int) ^ r * u_a
  let m := i ||| j
  let wTerm : Int :=
    if i = 0 ∧ j = 0 then 1
    else if ((m + 1) &&& m) = 0 then
      let vW := r * (pop m - 1) + pop (i &&& j)
      (2 : Int) ^ (vW - (rowExp e i + colExp e j)) *
        ((a - 1) * u_a ^ (pop m - 1) * (-1 : Int) ^ pop (i &&& j))
    else 0
  let dTerm : Int :=
    if i = j then
      if i = 0 then 1
      else if i = 1 then (2 : Int) ^ e * u_q
      else u_q ^ pop i
    else 0
  wTerm + dTerm

/-- Exact `2 × 2` corner `F_2`-inverse for the Supercritical Regime: `[[0, 1], [1, 0]]`. -/
def R_super2 : Mat 2 := fun i j => if i.val + j.val = 1 then 1 else 0

/-- Exact universal mod-2 corner matrix for Critical Regime I (`e = 1, r = 1`, `k ≤ 8`). -/
def cornerCrit1 (k : Nat) : Mat k :=
  fun i j =>
    ((if i.val = 0 ∧ j.val = 0 then (1 : Int)
      else if (((i.val ||| j.val) + 1) &&& (i.val ||| j.val)) = 0 then
        if (pop (i.val ||| j.val) - 1) + pop (i.val &&& j.val) -
          (rowExp 1 i.val + colExp 1 j.val) = 0 then 1 else 0
      else 0) +
     (if i.val = j.val then if i.val = 0 then 1 else if i.val = 1 then 0 else 1 else 0)) % 2

/-- Explicit `F_2`-left-inverse certificates `R_k` for `k = 2, 3, 4, 5, 6, 7, 8` (synthesized by `explore_and_verify.py`). -/
def matFromList {k : Nat} (rows : List (List Int)) : Mat k :=
  fun i j => (rows.getD i.val []).getD j.val 0

def R_crit1 (k : Nat) : Mat k :=
  match k with
  | 2 => matFromList [[0,1],[1,0]]
  | 3 => matFromList [[0,1,1],[1,0,0],[0,0,1]]
  | 4 => matFromList [[0,1,1,0],[1,1,0,1],[0,0,1,0],[0,1,0,1]]
  | 5 => matFromList [[0,1,1,0,0],[1,1,0,1,1],[0,0,1,0,0],[0,1,0,1,1],[0,0,0,0,1]]
  | 6 => matFromList [[0,1,1,0,0,0],[1,1,0,1,1,0],[0,0,1,0,0,0],[0,1,0,1,1,0],[0,0,0,0,1,0],[0,0,1,0,0,1]]
  | 7 => matFromList [[0,1,1,0,0,0,0],[1,1,0,1,1,0,0],[0,0,1,0,0,0,0],[0,1,0,1,1,0,0],[0,0,0,0,1,0,0],[0,0,1,0,0,1,0],[0,0,0,0,0,0,1]]
  | 8 => matFromList [[0,1,1,0,0,0,0,0],[1,1,0,1,1,0,0,1],[0,0,1,0,0,0,0,0],[0,1,0,1,1,0,0,0],[0,0,0,0,1,0,0,0],[0,0,1,0,0,1,0,0],[0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,1]]
  | m => idMat m

def cornerCrit2 (k : Nat) : Mat k :=
  fun i j =>
    ((if i.val = 0 ∧ j.val = 0 then (1 : Int)
      else if (((i.val ||| j.val) + 1) &&& (i.val ||| j.val)) = 0 then
        if 2 * (pop (i.val ||| j.val) - 1) + pop (i.val &&& j.val) -
          (rowExp 2 i.val + colExp 2 j.val) = 0 then 1 else 0
      else 0) +
     (if i.val = j.val then if i.val = 0 then 1 else if i.val = 1 then 0 else 1 else 0)) % 2

def R_crit2 (k : Nat) : Mat k :=
  match k with
  | 2 => matFromList [[0,1],[1,0]]
  | 3 => matFromList [[0,1,0],[1,0,0],[0,0,1]]
  | 4 => matFromList [[0,1,0,0],[1,1,1,1],[0,1,0,1],[0,1,1,1]]
  | m => idMat m

end SpecMat12
