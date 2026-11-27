/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`stern-walsh-carry-resonance`)

Stern diatomic sequence, Calkin-Wilf SL2(Z) tree matrices, Walsh-Hadamard monomial lifter, carry-orbit lifter and mod-3 resonance laws.
-/

namespace SternCW


/-! ## Section 0: Core Exact Integer Linear Algebra & Bitwise Primitives -/

structure Vec2 where
  x : Int
  y : Int
  deriving DecidableEq, Repr

structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, Repr

def Vec2.add (u v : Vec2) : Vec2 := ⟨u.x + v.x, u.y + v.y⟩
def Vec2.smul (s : Int) (u : Vec2) : Vec2 := ⟨s * u.x, s * u.y⟩
def Vec2.zero : Vec2 := ⟨0, 0⟩

def Mat2.id : Mat2 := ⟨1, 0, 0, 1⟩
def Mat2.add (M N : Mat2) : Mat2 := ⟨M.a + N.a, M.b + N.b, M.c + N.c, M.d + N.d⟩
def Mat2.mul (M N : Mat2) : Mat2 :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩
def Mat2.mulV (M : Mat2) (v : Vec2) : Vec2 :=
  ⟨M.a * v.x + M.b * v.y, M.c * v.x + M.d * v.y⟩
def Lmat (a : Int) : Mat2 := ⟨1, 0, a, 1⟩
def Rmat (a : Int) : Mat2 := ⟨1, a, 0, 1⟩
def ePlus : Vec2 := ⟨1, 1⟩

/-- Finite sum of `Vec2` over `x ∈ {0, ..., n - 1}`. -/
def sumVec : Nat → (Nat → Vec2) → Vec2
  | 0, _ => Vec2.zero
  | n + 1, f => (sumVec n f).add (f n)

/-- Finite sum of `Int` over `x ∈ {0, ..., n - 1}`. -/
def sumInt : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumInt n f + f n

/-- Binary popcount (Hamming weight). -/
def popcount : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)

/-- Thue-Morse sign `(-1)^(popcount n)`. -/
def tmSign (n : Nat) : Int :=
  if popcount n % 2 = 0 then 1 else -1

/-- Bitwise AND defined recursively by LSB splitting. -/
def bitAnd : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 0
  | a + 1, b + 1 => ((a + 1) % 2) * ((b + 1) % 2) + 2 * bitAnd ((a + 1) / 2) ((b + 1) / 2)

/-- Inverse Gray code `igray m = m ^^^ (m >>> 1) ^^^ (m >>> 2) ^^^ ...` -/
def igray : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) ^^^ igray ((n + 1) / 2)

/-! ## Section 1: Stern's Diatomic Sequence & Calkin-Wilf `SL₂(ℤ)` Binary Tree -/

/-- Stern's diatomic sequence `s(0)=0, s(1)=1, s(2n)=s(n), s(2n+1)=s(n)+s(n+1)`. -/
def stern : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then
      stern ((n + 2) / 2)
    else
      stern ((n + 2) / 2) + stern ((n + 2) / 2 + 1)
termination_by n => n

/-- General binary-tree matrix walk `M_{x_0} M_{x_1} ... M_{x_{k-1}}` for `k`-bit index `x`. -/
def treeMat (M0 M1 : Mat2) : Nat → Nat → Mat2
  | 0, _ => Mat2.id
  | k + 1, x => (if x % 2 = 0 then M0 else M1).mul (treeMat M0 M1 k (x / 2))

def cwMat (a : Int) (k x : Nat) : Mat2 := treeMat (Lmat a) (Rmat a) k x
def cwVec (a : Int) (k x : Nat) : Vec2 := (cwMat a k x).mulV ePlus

/-- Exact level-`k` Walsh-Hadamard transform of the binary-tree walk `(M₀, M₁, v₀)`. -/
def walshSum (M0 M1 : Mat2) (v0 : Vec2) (k m : Nat) : Vec2 :=
  sumVec (2 ^ k) (fun x => ((treeMat M0 M1 k x).mulV v0).smul (tmSign (bitAnd x m)))

/-- Exact Gray-exponent counters for the Hadamard monomialization spectrum. -/
def expPlus (k m : Nat) : Nat := k - popcount (m ||| igray m)
def expMinus (m : Nat) : Nat := popcount (m ||| igray m) - popcount m

/-- Triangular sign `(-1)^(p*(p+1)/2)` extracted from the first coordinate of `rotBasis ePlus eMinus p`. -/
def triSign (p : Nat) : Int :=
  if (p * (p + 1) / 2) % 2 = 0 then 1 else -1

/-- The Carry-Shifted Thue-Morse Stern Vector at shift `c` and level `k`:
    `V_c(k) = ∑_{x < 2^k} (-1)^pop(x + c) • (s(2^k + x), s(2^k + x + 1))`. -/
def carrySternVec (c k : Nat) : Vec2 :=
  sumVec (2 ^ k) (fun x => (cwVec 1 k x).smul (tmSign (x + c)))

def carrySternF (c k : Nat) : Int := (carrySternVec c k).x
def carrySternG (c k : Nat) : Int := (carrySternVec c k).y

/-! ## Section 4: Reusable Infinite Proof Engine III — `Sym²` Spectral-Collapse & Left-Kernel Conservation Lifter -/

structure Vec3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

structure Mat3 where
  r1 : Vec3
  r2 : Vec3
  r3 : Vec3
  deriving DecidableEq, Repr

def Vec3.zero : Vec3 := ⟨0, 0, 0⟩
def Vec3.add (u v : Vec3) : Vec3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def Vec3.smul (s : Int) (u : Vec3) : Vec3 := ⟨s * u.x, s * u.y, s * u.z⟩
def Vec3.dot (u v : Vec3) : Int := u.x * v.x + u.y * v.y + u.z * v.z

def Mat3.mulV (M : Mat3) (v : Vec3) : Vec3 :=
  ⟨M.r1.dot v, M.r2.dot v, M.r3.dot v⟩

def sumVec3 : Nat → (Nat → Vec3) → Vec3
  | 0, _ => Vec3.zero
  | n + 1, f => (sumVec3 n f).add (f n)

def vec2Sym2 (v : Vec2) : Vec3 := ⟨v.x * v.x, v.x * v.y, v.y * v.y⟩

/-- Level-`k` quadratic Thue-Morse Stern vector
    `(∑ (-1)^pop(x) s(2^k+x)², ∑ (-1)^pop(x) s(2^k+x)s(2^k+x+1), ∑ (-1)^pop(x) s(2^k+x+1)²)`. -/
def quadSternVec (k : Nat) : Vec3 :=
  sumVec3 (2 ^ k) (fun x => (vec2Sym2 (cwVec 1 k x)).smul (tmSign x))

end SternCW
