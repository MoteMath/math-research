/-
  adic-16: Evil/Odious & Mod-m Bit-Weight Class Additive/Bitwise Engine
  ======================================================================
  Standalone Lean 4.36.0 formalization (pure core Lean, kernel-verified).

  Contains TWO reusable pure-silicon infinite proof mechanisms and their
  flagship infinite theorems, sharpness counterexamples, non-vacuity witnesses,
  and hostile mutation tests:

  ENGINE I — Involutive Ring Base-2^m Circulant Carry-Transfer Compiler
    * General lifting theorem (`hermitian_row0_telescope_symm`):
      For any m >= 1, d >= 1, any rev-Hermitian matrix H over Z[Z/mZ], and any
      vector v with row-0 telescoping H 0 j = delta_{0,j} e_0 + rev(v j),
      (H^k v)_0 is rev-palindromic for ALL k in Nat.
    * General exact orbit-lumping theorem (`orbit_lumping_sound`).
    * Theorem 1 (`mersenne_popcount_palindromy`):
      FOR ALL m >= 1, k >= 0, r < m:
        #{n < 2^(m*k) : s2((2^m - 1)*n) == r (mod m)}
          = #{n < 2^(m*k) : s2((2^m - 1)*n) == (m - r) % m (mod m)}.
    * Theorem 1b (`mersenne_mod3_recurrence`, `mersenne_mod3_strict_dominance`):
      For m=3 (c=7), D3(k) = c0(2^(3k)) - c1(2^(3k)) = c0(2^(3k)) - c2(2^(3k))
      satisfies D3(k+3) = 4*D3(k+2) + 4*D3(k+1) - D3(k) and D3(k) >= 4^k > 0
      for ALL k >= 0.
    * Theorem 1c (`mersenne_mod6_dominance_breaks_at_2_pow_72`):
      Kernel-checked sharp phase-transition refutation via exact 13-orbit lumping:
        m=6, c=63, k=12 (N = 2^72): c0(2^72) - c2(2^72) = -4543260596431345 < 0.

  ENGINE II — Pure-Data 2-Window Bit-Splitting Polyhedral Cone Certificate Engine
    * General 2-window bit-splitting theorem (`windowVec_two_mul`, `windowVec_two_mul_add_one`)
      for arbitrary consistent finite-state LSB parity transducers.
    * Pure-data Farkas polyhedral cone checker `checkConeCert` + general infinite
      soundness theorem (`coneCert_sound`):
        checkConeCert tr cert = true -> ∀ N >= 1, ∀ i, (C * W(N))_i >= 1.
    * Theorem 2 (`or_mul5_strict_evil_dominance`):
      FOR ALL N >= 1, #{n < N : s2(n ||| 5*n) even} > #{n < N : s2(n ||| 5*n) odd}.
    * Theorem 2b (`or_mul5_tribonacci_law`):
      FOR ALL k >= 1, sum_{n < 2^k} (-1)^s2(n ||| 5*n) = 2 * tribonacci (k + 1).
    * Theorem 3 (`or_mul3_strict_evil_dominance`):
      FOR ALL N >= 1, #{n < N : s2(n ||| 3*n) even} > #{n < N : s2(n ||| 3*n) odd}.
    * Theorem 4 (`mul3_newman_benchmark`):
      Classical Newman (1969) s2(3*n) mod 2 recovered in 9 cone rows as benchmark.
    * Hostile mutation tests + 3-way sharpness counterexamples + non-vacuity witnesses.
-/

set_option autoImplicit false

namespace Adic16

-- ============================================================================
-- SECTION 0: ELEMENTARY BINARY PRIMITIVES (STRUCTURAL RECURSION FOR KERNEL REDUCE)
-- ============================================================================

/-- Structurally recursive fuel-based popcount so Lean 4 kernel `decide` reduces it natively. -/
def popcountFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else (n % 2) + popcountFuel fuel (n / 2)

/-- Exact binary popcount `s_2(n)`. -/
def popcount (n : Nat) : Nat := popcountFuel n n

/-- Exact count of `0 ≤ n < N` with `f n % m = r % m`. -/
def countMod : Nat → Nat → Nat → (Nat → Nat) → Nat
  | 0, _, _, _ => 0
  | N + 1, m, r, f => countMod N m r f + if f N % m = r % m then 1 else 0

/-- Exact integer sum `∑_{0 ≤ n < N} f n`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | N + 1, f => sumRange N f + f N

def paritySign (n : Nat) : Int :=
  if n % 2 = 0 then 1 else -1

/-- Exact finite sum over `Fin d`. -/
def sumFin (d : Nat) (f : Fin d → Int) : Int :=
  sumRange d (fun i => if h : i < d then f ⟨i, h⟩ else 0)

/-- Elements of the exact integer group ring `Z[Z/mZ]`. -/
abbrev GR (m : Nat) := Fin m → Int

def grZero (m : Nat) : GR m := fun _ => 0

def grAdd {m : Nat} (a b : GR m) : GR m := fun r => a r + b r

def grUnit {m : Nat} (s : Nat) : GR m :=
  fun r => if r.val = s % m then 1 else 0

/-- Group-ring involution `rev(a)_r = a_{(-r) mod m}`. -/
def grRev {m : Nat} (hm : 0 < m) (a : GR m) : GR m :=
  fun r => a ⟨(m - r.val) % m, Nat.mod_lt _ hm⟩

/-- Exact cyclic convolution product in `Z[Z/mZ]`. -/
def grMul {m : Nat} (hm : 0 < m) (a b : GR m) : GR m :=
  fun r => sumFin m (fun i => a i * b ⟨(r.val + m - i.val) % m, Nat.mod_lt _ hm⟩)

/-- Matrix and vector operations over `GR m`. -/
def grSumFin {m : Nat} (d : Nat) (f : Fin d → GR m) : GR m :=
  fun r => sumFin d (fun i => f i r)

abbrev GRMat (d m : Nat) := Fin d → Fin d → GR m
abbrev GRVec (d m : Nat) := Fin d → GR m

def grMatVec {d m : Nat} (hm : 0 < m) (A : GRMat d m) (v : GRVec d m) : GRVec d m :=
  fun i => grSumFin d (fun j => grMul hm (A i j) (v j))

def grMatMul {d m : Nat} (hm : 0 < m) (A B : GRMat d m) : GRMat d m :=
  fun i k => grSumFin d (fun j => grMul hm (A i j) (B j k))

def grMatId {d m : Nat} : GRMat d m :=
  fun i j => if i = j then grUnit 0 else grZero m

def grMatPow {d m : Nat} (hm : 0 < m) (A : GRMat d m) : Nat → GRMat d m
  | 0 => grMatId
  | k + 1 => grMatMul hm A (grMatPow hm A k)

def grQuadForm {d m : Nat} (hm : 0 < m) (v : GRVec d m) (A : GRMat d m) : GR m :=
  grSumFin d (fun i => grSumFin d (fun j => grMul hm (grRev hm (v i)) (grMul hm (A i j) (v j))))

def IsRevHermitian {d m : Nat} (hm : 0 < m) (A : GRMat d m) : Prop :=
  ∀ i j : Fin d, A j i = grRev hm (A i j)

/-- The `(2^m - 1) × (2^m - 1)` circulant carry-transfer matrix `H_m` over `Z[Z/mZ]`. -/
def mersenneH (m : Nat) : GRMat (2 ^ m - 1) m :=
  fun g gp =>
    if g = gp then
      grAdd (grUnit 0) (grUnit 0)
    else
      grUnit (popcount ((g.val + (2 ^ m - 1) - gp.val) % (2 ^ m - 1)))

/-- Initial carry-weight vector `v_0(g) = e_{s_2(g) mod m}`. -/
def mersenneV0 (m : Nat) : GRVec (2 ^ m - 1) m :=
  fun g => grUnit (popcount g.val)

def orb3 (g : Fin 7) : Fin 3 :=
  if g.val = 0 then ⟨0, by decide⟩
  else if g.val = 1 ∨ g.val = 2 ∨ g.val = 4 then ⟨1, by decide⟩
  else ⟨2, by decide⟩

def matOrb3 : GRMat 3 3
  | ⟨0, _⟩, ⟨0, _⟩ => fun r => if r.val = 0 then 2 else 0
  | ⟨0, _⟩, ⟨1, _⟩ => fun r => if r.val = 2 then 3 else 0
  | ⟨0, _⟩, ⟨2, _⟩ => fun r => if r.val = 1 then 3 else 0
  | ⟨1, _⟩, ⟨0, _⟩ => fun r => if r.val = 1 then 1 else 0
  | ⟨1, _⟩, ⟨1, _⟩ => fun r => if r.val = 0 then 2 else 1
  | ⟨1, _⟩, ⟨2, _⟩ => fun r => if r.val = 0 then 0 else if r.val = 1 then 1 else 2
  | ⟨2, _⟩, ⟨0, _⟩ => fun r => if r.val = 2 then 1 else 0
  | ⟨2, _⟩, ⟨1, _⟩ => fun r => if r.val = 0 then 0 else if r.val = 1 then 2 else 1
  | ⟨2, _⟩, ⟨2, _⟩ => fun r => if r.val = 0 then 2 else 1

def v0Orb3 : GRVec 3 3
  | ⟨0, _⟩ => grUnit 0
  | ⟨1, _⟩ => grUnit 1
  | ⟨2, _⟩ => grUnit 2

/-- The 3-state integer recurrence `(A_k, u_k, v_k)` for Mod-3 Mersenne excess `D_3(k)`. -/
def D3State : Nat → Int × Int × Int
  | 0 => (1, 1, 1)
  | k + 1 =>
    let (A, u, v) := D3State k
    (2 * A + 3 * u + 3 * v, A + 2 * v, A + u + 2 * v)

/-- Excess `D_3(k) = c_0(2^(3k)) - c_1(2^(3k))` for `s_2(7n) mod 3`. -/
def mersenneMod3Excess (k : Nat) : Int :=
  (countMod (2 ^ (3 * k)) 3 0 (fun n => popcount (7 * n)) : Int) -
  (countMod (2 ^ (3 * k)) 3 1 (fun n => popcount (7 * n)) : Int)

/-- Canonical cyclic orbit minimum under `g ↦ 2*g mod 63`. -/
def canonOrb6 (g : Nat) : Nat :=
  let g1 := (2 * g) % 63
  let g2 := (2 * g1) % 63
  let g3 := (2 * g2) % 63
  let g4 := (2 * g3) % 63
  let g5 := (2 * g4) % 63
  min g (min g1 (min g2 (min g3 (min g4 g5))))

def orb6Idx (c : Nat) : Nat :=
  match c with
  | 0 => 0  | 1 => 1  | 3 => 2  | 5 => 3  | 7 => 4  | 9 => 5  | 11 => 6
  | 13 => 7 | 15 => 8 | 21 => 9 | 23 => 10 | 27 => 11 | 31 => 12 | _ => 0

def orb6 (g : Fin 63) : Fin 13 :=
  ⟨orb6Idx (canonOrb6 g.val), by revert g; decide⟩

def orb6RepFin (i : Fin 13) : Fin 63 :=
  match i.val with
  | 0 => ⟨0, by decide⟩   | 1 => ⟨1, by decide⟩   | 2 => ⟨3, by decide⟩
  | 3 => ⟨5, by decide⟩   | 4 => ⟨7, by decide⟩   | 5 => ⟨9, by decide⟩
  | 6 => ⟨11, by decide⟩  | 7 => ⟨13, by decide⟩  | 8 => ⟨15, by decide⟩
  | 9 => ⟨21, by decide⟩  | 10 => ⟨23, by decide⟩ | 11 => ⟨27, by decide⟩
  | _ => ⟨31, by decide⟩

abbrev Vec6 := Int × Int × Int × Int × Int × Int

def v6Zero : Vec6 := (0, 0, 0, 0, 0, 0)

def v6Add (a b : Vec6) : Vec6 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1, a.2.2.2.2.1 + b.2.2.2.2.1, a.2.2.2.2.2 + b.2.2.2.2.2)

def v6Mul (a b : Vec6) : Vec6 :=
  let (a0, a1, a2, a3, a4, a5) := a
  let (b0, b1, b2, b3, b4, b5) := b
  ( a0*b0 + a1*b5 + a2*b4 + a3*b3 + a4*b2 + a5*b1,
    a0*b1 + a1*b0 + a2*b5 + a3*b4 + a4*b3 + a5*b2,
    a0*b2 + a1*b1 + a2*b0 + a3*b5 + a4*b4 + a5*b3,
    a0*b3 + a1*b2 + a2*b1 + a3*b0 + a4*b5 + a5*b4,
    a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0 + a5*b5,
    a0*b5 + a1*b4 + a2*b3 + a3*b2 + a4*b1 + a5*b0 )

def v6Get (v : Vec6) (r : Fin 6) : Int :=
  match r.val with
  | 0 => v.1 | 1 => v.2.1 | 2 => v.2.2.1 | 3 => v.2.2.2.1 | 4 => v.2.2.2.2.1 | _ => v.2.2.2.2.2

def v6OfGR (f : GR 6) : Vec6 :=
  (f ⟨0, by decide⟩, f ⟨1, by decide⟩, f ⟨2, by decide⟩, f ⟨3, by decide⟩, f ⟨4, by decide⟩, f ⟨5, by decide⟩)

/-- Exact literal 13 × 13 orbit-lumped matrix `M_6` over `Z[Z/6Z]` (verified against `mersenneH 6` below!). -/
def matOrb6Data : List (List Vec6) := [
  [(2,0,0,0,0,0), (0,0,0,0,0,6), (0,0,0,0,6,0), (0,0,0,0,6,0), (0,0,0,6,0,0), (0,0,0,0,3,0), (0,0,0,6,0,0), (0,0,0,6,0,0), (0,0,6,0,0,0), (0,0,0,2,0,0), (0,0,6,0,0,0), (0,0,3,0,0,0), (0,6,0,0,0,0)],
  [(0,1,0,0,0,0), (2,1,1,1,1,1), (0,1,1,1,1,2), (0,0,1,1,2,2), (0,1,1,1,3,0), (0,0,0,1,1,1), (0,0,1,2,3,0), (0,0,1,2,3,0), (0,1,1,4,0,0), (0,0,0,1,1,0), (0,0,2,4,0,0), (0,0,1,2,0,0), (0,1,5,0,0,0)],
  [(0,0,1,0,0,0), (0,2,1,1,1,1), (2,0,2,1,2,0), (0,1,0,3,1,1), (0,0,2,2,0,2), (0,0,1,0,2,0), (0,1,0,3,1,1), (0,0,1,3,1,1), (0,0,3,0,3,0), (0,0,1,0,1,0), (0,1,1,2,2,0), (0,0,1,1,1,0), (0,1,1,4,0,0)],
  [(0,0,1,0,0,0), (0,2,2,1,1,0), (0,1,1,3,0,1), (2,0,2,1,2,0), (0,0,3,1,1,1), (0,1,0,1,0,1), (0,0,2,0,3,1), (0,1,0,2,2,1), (0,1,1,2,2,0), (0,0,0,1,0,1), (0,0,1,2,3,0), (0,0,0,2,1,0), (0,0,2,4,0,0)],
  [(0,0,0,1,0,0), (0,0,3,1,1,1), (0,2,0,2,2,0), (0,1,1,1,3,0), (2,0,0,5,0,0), (0,0,1,1,0,1), (0,0,3,1,1,1), (0,1,1,1,3,0), (0,0,2,2,0,2), (0,0,0,2,0,0), (0,0,3,1,1,1), (0,1,0,1,1,0), (0,1,1,1,3,0)],
  [(0,0,1,0,0,0), (0,2,2,2,0,0), (0,0,4,0,2,0), (0,2,0,2,0,2), (0,2,0,2,2,0), (2,0,1,0,1,0), (0,0,0,4,0,2), (0,0,2,0,2,2), (0,0,2,2,2,0), (0,0,0,0,2,0), (0,0,0,4,2,0), (0,0,1,0,2,0), (0,0,2,4,0,0)],
  [(0,0,0,1,0,0), (0,0,3,2,1,0), (0,1,1,3,0,1), (0,1,3,0,2,0), (0,1,1,1,3,0), (0,1,0,2,0,0), (2,0,1,3,1,0), (0,0,3,1,0,2), (0,0,1,3,1,1), (0,1,0,0,1,0), (0,1,0,2,2,1), (0,0,1,0,1,1), (0,0,1,2,3,0)],
  [(0,0,0,1,0,0), (0,0,3,2,1,0), (0,1,1,3,1,0), (0,1,2,2,0,1), (0,0,3,1,1,1), (0,1,1,0,1,0), (0,2,0,1,3,0), (2,0,1,3,1,0), (0,1,0,3,1,1), (0,0,1,0,0,1), (0,0,2,0,3,1), (0,0,0,2,0,1), (0,0,1,2,3,0)],
  [(0,0,0,0,1,0), (0,0,0,4,1,1), (0,0,3,0,3,0), (0,0,2,2,1,1), (0,2,0,2,2,0), (0,0,1,1,1,0), (0,1,1,3,1,0), (0,1,1,3,0,1), (2,0,2,1,2,0), (0,0,1,0,1,0), (0,1,1,3,0,1), (0,0,2,0,1,0), (0,1,1,1,1,2)],
  [(0,0,0,1,0,0), (0,0,3,3,0,0), (0,0,3,0,3,0), (0,3,0,3,0,0), (0,0,0,6,0,0), (0,0,3,0,0,0), (0,0,3,0,0,3), (0,3,0,0,3,0), (0,0,3,0,3,0), (2,0,0,1,0,0), (0,0,0,3,0,3), (0,0,0,0,3,0), (0,0,0,3,3,0)],
  [(0,0,0,0,1,0), (0,0,0,4,2,0), (0,0,2,2,1,1), (0,0,3,2,1,0), (0,1,1,1,3,0), (0,0,1,2,0,0), (0,1,2,2,0,1), (0,1,3,0,2,0), (0,1,0,3,1,1), (0,1,0,1,0,0), (2,0,2,1,2,0), (0,1,0,1,0,1), (0,0,1,1,2,2)],
  [(0,0,0,0,1,0), (0,0,0,4,2,0), (0,0,2,2,2,0), (0,0,2,4,0,0), (0,0,2,2,0,2), (0,0,2,0,1,0), (0,2,2,0,2,0), (0,2,0,4,0,0), (0,0,2,0,4,0), (0,0,2,0,0,0), (0,2,0,2,0,2), (2,0,1,0,1,0), (0,0,0,2,2,2)],
  [(0,0,0,0,0,1), (0,0,0,0,5,1), (0,0,0,4,1,1), (0,0,0,4,2,0), (0,0,3,1,1,1), (0,0,0,2,1,0), (0,0,3,2,1,0), (0,0,3,2,1,0), (0,2,1,1,1,1), (0,0,1,1,0,0), (0,2,2,1,1,0), (0,1,1,1,0,0), (2,1,1,1,1,1)]
]

def orb6Entry (i j : Fin 13) : Vec6 :=
  (matOrb6Data.getD i.val []).getD j.val v6Zero

def matOrb6 (i j : Fin 13) : GR 6 := v6Get (orb6Entry i j)

def v0Orb6 (i : Fin 13) : GR 6 := mersenneV0 6 (orb6RepFin i)

/-- Cyclic bit-rotation `g ↦ 2*g mod 63` on `Fin 63`. -/
def rot6 (g : Fin 63) : Fin 63 := ⟨(2 * g.val) % 63, Nat.mod_lt _ (by decide)⟩

def rot6Iter : Nat → Fin 63 → Fin 63
  | 0, g => g
  | t + 1, g => rot6 (rot6Iter t g)

/-- Fast check ONLY on the 13 orbit representatives (819 ops instead of 51,597!). -/
def v6Unit (s : Nat) : Vec6 :=
  match s % 6 with
  | 0 => (1, 0, 0, 0, 0, 0) | 1 => (0, 1, 0, 0, 0, 0) | 2 => (0, 0, 1, 0, 0, 0)
  | 3 => (0, 0, 0, 1, 0, 0) | 4 => (0, 0, 0, 0, 1, 0) | _ => (0, 0, 0, 0, 0, 1)

def mersenneH6Vec (g gp : Fin 63) : Vec6 :=
  if g = gp then (2, 0, 0, 0, 0, 0)
  else v6Unit (popcount ((g.val + 63 - gp.val) % 63))

def orb6RepSum (i j : Fin 13) : Vec6 :=
  (List.finRange 63).foldl
    (fun acc gp => if orb6 gp = j then v6Add acc (mersenneH6Vec (orb6RepFin i) gp) else acc)
    v6Zero

/-- Fast memoized `List Vec6` iteration of the literal 13 × 13 matrix `matOrb6Data`. -/
def iterOrb6List : Nat → List Vec6
  | 0 => (List.finRange 13).map fun i => v6OfGR (v0Orb6 i)
  | k + 1 =>
    let prev := iterOrb6List k
    (List.finRange 13).map fun i =>
      (List.finRange 13).foldl
        (fun acc j => v6Add acc (v6Mul (orb6Entry i j) (prev.getD j.val v6Zero)))
        v6Zero

def signBool (b : Bool) : Int := if b then -1 else 1

/-- Pure-data finite-state LSB parity transducer (zero Prop fields!). -/
structure ParityTransducer (d : Nat) where
  nxt : Fin d → Bool → Fin d
  outBit : Fin d → Bool → Bool
  base : Fin d → Int

/-- Structurally recursive fuel-based transducer evaluation (kernel-reducible!). -/
def ParityTransducer.evalFuel {d : Nat} (tr : ParityTransducer d) : Nat → Fin d → Nat → Int
  | 0, g, _ => tr.base g
  | fuel + 1, g, n =>
    if n = 0 then tr.base g
    else
      let b : Bool := (n % 2 == 1)
      signBool (tr.outBit g b) * tr.evalFuel fuel (tr.nxt g b) (n / 2)

def ParityTransducer.eval {d : Nat} (tr : ParityTransducer d) (g : Fin d) (n : Nat) : Int :=
  tr.evalFuel n g n

/-- Decidable consistency check ensuring `n = 0` obeys the `b = false` bit-splitting law. -/
def ParityTransducer.isConsistent {d : Nat} (tr : ParityTransducer d) : Bool :=
  (List.finRange d).all fun g =>
    tr.base g == signBool (tr.outBit g false) * tr.base (tr.nxt g false)

/-- Exact prefix sum `P_g(N) = ∑_{n < N} eval tr g n`. -/
def prefixSum {d : Nat} (tr : ParityTransducer d) (g : Fin d) (N : Nat) : Int :=
  sumRange N (fun n => tr.eval g n)

/-- Exact 2-window state vector `W(N) = (P(N), P(N+1)) ∈ Z^(2d)`. -/
def windowVec {d : Nat} (tr : ParityTransducer d) (N : Nat) : Fin (2 * d) → Int :=
  fun i =>
    if h : i.val < d then
      prefixSum tr ⟨i.val, h⟩ N
    else
      prefixSum tr ⟨i.val - d, by omega⟩ (N + 1)

/-- Single-bit transition matrix `L_b` of size `d × d`. -/
def LMat {d : Nat} (tr : ParityTransducer d) (b : Bool) (i j : Fin d) : Int :=
  if tr.nxt i b = j then signBool (tr.outBit i b) else 0

/-- Compiled 2-window transfer matrices `T_0, T_1` of size `(2d) × (2d)`. -/
def T0Mat {d : Nat} (tr : ParityTransducer d) (i j : Fin (2 * d)) : Int :=
  if hi : i.val < d then
    if hj : j.val < d then LMat tr false ⟨i.val, hi⟩ ⟨j.val, hj⟩ + LMat tr true ⟨i.val, hi⟩ ⟨j.val, hj⟩
    else 0
  else
    if hj : j.val < d then LMat tr true ⟨i.val - d, by omega⟩ ⟨j.val, hj⟩
    else LMat tr false ⟨i.val - d, by omega⟩ ⟨j.val - d, by omega⟩

def T1Mat {d : Nat} (tr : ParityTransducer d) (i j : Fin (2 * d)) : Int :=
  if hi : i.val < d then
    if hj : j.val < d then LMat tr true ⟨i.val, hi⟩ ⟨j.val, hj⟩
    else LMat tr false ⟨i.val, hi⟩ ⟨j.val - d, by omega⟩
  else
    if hj : j.val < d then 0
    else LMat tr false ⟨i.val - d, by omega⟩ ⟨j.val - d, by omega⟩ +
         LMat tr true ⟨i.val - d, by omega⟩ ⟨j.val - d, by omega⟩

def matVecInt {r c : Nat} (A : Fin r → Fin c → Int) (v : Fin c → Int) : Fin r → Int :=
  fun i => sumFin c (fun j => A i j * v j)

/-- Pure-data row-scaled Farkas polyhedral cone certificate (ZERO Prop fields!). -/
structure ConeCert (q dim : Nat) where
  C : List (List Int)
  U0 : List (List Nat)
  U1 : List (List Nat)
  den0 : List Nat
  den1 : List Nat

def ConeCert.CAt {q dim : Nat} (cert : ConeCert q dim) (i : Fin q) (j : Fin dim) : Int :=
  (cert.C.getD i.val []).getD j.val 0

def ConeCert.U0At {q dim : Nat} (cert : ConeCert q dim) (i j : Fin q) : Nat :=
  (cert.U0.getD i.val []).getD j.val 0

def ConeCert.U1At {q dim : Nat} (cert : ConeCert q dim) (i j : Fin q) : Nat :=
  (cert.U1.getD i.val []).getD j.val 0

def ConeCert.den0At {q dim : Nat} (cert : ConeCert q dim) (i : Fin q) : Nat :=
  cert.den0.getD i.val 0

def ConeCert.den1At {q dim : Nat} (cert : ConeCert q dim) (i : Fin q) : Nat :=
  cert.den1.getD i.val 0

/-- Exact computable initial vector `W(1) = T_1 * W(0)`. -/
def windowVec1 {d : Nat} (tr : ParityTransducer d) : Fin (2 * d) → Int :=
  matVecInt (T1Mat tr) (fun j => if hj : j.val < d then 0 else tr.base ⟨j.val - d, by omega⟩)

/-- Pure decidable boolean certificate checker for `ConeCert`. -/
def checkConeCert {d q : Nat} (tr : ParityTransducer d) (cert : ConeCert q (2 * d)) : Bool :=
  let W1 := windowVec1 tr
  let okBase := (List.finRange q).all fun i =>
    1 ≤ sumFin (2 * d) (fun j => cert.CAt i j * W1 j)
  let ok0 := (List.finRange q).all fun i =>
    (0 < cert.den0At i) &&
    (1 ≤ sumFin q (fun r => (cert.U0At i r : Int))) &&
    (List.finRange (2 * d)).all fun col =>
      (cert.den0At i : Int) * sumFin (2 * d) (fun k => cert.CAt i k * T0Mat tr k col) ==
      sumFin q (fun r => (cert.U0At i r : Int) * cert.CAt r col)
  let ok1 := (List.finRange q).all fun i =>
    (0 < cert.den1At i) &&
    (1 ≤ sumFin q (fun r => (cert.U1At i r : Int))) &&
    (List.finRange (2 * d)).all fun col =>
      (cert.den1At i : Int) * sumFin (2 * d) (fun k => cert.CAt i k * T1Mat tr k col) ==
      sumFin q (fun r => (cert.U1At i r : Int) * cert.CAt r col)
  okBase && ok0 && ok1

/-- Transducer for `s_2(n ||| (c * n + g)) mod 2` for any `c > 0`. -/
def orMulTransducer (c : Nat) (_hc : 0 < c) : ParityTransducer c where
  nxt g b := ⟨(c * (if b then 1 else 0) + g.val) / 2, by
    have := g.isLt; cases b <;> simp <;> omega⟩
  outBit g b :=
    let bit := if b then 1 else 0
    ((bit ||| ((c * bit + g.val) % 2)) == 1)
  base g := paritySign (popcount g.val)

/-- Transducer for `s_2(c * n + g) mod 2` for any `c > 0`. -/
def mulTransducer (c : Nat) (_hc : 0 < c) : ParityTransducer c where
  nxt g b := ⟨(c * (if b then 1 else 0) + g.val) / 2, by
    have := g.isLt; cases b <;> simp <;> omega⟩
  outBit g b :=
    let bit := if b then 1 else 0
    (((c * bit + g.val) % 2) == 1)
  base g := paritySign (popcount g.val)

def certOrMul5 : ConeCert 18 10 where
  den0 := [1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1]
  den1 := [1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 2, 6]
  C := [
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 1, 0, 0, 0, 0],
    [1, -1, -1, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, -1, 1, 0, 1, -1, 0, 0, 0],
    [0, -1, -1, 1, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 1, -1, -1, 0, 0],
    [2, -2, -1, 2, -1, 0, 0, 0, 0, 0],
    [0, 0, -1, 2, -1, 2, -2, 0, 0, 0],
    [0, -2, -1, 2, -1, 2, 0, 0, 0, 0],
    [0, 0, 0, 2, -1, 2, -2, -1, 0, 0],
    [0, 0, 0, 0, -1, 2, -2, -1, 2, 0],
    [0, 0, 0, 3, -1, 4, -3, -3, 0, 0],
    [0, 0, 0, 0, -1, 4, -3, -3, 3, 0],
    [0, 0, 0, 0, 1, 4, -3, -3, 3, -2],
    [0, 0, 0, 0, -2, 7, -6, -5, 6, 0],
    [0, 0, 0, 0, 1, 7, -6, -5, 6, -3],
    [0, 0, 0, 0, 2, 13, -11, -9, 11, -6]
  ]
  U0 := [
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 2, 0, 0, 4, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 4, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0],
    [0, 0, 2, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 2, 0, 4, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0]
  ]
  U1 := [
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 7, 0, 7, 0, 5]
  ]

def tribonacci : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | k + 3 => tribonacci (k + 2) + tribonacci (k + 1) + tribonacci k

def or5DyadicVec (k : Nat) : Fin 5 → Int :=
  fun g => prefixSum (orMulTransducer 5 (by decide)) g (2 ^ k)

def certOrMul3 : ConeCert 27 6 where
  den0 := [1, 1, 2, 1, 3, 2, 16, 8, 1, 10, 1, 2062, 1, 9, 1031, 1, 141, 2, 1, 733, 1, 19, 489, 1, 11, 1797, 13]
  den1 := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 1, 13, 1, 1, 294, 1, 173, 1, 1, 39]
  C := [
    [1, 0, 0, 0, 0, 0],
    [1, -1, 0, 0, 0, 0],
    [0, -1, 0, 1, 0, 0],
    [2, -1, 1, 0, 0, 0],
    [0, -1, 1, 2, 0, 0],
    [0, 0, 1, 2, -1, 0],
    [0, -2, 0, 3, 1, 0],
    [0, 0, 0, 3, -1, 0],
    [0, 0, -1, 3, -1, 1],
    [0, 0, 2, 4, -3, -1],
    [0, 0, 0, 4, -3, 1],
    [0, -4, 1, 4, 1, 0],
    [0, 0, -2, 7, -3, 4],
    [0, 0, 3, 7, -3, -1],
    [0, -9, 1, 10, 4, 0],
    [0, 0, -3, 10, -5, 4],
    [0, 0, 8, 15, -9, -4],
    [0, -13, 4, 15, 4, 0],
    [0, 0, -8, 24, -11, 13],
    [0, 0, 9, 24, -11, -4],
    [0, -32, 6, 35, 13, 0],
    [0, 0, -9, 35, -19, 15],
    [0, 0, 26, 54, -29, -13],
    [0, 0, -26, 83, -41, 42],
    [0, -109, 25, 124, 42, 0],
    [0, 0, 84, 191, -99, -42],
    [0, 0, -84, 290, -149, 141]
  ]
  U0 := [
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [2, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 16, 0, 8, 0, 0, 0, 0, 0, 1, 1, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 10, 0, 5, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [2480, 64, 0, 2852, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 30, 9, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 8, 0, 4, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [418, 3157, 0, 2852, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 30, 9, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 112, 0, 0, 0, 0, 0, 0, 140, 0, 0, 0, 0, 20, 30, 0, 0, 0, 0, 7, 0, 0],
    [4, 4, 0, 9, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 544, 0, 0, 0, 0, 187, 493, 0, 0, 0, 0, 291, 0, 0, 0, 0, 34, 0],
    [0, 8, 0, 12, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 47, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 7, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112, 0, 0, 0, 0, 798, 301, 0, 0, 76, 28, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [58, 299, 0, 421, 0, 0, 0, 164, 0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3696, 4636, 0, 0, 1049, 403, 697, 0],
    [0, 0, 0, 0, 146, 0, 69, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0]
  ]
  U1 := [
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 32, 32, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 272, 0, 0, 0, 340, 0, 0, 0, 0, 0, 73, 0, 0, 0, 17],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 380, 0, 0, 0, 0, 0, 129, 0, 0, 0, 0, 0, 167, 0, 0, 0, 67, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 148, 90, 0, 0, 31, 4]
  ]

def certNewman3 : ConeCert 9 6 where
  den0 := [1, 1, 2, 1, 1, 1, 1, 1, 1]
  den1 := [1, 1, 1, 3, 1, 1, 1, 3, 1]
  C := [
    [1, 0, 0, 0, 0, 0],
    [1, -1, 0, 0, 0, 0],
    [0, -1, 0, 1, 0, 0],
    [2, -1, -1, 0, 0, 0],
    [0, -1, -1, 2, 0, 0],
    [0, 0, -1, 2, -1, 0],
    [0, 0, 0, 3, -3, 0],
    [0, 0, 1, 3, -3, -1],
    [0, 0, 0, 6, -3, -3]
  ]
  U0 := [
    [0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 0],
    [0, 3, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 2, 0, 0, 0, 0, 0, 0],
    [0, 0, 3, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 3, 0, 0, 0, 0],
    [0, 0, 0, 0, 2, 1, 0, 0, 0],
    [0, 0, 6, 0, 0, 0, 1, 0, 0]
  ]
  U1 := [
    [0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 6, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 3, 0, 0, 2],
    [0, 0, 0, 0, 0, 0, 3, 0, 0]
  ]

/-- Hostile mutation 1: perturbing a single entry of `U0` causes `checkConeCert = false`. -/
def badCertOrMul5_U0 : ConeCert 18 10 :=
  { certOrMul5 with U0 := [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] :: certOrMul5.U0.tail }

/-- Hostile mutation 2: zeroing a row denominator causes `checkConeCert = false`. -/
def badCertOrMul5_den0 : ConeCert 18 10 :=
  { certOrMul5 with den0 := 0 :: certOrMul5.den0.tail }

/-- Hostile mutation 3: applying `certOrMul5` to the XOR transducer `n ^^^ 5*n` is rejected. -/
def xorMulTransducer (c : Nat) (_hc : 0 < c) : ParityTransducer c where
  nxt g b := ⟨(c * (if b then 1 else 0) + g.val) / 2, by
    have := g.isLt; cases b <;> simp <;> omega⟩
  outBit g b :=
    let bit := if b then 1 else 0
    ((bit ^^^ ((c * bit + g.val) % 2)) == 1)
  base g := paritySign (popcount g.val)

end Adic16
