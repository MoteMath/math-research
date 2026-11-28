namespace ClmulCarryDynamics

/-- Carry-less multiplication over `F_2[X]` encoded on natural numbers. -/
def clmul (a x : Nat) : Nat :=
  if a = 0 then 0
  else (if a % 2 = 1 then x else 0) ^^^ (clmul (a / 2) x <<< 1)
termination_by a

/-- `n`-fold iteration of an endomap. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterate f n (f x)

/-- Carryless-carried hybrid affine map `x ↦ (clmul a x + b) mod 2^w`. -/
def hybridStep (a b w x : Nat) : Nat :=
  (clmul a x + b) % 2 ^ w

/-- `f` forms a single full cycle of length `N` on `{0, ..., N - 1}` starting at `0`. -/
def IsFullCycle (f : Nat → Nat) (N : Nat) : Prop :=
  iterate f N 0 = 0 ∧
  (∀ i j, i < N → j < N → iterate f i 0 = iterate f j 0 → i = j) ∧
  (∀ x, x < N → ∃ i, i < N ∧ iterate f i 0 = x)

/-- Pure-silicon carry-vector rotation Kaprekar map on `BitVec w`. -/
def kaprekarStep {w : Nat} (x : BitVec w) : BitVec w :=
  (((x + 1#w) ^^^ x ^^^ 1#w) + x.rotateLeft 1) + 1#w

/-- Binary Hamming weight (population count) of a natural number. -/
def popcount (n : Nat) : Nat :=
  if n = 0 then 0
  else (n % 2) + popcount (n / 2)
termination_by n

/-- Parity sign `(-1)^k` as an integer. -/
def paritySign (k : Nat) : Int :=
  if k % 2 = 0 then 1 else -1

/-- Fibonacci numbers (`fib 0 = 0, fib 1 = 1, fib 2 = 1, fib 3 = 2, ...`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- Sum of `f 0 + ... + f (n - 1)` in `Nat`. -/
def sumNat : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumNat n f + f n

/-- Sum of `f 0 + ... + f (n - 1)` in `Int`. -/
def sumInt : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumInt n f + f n

/-- Number of `x < 2^w` for which carried and carry-less multiplication by `3` coincide. -/
def zeroCarry3Count (w : Nat) : Nat :=
  sumNat (2 ^ w) (fun x => if 3 * x = clmul 3 x then 1 else 0)

/-- Exact carried-vs-carryless `m = 3` parity correlation sum over `0 ≤ x < 2^w`. -/
def clmul3ParitySum (w : Nat) : Int :=
  sumInt (2 ^ w) (fun x => paritySign (popcount (3 * x) + popcount (clmul 3 x)))

end ClmulCarryDynamics
