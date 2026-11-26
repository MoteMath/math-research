namespace ArxFibonacciIsospectrality

/-- `n`-fold iteration of a map `F : α → α`. -/
def iter {α : Type} (F : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iter F n (F x)

/-- Exact minimal period predicate for a map `F` at a starting state `p`:
`L > 0`, `F^L(p) = p`, and no strictly smaller positive iterate returns to `p`. -/
def IsMinPeriod {α : Type} (F : α → α) (p : α) (L : Nat) : Prop :=
  0 < L ∧ iter F L p = p ∧ ∀ k : Nat, 0 < k → k < L → iter F k p ≠ p

/-- Unreduced XOR-keyed ARX Fibonacci map over `Nat × Nat`:
`G_c^{\mathrm{raw}}(x, y) = (y, x + (y ^^^ c))`. -/
def arxFibRaw (c : Nat) (p : Nat × Nat) : Nat × Nat :=
  (p.2, p.1 + (p.2 ^^^ c))

/-- `m`-bit modular XOR-keyed ARX Fibonacci map:
`G_{c,m}(x, y) = (y mod 2^m, (x + (y ^^^ c)) mod 2^m)`. -/
def arxFibStep (c m : Nat) (p : Nat × Nat) : Nat × Nat :=
  (p.2 % 2 ^ m, (p.1 + (p.2 ^^^ c)) % 2 ^ m)

/-- Contrast map replacing `1 * x` with `3 * x`:
`H_{c,m}(x, y) = (y mod 2^m, (3 * x + (y ^^^ c)) mod 2^m)`. -/
def arxFibStep3 (c m : Nat) (p : Nat × Nat) : Nat × Nat :=
  (p.2 % 2 ^ m, (3 * p.1 + (p.2 ^^^ c)) % 2 ^ m)

end ArxFibonacciIsospectrality
