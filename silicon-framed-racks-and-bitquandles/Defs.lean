namespace SiliconRacksQuandles

/-- General coset-shift framed-link rack operation `x ⋆ y = y + g (y - x)` on `BitVec w`. -/
def cosetRack {w : Nat} (g : BitVec w → BitVec w) (x y : BitVec w) : BitVec w :=
  y + g (y - x)

/-- Left-multiplication inverse `x ⋆⁻¹ y = y - g (y - x)` for a coset-shift rack. -/
def cosetRackInv {w : Nat} (g : BitVec w → BitVec w) (x y : BitVec w) : BitVec w :=
  y - g (y - x)

/-- Single-bit carry-XOR framed-link rack `x + ((y - x) ^^^ 2^k) + 2^k` on `BitVec w`. -/
def carryXorRack {w : Nat} (k : Nat) (x y : BitVec w) : BitVec w :=
  x + ((y - x) ^^^ (1#w <<< k)) + (1#w <<< k)

/-- Low-`k`-bit all-ones mask `(1#w <<< k) - 1#w` (`2^k - 1` mod `2^w`). -/
def lowMask (w k : Nat) : BitVec w :=
  (1#w <<< k) - 1#w

/-- Zero-borrow core-XOR framed-link rack `(x ^^^ lowMask w k) + (x - y)` on `BitVec w`. -/
def coreXorRack {w : Nat} (k : Nat) (x y : BitVec w) : BitVec w :=
  (x ^^^ lowMask w k) + (x - y)

/-- Single-bit conjugated knot quandle `((x ^^^ 2^k) + (y - x)) ^^^ 2^k` on `BitVec w`. -/
def conjBitQuandle {w : Nat} (k : Nat) (x y : BitVec w) : BitVec w :=
  ((x ^^^ (1#w <<< k)) + (y - x)) ^^^ (1#w <<< k)

/-- Explicit left-multiplication inverse of `conjBitQuandle`. -/
def conjBitQuandleInv {w : Nat} (k : Nat) (x y : BitVec w) : BitVec w :=
  if x.getLsbD k = y.getLsbD k then y
  else if x.getLsbD k then y + (1#w <<< (k + 1))
  else y - (1#w <<< (k + 1))

end SiliconRacksQuandles
