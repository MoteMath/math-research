namespace NegabinaryCarryParityBias

/-- Signed carry states of a base-`(-2)` (negabinary) adder: `0`, `+1`, `-1`. -/
inductive NegCarry where
  | zero
  | pos
  | neg
  deriving DecidableEq, Repr

/-- Carry states of a standard base-`(+2)` binary adder: `0`, `+1`. -/
inductive BinCarry where
  | zero
  | one
  deriving DecidableEq, Repr

def NegCarry.toInt : NegCarry → Int
  | .zero => 0
  | .pos => 1
  | .neg => -1

def BinCarry.toInt : BinCarry → Int
  | .zero => 0
  | .one => 1

/-- One bit-slice step of negabinary addition with incoming carry `c`.
Returns `(carryGenerated : Nat, nextCarry : NegCarry)`, where `carryGenerated = 1`
iff a positive carry (`s ≥ 2`, next carry `-1`) or negative carry (`s < 0`, next carry `+1`) occurs. -/
def negabinStep (a b : Nat) (c : NegCarry) : Nat × NegCarry :=
  let s : Int := (a : Int) + (b : Int) + c.toInt
  if s ≥ 2 then (1, .neg)
  else if s < 0 then (1, .pos)
  else (0, .zero)

/-- Trailing carries generated while draining a carry `c` after both addends reach `0`. -/
def negabinDrain : NegCarry → Nat
  | .zero => 0
  | .pos => 0
  | .neg => 1

/-- Exact total count of positive and negative carries generated when adding `x` and `m`
in negabinary (base `-2`) starting from incoming carry `c`. -/
def negabinCarries (x m : Nat) (c : NegCarry) : Nat :=
  if _ : x = 0 ∧ m = 0 then
    negabinDrain c
  else
    let step := negabinStep (x % 2) (m % 2) c
    step.1 + negabinCarries (x / 2) (m / 2) step.2
termination_by x + m
decreasing_by
  omega

/-- One bit-slice step of standard base-`(+2)` binary addition with incoming carry `c`. -/
def base2Step (a b : Nat) (c : BinCarry) : Nat × BinCarry :=
  let s : Int := (a : Int) + (b : Int) + c.toInt
  if s ≥ 2 then (1, .one)
  else (0, .zero)

/-- Exact total count of carries generated when adding `x` and `m` in standard binary
(base `+2`) starting from incoming carry `c`. -/
def base2Carries (x m : Nat) (c : BinCarry) : Nat :=
  if _ : x = 0 ∧ m = 0 then
    0
  else
    let step := base2Step (x % 2) (m % 2) c
    step.1 + base2Carries (x / 2) (m / 2) step.2
termination_by x + m
decreasing_by
  omega

/-- Parity character `(-1)^n ∈ {+1, -1}` in pure `Int` arithmetic. -/
def signOfNat (n : Nat) : Int :=
  if n % 2 = 0 then 1 else -1

/-- Exact integer sum `∑_{x = 0}^{n - 1} f x`. -/
def sumRange (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumRange f n + f n

/-- Exact finite-width negabinary carry-parity sum
`S_w(m, c) = ∑_{x = 0}^{2^w - 1} (-1)^{negabinCarries x m c}`. -/
def negabinParitySum (w m : Nat) (c : NegCarry) : Int :=
  sumRange (fun x => signOfNat (negabinCarries x m c)) (2 ^ w)

/-- Exact finite-width standard binary carry-parity sum
`S^{+2}_w(m, c) = ∑_{x = 0}^{2^w - 1} (-1)^{base2Carries x m c}`. -/
def base2ParitySum (w m : Nat) (c : BinCarry) : Int :=
  sumRange (fun x => signOfNat (base2Carries x m c)) (2 ^ w)

/-- Binary bit-length of `m` (`bitLen 0 = 0`, `bitLen m = ⌊log₂ m⌋ + 1` for `m ≥ 1`). -/
def bitLen (m : Nat) : Nat :=
  if _ : m = 0 then 0 else bitLen (m / 2) + 1
termination_by m
decreasing_by
  omega

/-- Jacobsthal sequence `J_k = (2^k - (-1)^k) / 3` (`J_0 = 0, J_1 = 1, J_2 = 1, J_3 = 3, ...`). -/
def jacobsthal : Nat → Int
  | 0 => 0
  | k + 1 => (2 ^ k : Int) - jacobsthal k

/-- Exact 3-mode spectral triple `(b, o, d)` for negabinary carry-parity sums at carry state `c`.
For all `m, k : Nat` and `c : NegCarry`:
`3 * negabinParitySum (bitLen m + k) m c = b * 2^k + o * (-1)^k + 3 * d`,
where the asymptotic bias is `β_{-2}(m) = b / (3 * 2^(bitLen m))`. -/
def negabinSpec (m : Nat) : (Int × Int × Int) × (Int × Int × Int) × (Int × Int × Int) :=
  if _ : m = 0 then
    ((3, 1, 1), (0, -1, -1), (0, 1, -1))
  else
    let ((b0, bp, bm), (o0, op, om), (d0, dp, dm)) := negabinSpec (m / 2)
    if m % 2 = 0 then
      ((2 * b0, b0 - bm, b0 - bp),
       (2 * o0, o0 - om, o0 - op),
       (2 * d0, d0 - dm, d0 - dp))
    else
      ((b0 - bm, -2 * bm, 2 * b0),
       (o0 - om, -2 * om, 2 * o0),
       (d0 - dm, -2 * dm, 2 * d0))
termination_by m
decreasing_by
  omega

/-- Exact 2-mode spectral pair `(g, u)` for standard binary (base `+2`) carry-parity sums.
For all `m, k : Nat` and `c : BinCarry`:
`3 * base2ParitySum (bitLen m + k) m c = g * 2^k + u * (-1)^k`,
where the asymptotic bias is `β_{+2}(m) = g / (3 * 2^(bitLen m))`. -/
def base2Spec (m : Nat) : (Int × Int) × (Int × Int) :=
  if _ : m = 0 then
    ((3, 1), (0, 2))
  else
    let ((g0, g1), (u0, u1)) := base2Spec (m / 2)
    if m % 2 = 0 then
      ((2 * g0, g0 - g1), (2 * u0, u0 - u1))
    else
      ((g0 - g1, -2 * g1), (u0 - u1, -2 * u1))
termination_by m
decreasing_by
  omega

end NegabinaryCarryParityBias
