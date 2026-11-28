# Negabinary Carry Determinants

Machine-checked Lean 4 / Mathlib formalization of **base-$(-2)$ (negabinary) carry-borrow matrix theory** over arbitrary commutative rings, discovered by exact 32-prime modular determinant mining on an AMD RX 7900 XTX (`Engine 4C`, zero floating-point ISA ops) and validated bit-for-bit on CPU.

## Why This Confuses Classical Intuition

In ordinary base $+2$, adding two non-negative integers has a single carry state $\{0, 1\}$, and zero carries occurs if and only if the binary operands are bitwise disjoint (`i &&& j = 0`), producing the classical Sierpinski matrix $S _ n(i, j) = \mathbf{1}[i \mathbin{\&} j = 0]$ with determinant $\prod _ {k=0} ^ {n-1} (-1)^{s _ 2(k)}$.

In **negabinary (base $-2$)**, addition uses a **three-state** carry/borrow automaton $\{-1, 0, +1\}$: a bit collision `1 + 1 = 2` emits a **borrow** $-1$ into the next bit, which can either be absorbed (`1 + 0 - 1 = 0`, `1 + 1 - 1 = 1`) or underflow (`0 + 0 - 1 = -1`) to emit a **positive carry** $+1$.

Two startling, completely non-classical laws emerge:

1. **The Hidden Thue–Morse $LDL^T$ Twins (for ALL $n \in \mathbb{N}$):**
   The zero-positive-carry matrix $Z _ n(i, j) = \mathbf{1}[\mathrm{pos\_carries} _ {-2}(i, j) = 0]$ is **genuinely different** from the disjoint-bit Sierpinski matrix $S _ n(i, j) = \mathbf{1}[i \mathbin{\&} j = 0]$ — it has $90$ extra `1`-entries already below $16$ (e.g. `(1, 3)` and `(3, 3)` have zero positive carries because borrows self-absorb in pairs). Yet $Z _ n$ admits an **explicit lower-unitriangular bitwise run-prefix $LDL^T$ factorization** over every commutative ring $R$ with the **exact same Thue–Morse diagonal** $D _ {kk} = (-1)^{s _ 2(k)}$:
   ```math
   Z_n = L_{Z, n} \cdot \mathrm{diag}\bigl((-1)^{s_2(0)}, \dots, (-1)^{s_2(n-1)}\bigr) \cdot L_{Z, n}^{\mathsf{T}},
   \qquad
   \det(Z_n) = \prod_{k=0}^{n-1} (-1)^{s_2(k)} \in \{-1, +1\}.
   ```
   Here $L _ {Z}(i, k) = 1$ iff $k$ keeps a downward prefix of every contiguous `1`-run of $i$ (never dropping a `1`-bit directly above a kept `1`-bit).

2. **The $n = 34$ Spontaneous Prime-Factor-$3$ Anomaly:**
   The positive-carry parity matrix $H _ n(i, j) = (-1)^{\mathrm{pos\_carries} _ {-2}(i, j)}$ satisfies
   ```math
   \det(H_n) = 2^{n-1} \prod_{k=0}^{n-1} (-1)^{s_2(k)}
   ```
   for **33 consecutive dimensions** ($1 \le n \le 33$) — and then at **$n = 34$**, a spontaneous prime factor of **$3$** erupts:
   ```math
   \det(H_{34}) = 3 \cdot 2^{33} \prod_{k=0}^{33} (-1)^{s_2(k)} = -25769803776,
   ```
   proved cleanly via an exact recursive even/odd block-decoupling theorem reducing $H _ {34}$ directly to the $9 \times 9$ auxiliary block $\det(J _ 9) = -1536 = -3 \cdot 2 ^ 9$.

3. **Exact Base-$(-2)$ Digit-Sum Conservation Law (Mod-$3$ Kummer Twin):**
   For every $i, j \in \mathbb{N}$,
   ```math
   s_2(i) + s_2(j) - s_2(i +_{-2} j) = 3\bigl(\mathrm{neg\_borrows}_{-2}(i, j) - \mathrm{pos\_carries}_{-2}(i, j)\bigr).
   ```

## Headline Theorems (All Verified in Lean 4.34.1)

| Theorem | Statement Summary |
|---|---|
| `negAdd_popcount_conservation` | $s _ 2(i) + s _ 2(j) - s _ 2(i + _ {-2} j) = 3(\mathrm{negNegBorrows} - \mathrm{negPosCarries})$ for all $i, j \in \mathbb{N}$ |
| `runPrefix_iff_bits` | Bitwise downward-prefix characterization of `runPrefix i k` |
| `negZeroPosCarryMat_eq_LDL` | $Z _ n = L _ {Z,n} \cdot \mathrm{diag}((-1)^{s _ 2(k)}) \cdot L _ {Z,n}^{\mathsf{T}}$ over every `CommRing R` and $n \in \mathbb{N}$ |
| `det_negZeroPosCarryMat` | $\det(Z _ n) = \prod _ {k < n} (-1)^{s _ 2(k)}$ for every `CommRing R` and $n \in \mathbb{N}$ |
| `det_negZeroBorrowMat` | $\det(B _ n) = \prod _ {k < n} (-1)^{s _ 2(k)}$ via $B _ n = S _ n$ |
| `negZeroPosCarry_ne_disjointBit` | Explicit witness that $Z _ n \ne S _ n$ at `(1, 3)` and `(3, 3)` |
| `det_negParityMat_decouple` | $\det(H _ n) = \det(H _ {\lceil n/2 \rceil}) \cdot \det(K _ {\lfloor n/2 \rfloor})$ for every `CommRing R` and $n \in \mathbb{N}$ |
| `det_negKMat_decouple` | $\det(K _ m) = (-1)^m \det(J _ {\lceil m/2 \rceil}) \cdot \det(K _ {\lfloor m/2 \rfloor})$ for every `CommRing R` and $m \in \mathbb{N}$ |
| `negParityMat_n34_anomaly` | $\det(H _ {33}) = 2^{32} \prod _ {k<33}(-1)^{s _ 2(k)}$ while $\det(H _ {34}) = 3 \cdot 2^{33} \prod _ {k<34}(-1)^{s _ 2(k)}$ |

## Layout

- `NegabinaryCarryDet/Defs.lean`: Pure-Mathlib definitions only (no proofs).
- `Challenge.lean`: Trusted statement file importing only `NegabinaryCarryDet.Defs` for `leanprover/comparator`.
- `NegabinaryCarryDet/Core.lean`: Complete sorry-free proofs of all 9 headline theorems.
- `Solution.lean`: Exports all 9 verified proofs matching `Challenge.lean`.
- `scripts/PrintAxioms.lean` & `AUDIT.md`: Verbatim kernel axiom verification record.
