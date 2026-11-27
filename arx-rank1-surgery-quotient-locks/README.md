# ARX Rank-1 Surgery & Speck Quotient Locks (`arx-rank1-surgery-quotient-locks`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): three reusable infinite-width ARX engines (Mersenne-ring affine lifting with an 8-member ARX conjugacy group, abstract rank-1 carry-defect cycle surgery, and multi-word keyed carry-barrier quotient locks) yielding exact Fermat-Mersenne permutation orders, exact rank-1 cycle surgery on `(x + 1).rotateLeft r`, and round-varying period-3 quotient locks on Speck across all word widths, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Add-Rotate-XOR (ARX) round functions mix modular addition over $\mathbb{Z}/2^w\mathbb{Z}$, cyclic rotation $\mathrm{rotL} _ r$ (which acts as multiplication by $2^r$ in the Mersenne ring $\mathbb{Z}/(2^w - 1)\mathbb{Z}$), and bitwise XOR. We build three reusable infinite-width engines:

1. **Mersenne-Ring Lifting & Conjugacy Group (`MersenneAffineLift`):** For $F _ {w, r}(x) = \mathrm{rotL} _ r(x + 1) \oplus (2^w - 1)$ with $g = \gcd(w, r)$ and $q = w / g$, the exact permutation order (realized minimally at $0$) is $2q$ when $q$ is odd ($w \ge 2$) and $q(2^g + 1)$ when $q$ is even ($w \ge 3$). On power-of-two words $w = 2^k, r = 2^j$ ($k \ge 2, j < k$), this evaluates to $2^{k-j} F _ j$ where $F _ j = 2^{2^j} + 1$ is the $j$-th Fermat number.
2. **Rank-1 Carry-Defect Cycle Surgery (`Rank1Surgery`):** For any injective $\psi$ with fixed point $\top$ and a $B$-cycle at $a \neq \top$, composing with the single transposition $\tau _ {(a, \top)}$ splices $\top$ into $a$'s cycle for exact minimal period $B + 1$, leaves every outside state invariant, and locks global order to $B(B + 1)$. Applying this to $A _ {w, r}(x) = \mathrm{rotL} _ r(x + 1)$ with $B = q(2^g - 1)$ gives one anomalous $(B + 1)$-cycle at $0$, period dividing $B$ everywhere outside, and global order dividing $B(B + 1)$; the MSB-flip conjugacy transports this identically to the genuine Add+Rotate+XOR map $G(x) = \mathrm{rotL} _ r(x + (1 \oplus 2^{w-1})) \oplus 2^{w-1}$.
3. **Multi-Word Speck Carry-Barrier Quotient Lock (`KeyedQuotientLock`):** For every $h \ge 1$, the 2-word Speck round on $(\mathrm{BitVec}(2h))^2$ preserves a $(2h + 2)$-dimensional proper $\mathbb{F} _ 2$-linear subspace $V _ h$ under all $2^{h+1}$ valid keys (with arbitrary upper $h$-bit halves) and obeys a round-varying period-3 lock on a 2-bit quotient $\pi _ h$ for any three independent keys with vanishing low $h$ bits.

## For Non-Mathematicians

Modern lightweight encryption schemes like Speck are built from just three fast CPU instructions: addition, bit-rotation, and XOR (collectively called ARX). Because addition carries upward while rotation wraps the top bit back to the bottom, predicting how long an ARX operation takes to repeat usually seems hopeless. This package proves that for infinite families of ARX maps of every bit width (including 64-bit and arbitrarily wider words), the cycle lengths follow exact closed formulas involving Mersenne and Fermat numbers. When a single addition overflow breaks the clean Mersenne symmetry, a "rank-1 cycle surgery" theorem shows it splices exactly one extra state into one cycle while leaving every other cycle untouched. Finally, for the two-word Speck cipher round, the package constructs an exponentially large subspace of inputs where carries are blocked across the middle of the word, locking a two-bit summary of the state to repeat every 3 rounds regardless of the upper half of the round keys.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of Mersenne-ring lifting, rank-1 carry-defect cycle surgery, and Speck carry-barrier quotient locks across arbitrary bit-widths.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `rank1Surgery_spliced_minPeriod` | Abstract rank-1 surgery $\tau _ {(a, \top)} \circ \psi$ splices fixed point $\top$ into $a$'s $B$-cycle to yield exact minimal period $B + 1$.' |
| `rank1Surgery_global_order` | If $\psi^B = \mathrm{id}$ globally, rank-1 surgery $\tau _ {(a, \top)} \circ \psi$ has global period dividing $B(B + 1)$. |
| `arx_fermat_mersenne_odd` | For $w \ge 2$ and odd $q = w / \gcd(w, r)$, `arxFermatMap w r` has global period $2q$ realized minimally at $0$. |
| `arx_fermat_mersenne_even` | For $w \ge 3$ and even $q = w / \gcd(w, r)$ with $g = \gcd(w, r)$, `arxFermatMap w r` has global period $q(2^g + 1)$ realized minimally at $0$. |
| `arx_fermat_number_order` | For $w = 2^k$ ($k \ge 2$) and $r = 2^j$ ($j < k$), `arxFermatMap w r` has exact permutation order $2^{k-j}(2^{2^j} + 1) = 2^{k-j} F _ j$. |
| `arx_rank1_surgery_theorem` | For $w \ge 2$ and $B = q(2^g - 1)$, `arxAddRot w r` has one anomalous $(B + 1)$-cycle at $0$, period dividing $B$ everywhere outside it, and global order dividing $B(B + 1)$. |
| `arx_rank1_surgery_nontrivial_xor` | Conjugacy transports the exact $(B + 1)$ minimal period and $B(B + 1)$ global lock to the genuine Add+Rotate+XOR map $G(x) = \mathrm{rotL} _ r(x + (1 \oplus 2^{w-1})) \oplus 2^{w-1}$. |
| `speck_period3_quotient_lock` | For every $h \ge 1$ and any three independent Speck keys whose low $h$ bits vanish, 3 Speck rounds preserve $V _ h$ and lock the 2-bit quotient $\pi _ h$ back to its starting value. |

## Proof Architecture

1. **Mersenne-Ring Lifting (`rotateLeft_toNat_mod_mersenne`, `MersenneAffineLift.zero_master_period`):** cyclic rotation acts as multiplication by $2^r \pmod{2^w - 1}$, reducing global periodicity to a coprime geometric sum (`sumRange_mul_coprime`) and an explicit minimal-period check at $0$.
2. **Abstract Rank-1 Surgery (`rank1Surgery_spliced_minPeriod`, `rank1Surgery_outside_invariant`, `rank1Surgery_global_order`):** factors the overflow defect of `arxAddRot` as a single transposition $\tau _ {(0, 2^w - 1)}$ composed with its zero-defect Mersenne shadow; MSB-flip conjugacy transports the exact cycle structure to nontrivial XOR masks.
3. **Keyed Quotient Locks (`KeyedQuotientLock.iterKeys_sound`, `speckCarryBarrierEngine`):** vanishing low bits block carry propagation across the half-word boundary (`carry_false_below`), making $V _ h$ invariant and semiconjugating Speck onto a 2-bit linear map of order 3.

## Prior-Art Context

- **ARX & invariant-subspace cryptanalysis:** Beaulieu et al. (2013) introduced the Speck block-cipher family; Leander et al. (2011) and Todo et al. (2016) studied invariant-subspace and nonlinear-invariant attacks on block ciphers.
- **Verdict status:** not independently reviewed; no novelty audit has been done, so the novelty summary (exact Fermat-Mersenne order classification, abstract rank-1 carry-defect cycle surgery, and the arbitrary-width Speck half-word carry-barrier period-3 quotient lock) is the packager's conservative reading.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib). See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts, [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest, and `scripts/explore_and_verify.py` for the exact-integer exploration and verification script (zero floating point).
