# Modular Carry-Residue Duality: MSB-Euclid / LSB-2-adic Coboundary Coupling (`modular-carry-residue-duality`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **9 / 10** | **7 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a bidirectional dual-transducer coupling that cancels the input popcount identically, together with residue-blind 2-adic reciprocal popcount laws for every Mersenne modulus $2 ^ k - 1$, every Fermat modulus $2 ^ k + 1$ and every odd modulus dividing some $2 ^ d + 1$, formalized in pure Lean 4 `Init` (zero Mathlib). Novelty is held below 9 because the negacyclic reciprocal popcount law is the 2-adic shadow of Midy's theorem (see Prior-Art Context).*

## For Mathematicians

Fix an odd modulus $m = 2 u + 1$ and write $s _ 2$ for the binary popcount and $v _ 2$ for the 2-adic valuation. Every $L$-bit integer $n < 2 ^ L$ drives **two finite-state bit transducers over the identical state space** $\mathrm{Fin}\,m$ in opposite bit orders:

1. the **MSB-first Euclidean remainder automaton** with prefix remainders $r _ i = \lfloor n / 2 ^ i \rfloor \bmod m$ and quotient $E = \lfloor n / m \rfloor$;
2. the **LSB-first 2-adic division carry transducer** with carries $c _ i$ satisfying $c _ i + m \cdot q _ i = b _ i + 2 c _ {i + 1}$, producing the 2-adic quotient $Q _ L(n) = (n \cdot m ^ {-1}) \bmod 2 ^ L$ with $m \cdot Q _ L(n) = n + c _ L \cdot 2 ^ L$.

Each automaton carries a **one-bit coboundary certificate** (a state weight, a boundary potential and two scales $\alpha, \beta$ satisfying a single local identity). The generic lifting theorems `coboundary_lift_LSB`, `coboundary_lift_MSB` telescope any such certificate to all widths $L$, and `dual_coupling_lift` pairs an MSB and an LSB certificate with matched scales so that the input weight $s _ 2(n)$ **cancels identically**. For the division automata the two potentials are exact opposite-sign coboundaries ($\pm 2 s$) and the pointwise modular coupling yields, for **every odd $m$, every $L$, every $n < 2 ^ L$**, the master dual conservation law

```math
m \cdot \mathcal{I} _ m(n, L) = 2 \bigl( (n \bmod m) + c _ L \bigr) - O _ m(n \bmod m, L),
```

where $\mathcal{I} _ m(n, L) = s _ 2(Q _ L(n)) - s _ 2(E) - W _ m(n, L)$, $W _ m$ counts the positions with $r _ i < c _ i$ and $O _ m$ is the orbit sum of the halving map $x \mapsto x / 2 \bmod m$. Consequences proved for all $m$: $m \mid n \iff c _ L = 0 \iff (\forall i \le L,\ r _ i = c _ i) \iff Q _ L(n) = \lfloor n / m \rfloor$, and the exact carry-complementarity law $\kappa _ {\mathrm{add}}(\lfloor n / m \rfloor, Q _ L(n \bmod m)) + W _ m(n, L) = L - 1 - v _ 2(n \bmod m)$ whenever $m \nmid n$.

**Infinite families.** Halving modulo $2 ^ k - 1$ is a $k$-bit cyclic rotation, so its full-period orbit sum is $(2 ^ k - 1) \cdot s _ 2(r)$. For all $k \ge 2$, $t \ge 1$ and $n < 2 ^ {t k}$ this gives the **residue-weight extraction law** $\mathcal{I} _ {2 ^ k - 1}(n, t k) = 0$ if $(2 ^ k - 1) \mid n$ and $2 - t \cdot s _ 2(n \bmod (2 ^ k - 1))$ otherwise, a **sharp divisibility test for all $t \ge 3$**, and the **reciprocal popcount law**

```math
s _ 2 \bigl( (r \cdot (2 ^ k - 1) ^ {-1}) \bmod 2 ^ {t k} \bigr) = t \, (k - s _ 2(r)) + 1 - v _ 2(r) \qquad (0 < r < 2 ^ k - 1).
```

Whenever odd $m \ge 3$ divides $2 ^ d + 1$ (the whole Fermat family $m = 2 ^ k + 1$ plus infinitely many proper divisors such as $11, 13, 19, 25, 43$), half-period halving is the antipodal involution $x \mapsto m - x$, forcing $O _ m(r, 2 d) = d \cdot m$ independently of $r$. Then $\mathcal{I} _ m(n, 2 t d) = 2 - t d$ off multiples of $m$, divisibility is characterized exactly when $t d \ne 2$ (the exception set $t d = 2$ is exactly $(m, d, t) \in \{(3, 1, 2), (5, 2, 1)\}$ where $\mathcal{I} _ m(n, 4) \equiv 0$), and the reciprocal popcount is **independent of $s _ 2(r)$**:

```math
s _ 2 \bigl( (r \cdot m ^ {-1}) \bmod 2 ^ {2 t d} \bigr) = t d + 1 - v _ 2(r) \qquad (0 < r < m,\ m \mid 2 ^ d + 1).
```

Sharpness is kernel-checked: two infinite counterexample families show that the thresholds $t \ge 3$ (Mersenne) and $t d \ne 2$ (negacyclic) cannot be lowered, and a mutation witness shows that non-negacyclic moduli break the residue-blind collapse.

## For Non-Mathematicians

Dividing a binary number by an odd number such as $7$, $9$ or $11$ can be done by a small circuit in two ways: reading the bits from the most significant end (ordinary long division, tracking a remainder) or from the least significant end (a "carry" circuit that cancels low bits one at a time). Both circuits are tiny, and both look at the same number. This package proves that, running them side by side on the same input, **the count of 1-bits in the input cancels out exactly**, leaving a clean bookkeeping identity that is valid for numbers of **every length** and for **every odd divisor**.

For divisors of the special shapes $2 ^ k - 1$ (such as $3, 7, 15, 31$) and $2 ^ k + 1$ (such as $3, 5, 9, 17$), the identity collapses to a startlingly simple fact: the number of 1-bits in the binary expansion of $r / m$ (as a 2-adic number, i.e. truncated to the right length) depends only on the length and the number of trailing zero bits of $r$, **not on what the other bits of $r$ are**. Every statement is a theorem for all lengths at once, checked by Lean's kernel, with no sampling and no floating point.

## Main Theorems

All eight headline theorems live in `Challenge.lean` (statements, `sorry` placeholders) and are proved in `Solution.lean` by delegation to `ModularCarryResidueDuality/Theorems.lean`.

| Theorem | Statement |
| :--- | :--- |
| `master_dual_carry_residue_law` | $m \cdot \mathcal{I} _ m(n, L) = 2 ((n \bmod m) + c _ L) - O _ m(n \bmod m, L)$ for every odd $m$, $L$ and $n < 2 ^ L$. |
| `synchronized_trace_divisibility_iff` | $m \mid n \iff c _ L = 0 \iff (\forall i \le L,\ r _ i = c _ i) \iff Q _ L(n) = \lfloor n / m \rfloor$. |
| `carry_complementarity_law` | For $m \nmid n$: $\kappa _ {\mathrm{add}}(\lfloor n / m \rfloor, Q _ L(n \bmod m)) + W _ m(n, L) = L - 1 - v _ 2(n \bmod m)$. |
| `mersenne_dual_invariant_law` | For $m = 2 ^ k - 1$, $\mathcal{I} _ m(n, t k) = 0$ if $m \mid n$, else $2 - t \cdot s _ 2(n \bmod m)$. |
| `mersenne_divisibility_threshold_iff` | For $t \ge 3$: $(2 ^ k - 1) \mid n \iff s _ 2(Q _ {t k}(n)) - s _ 2(\lfloor n / (2 ^ k - 1) \rfloor) = W _ {2 ^ k - 1}(n, t k)$. |
| `mersenne_reciprocal_popcount_law` | $s _ 2(Q _ {t k}(r)) = t (k - s _ 2(r)) + 1 - v _ 2(r)$ for $0 < r < 2 ^ k - 1$. |
| `negacyclic_reciprocal_popcount_law` | For odd $m \ge 3$ with $m \mid 2 ^ d + 1$: $s _ 2(Q _ {2 t d}(r)) = t d + 1 - v _ 2(r)$ for $0 < r < m$. |
| `fermat_reciprocal_popcount_law` | $s _ 2(Q _ {2 t k}(r)) = t k + 1 - v _ 2(r)$ for $m = 2 ^ k + 1$ and $0 < r < m$. |

The module `ModularCarryResidueDuality/Theorems.lean` additionally proves the remaining Mersenne, negacyclic and Fermat laws (`fermat_dual_invariant_law`, `negacyclic_dual_invariant_law`, `negacyclic_divisibility_iff_ne_two`, `negacyclic_exceptional_collapse_eq_two`, `two_adic_reciprocal_popcount_master`), the generic transducer lifting theorems, non-vacuity witnesses and the sharpness theorems.

## Proof Architecture

- **`ModularCarryResidueDuality/Defs.lean`:** pure-silicon binary primitives (`bitAt`, `popcount`, `v2`, `carriesAdd`, `sumNat`, `sumInt`), the polymorphic `BitTransducer`, the certificate structures `LSBCoboundaryCert` / `MSBCoboundaryCert`, the dual automata `msbDivFin` / `lsbCarryFin` over `Fin m`, the observables `remAt`, `carryAt`, `twoAdicQuot`, `carryDomCount`, `dualInvariant`, `halvingOrbitSum`, and the oddness lemmas `mersenne_odd`, `fermat_odd` needed to state the family theorems.
- **`ModularCarryResidueDuality/Theorems.lean`:** all proofs (coboundary lifting by telescoping, dual coupling elimination, halving-orbit analysis for Mersenne rotations and negacyclic antipodes, divisibility characterizations, sharpness and non-vacuity).
- **`Challenge.lean`** imports only `Defs`; **`Solution.lean`** imports only the full library; `comparator.json` lists the eight theorems for the Palomar Comparator with `nanoda` enabled.
- **`scripts/explore_and_verify.py`:** exact-integer replay of every law (no floats), plus sharpness counterexamples.

## Prior-Art Context

- **Classical ingredients (not claimed as new):** base-$2 ^ k$ digit-sum congruences modulo $2 ^ k \mp 1$; Kummer's carry identity $s _ 2(a) + s _ 2(b) - s _ 2(a + b) = \kappa _ {\mathrm{add}}(a, b)$; the individual MSB Euclidean division automaton and LSB Hensel / exact-division (Montgomery-style) transducer; Newman's phenomenon on the Thue-Morse bias of multiples of $3$.
- **Midy's theorem:** for odd $m \mid 2 ^ d + 1$ the repeating $2 d$-bit block of $r / m$ splits into two bitwise-complementary $d$-bit halves (Midy 1836; Ginsberg, *Midy's (nearly) secret theorem*, 2004; Lewittes, *Midy's theorem for periodic decimals*, 2007). The negacyclic reciprocal popcount law is the exact 2-adic / two's-complement shadow of this antipodal pairing, here obtained uniformly as a corollary of the dual coboundary engine rather than from radix-expansion digit splitting.
- **Claimed by the authors as new (not independently reviewed):** the simultaneous MSB/LSB coupling mechanism (`dual_coupling_lift`) with opposite-sign coboundary potentials whose combination cancels the input popcount identically, the master conservation law and synchronized-trace divisibility equivalence for every odd modulus, the Mersenne residue-weight extraction law, and the exact exception set $t d = 2$. Both reciprocal popcount laws were also replayed exhaustively by the authors on small ranges (Mersenne $k = 2..6$, $t = 1..4$: 456 residues; negacyclic $d = 1..8$, $t = 1..3$: 1752 residues; 0 mismatches); this proves nothing beyond those ranges. No prior record of the dual coupling identity was found by the authors; the search was not recorded.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
python scripts/explore_and_verify.py
```

Toolchain `leanprover/lean4:v4.34.1`, pure `Init` (zero Mathlib). See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. Only the standard axioms `propext`, `Classical.choice`, `Quot.sound` are used; there is no `sorry`, `admit`, `native_decide` or custom `axiom` outside the intentional placeholders in `Challenge.lean`.
