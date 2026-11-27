# T-Function Curvature-Holonomy Lifting Engine (`tfunction-curvature-holonomy`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **7 / 10** | **10 / 10** | **80 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): an exact bit-slice doubling criterion and curvature-holonomy transport law for single-cycle 1-Lipschitz 2-adic T-functions, a finite-to-infinite lifting engine from width 4, a universal carry-mask XOR symmetry, and complete infinite classifications with sharp failure widths, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

A $1$-Lipschitz T-function $f : \mathbb{N} \to \mathbb{N}$ is single-cycle at width $w$ when its orbit of $0$ visits every residue mod $2^w$ exactly once. Define the bit-slice holonomy $\mathrm{hol}(f, w)$ as the XOR of bit $w$ of $f(r)$ over $r < 2^w$, the unit slice derivative $f(r + 2^w) \equiv f(r) + 2^w \pmod{2^{w+1}}$, and the curvature sum $K _ w(f) = \sum _ {r < 2^w} \big(f(r + 2^w) - f(r) - 2^w\big)$. We prove:

1. **Doubling criterion (Layer 1):** for $f$ single-cycle mod $2^w$, $f$ lifts to mod $2^{w+1}$ if and only if it has unit slice derivative and odd holonomy at $w$.
2. **Transport law (Layer 2):** $D _ {w+1}(f) = 2 D _ w(f) + K _ w(f)$ for the defect sums $D _ w(f) = \sum _ {r < 2^w} (f(r) - r)$, hence $\mathrm{hol}(f, w + 1)$ is odd if and only if $K _ w(f) \equiv 0 \pmod{2^{w+2}}$.
3. **Lifting engine (Layer 3):** one finite single-cycle check at width $4$ plus the derivative and curvature conditions at all larger widths certifies single-cycle behaviour at **every** width. Fixed-point-free involutions (for example a bit flip $r \mapsto r \oplus 2^j$) and $\mathbb{F} _ 2$-linearity annihilate curvature terms, and XORing with any even $2$-Lipschitz operator of vanishing bit-parities (in particular the unbounded carry mask $2k \cdot (x \oplus (x + 1))$) preserves single-cycle behaviour at every width simultaneously.
4. **Family A (hybrid ARX family $H _ {a,b,C,k}$):** single-cycle at all widths if and only if a four-bit condition on $(a, b, C)$ holds, independent of $k$ and of all bits $\ge 4$ of $C$. Both Klimov-Shamir $x + (x^2 \mathbin{|} 1)$ and the pure $2$-run map fail at width $3$, yet their XOR hybrid is single-cycle at every width.
5. **Family B (arbitrary-order run family $R _ {d,C}$):** single-cycle at all widths if and only if $C _ 0 = C _ d = 1$; $R _ {d,1}$ passes widths $1, \dots, d$ and fails at $d + 1$, so **no finite width suffices universally** for $1$-Lipschitz T-functions (in contrast to Larin's mod-$8$ theorem for integer polynomials).

## For Non-Mathematicians

Imagine a counter that, at every tick, replaces a number by a new number computed by a circuit in which each output bit looks only at lower-order input bits, like a row of dominoes that only look backward. Such a circuit makes a good pseudo-random generator only if, starting from 0, it visits every possible n-bit value exactly once before repeating, and it should do so for every word size n. Checking infinitely many word sizes one by one is impossible. This package proves two exact bookkeeping rules (a "derivative" test and a parity "holonomy" test) that say precisely when a full visit-everything cycle at n bits stretches to n + 1 bits. It then shows that for whole families of circuits a check on only 16 values (4 bits) settles all infinitely many word sizes, while for other families, however large a word size you test, a circuit exists that passes up to there and fails on the next size.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of exact single-cycle lifting laws for $1$-Lipschitz $2$-adic T-functions over unbounded $\mathbb{N}$.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `singleCycle_succ_iff` | For a $1$-Lipschitz T-function $f$ that is single-cycle mod $2^w$, $f$ is single-cycle mod $2^{w+1}$ if and only if it has unit bit-slice derivative and odd bit-slice holonomy at $w$. |
| `holonomy_succ_iff_curvatureSum_zero` | If $f$ is $1$-Lipschitz and single-cycle mod $2^{w+1}$, then its holonomy at $w + 1$ is odd if and only if its curvature sum $K _ w(f)$ vanishes mod $2^{w+2}$. |
| `lift_singleCycle_from_w4` | A width-$4$ single-cycle check, unit slice derivatives at all widths $w + 1$ with $w \ge 3$, and $K _ w(f) \equiv 0 \pmod{2^{w+2}}$ for all $w \ge 3$ force $f$ to be single-cycle mod $2^w$ for every $w \ge 1$. |
| `singleCycle_xor_carryMask_iff` | For every $1$-Lipschitz $g$ and every $k$, XORing $g$ with the carry-propagation mask $2k \cdot (x \oplus (x + 1))$ preserves single-cycle behaviour at every width $w \ge 1$. |
| `hybridH_singleCycle_iff_bits` | The hybrid map $H _ {a,b,C,k}$ is single-cycle at every width if and only if $C _ 0 = 1$, $a _ 1 = 1 \to C _ 1 = 1$, $a _ 0 = 0 \to C _ 2 = 1$ and $b _ 0 = 1 \to C _ 3 = 1$, independently of $k$. |
| `runT_singleCycle_iff` | For every $d \ge 2$ and $C$, $R _ {d,C}(x) = x + ((2 \cdot \mathrm{run} _ d(x)) \mathbin{|} C)$ is single-cycle at every width if and only if $C _ 0 = 1$ and $C _ d = 1$. |
| `runT_sharp_threshold` | For every $d \ge 2$, $R _ {d,1}$ is single-cycle at every width $1 \le w \le d$ but not at width $d + 1$. |
| `no_universal_finite_threshold` | For every $W \ge 1$ there is a $1$-Lipschitz T-function that is single-cycle at all widths $1 \le w \le W$ but not at width $W + 1$. |

## Proof Architecture

1. **Layers 1 and 2 (`singleCycle_succ_iff`, `holonomy_succ_iff_curvatureSum_zero`):** exact integer identities relating the sum $D _ w(f)$ of displacements over a full residue system to the holonomy bit, using that a single-cycle map permutes residues mod $2^w$.
2. **Lifting engine (`lift_singleCycle_from_w4`):** induction on the width using Layers 1 and 2; the base case at width $4$ is discharged by the sound and complete finite checker `checkSingleCycle_iff` plus `decide`, and widths below $4$ follow by reduction (`singleCycle_of_ge`).
3. **Symmetry (`singleCycle_xor_carryMask_iff`):** XOR with an even $2$-Lipschitz operator whose bit-$w$ parity over a residue system vanishes changes neither the derivative nor the holonomy data; the carry mask is $4$-Lipschitz and even, so its parities vanish for all $w$.
4. **Families (`hybridH_singleCycle_iff_bits`, `runT_singleCycle_iff`):** the width-$4$ check for the four-parameter hybrid family reduces mod $(16, 2, 16)$ to a finite `decide` over $512$ cases; the run family is handled by an explicit curvature computation showing that the first failing width is $d + 1$.

## Prior-Art Context

- **T-functions:** Klimov and Shamir (*A New Class of Invertible Mappings*, CHES 2002; *New Cryptographic Primitives Based on Multiword T-Functions*, FSE 2004) introduced single-cycle T-functions such as $x + (x^2 \mathbin{|} 1)$; Anashin and Khrennikov (*Applied Algebraic Dynamics*, De Gruyter 2009) give the $2$-adic ergodicity theory; Larin (2002) gives the mod-$8$ criterion for integer polynomials. The width-by-width doubling criterion and the curvature-holonomy transport law in exact integer form, the universal carry-mask XOR symmetry, the complete hybrid and run-family classifications and the no-universal-finite-threshold theorem are, to our knowledge, not recorded in these sources.
- **Review status:** not independently reviewed. No recorded novelty search was made, so the novelty claim above is the authors' reading only.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib). See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts, [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest, and `scripts/explore_and_verify.py` for the exact-integer exploration and verification script (zero floating point).
