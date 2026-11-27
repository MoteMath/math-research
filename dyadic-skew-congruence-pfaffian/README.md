# Dyadic Skew-Congruence & Integral Block-Schur Pfaffian Engine (`dyadic-skew-congruence-pfaffian`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): pure-`Init` Lean 4 formalization of signed integer combinatorial Pfaffians via fraction-free integral block-Schur congruence and skew-conference complementary-minor reflection, applied to carry-asymmetry, Gray-Walsh, and Skew-Walsh skew matrices.*

## For Mathematicians

Rather than proving $\det(A) = \mathrm{Pf}(A)^2$ over a field (which loses the sign of $\mathrm{Pf}(A)$), this package defines the signed combinatorial Laplace Pfaffian directly over $\mathbb{Z}$ and establishes fraction-free integral congruence elimination ($P^T A P$) from first principles in standalone Lean 4 `Init` (zero Mathlib, zero rationals, zero divisions). Three reusable lifting lemmas — upper-unitriangular congruence (`pfaffian_blockUpperId`), integral block-Schur elimination (`pfaffian_blockSchur_bot`), and skew-conference complementary-minor reflection (`pfaffian_skewConference_compl`) — are applied to direct bitwise matrix definitions: the bit-complement carry-asymmetry pencil $C _ k - S _ {2^k}$, the unweighted Gray-Walsh skew-conference matrix $G _ {2^k}$, and the unshifted Skew-Walsh matrix $W _ {2^k}$.

## For Non-Mathematicians

The Pfaffian is a signed square root of the determinant for skew-symmetric matrices. Most proofs compute the determinant first and lose track of the sign. Here, the signed Pfaffian is computed directly using only exact integer row-and-column operations, proving closed formulas for all matrix sizes $2^k \times 2^k$ built from binary carry counts, Gray codes, and bitwise AND parity — including an exact contrast showing that removing a single 1-bit Gray shift collapses exponential Mersenne-power Pfaffians $(2^k - 1)^{2^{k-2}}$ down to $+1$.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `DyadicSkewCongruencePfaffian/Theorems.lean`, definitions in `DyadicSkewCongruencePfaffian/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation. Note that `DyadicSkewCongruencePfaffian/Defs.lean` is part of the trusted base for `Challenge.lean`.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `pfaffian_blockUpperId` | Upper-unitriangular block congruence preserves the signed integer Pfaffian: $\mathrm{Pf}(P^T A P) = \mathrm{Pf}(A)$ for any skew $2r \times 2r$ matrix $A$. |
| `pfaffian_blockSchur_bot` | Fraction-free bottom-right integral block-Schur Pfaffian identity: given $d A _ {01} + Y^T A _ {11} = 0$, $d^{2m} \mathrm{Pf}(A) = \mathrm{Pf}(d^2 A _ {00} - d Y^T A _ {01}^T) \mathrm{Pf}(A _ {11})$. |
| `pfaffian_skewConference_compl` | Skew-conference complementary-minor reflection: for any skew integer matrix $A$ with $A^2 = -\mu I$, leading $2m \times 2m$ block $B$, and trailing $2n \times 2n$ block $D$, $\mathrm{Pf}(D)^2 \mathrm{Pf}(A) = \mu^n \mathrm{Pf}(D) \mathrm{Pf}(B)$. |
| `pfaffian_carry_dyadic` | Exact dyadic collapse for the carry-asymmetry pencil at $(a, b) = (1, -1)$: $\mathrm{Pf}(C _ k - S _ {2^k}) = (-1)^{2^{k-1}} 2^{2^k - 1}$ for all $k \ge 1$. |
| `pfaffian_grayWalsh_pow2` | Unweighted Gray-Walsh signed Mersenne-power Pfaffian: $\mathrm{Pf}(G _ {2^k}) = 1$ ($k = 1$), $-3$ ($k = 2$), and $(2^k - 1)^{2^{k-2}}$ for all $k \ge 3$. |
| `pfaffian_skewWalsh` | Skew-Walsh unimodularity: removing the 1-bit Gray shift gives $\mathrm{Pf}(W _ {2^k}) = 1$ for all $k \ge 1$. |
| `sharpness_raw_carry_no_complement` | Counterexample at $k = 2$: removing bit-complement from `carryAsymMat` collapses $\mathrm{Pf}$ from $3$ to $0$. |
| `sharpness_shifted_skewWalsh` | Counterexample at $k = 2$: shifting Skew-Walsh indices by $s = 2$ breaks unimodularity ($\mathrm{Pf} = 3$), whereas $s = 1$ gives $1$. |

## Prior-Art Context

- **Classical background:** Cayley's Pfaffian identities ($\mathrm{Pf}(P^T A P) = \det(P) \mathrm{Pf}(A)$, $\det(A) = \mathrm{Pf}(A)^2$) and Jacobi's complementary-minor identity are classical (see also Ishikawa & Wakayama, *Linear and Multilinear Algebra* 39 (1995), 285–292, and D. E. Knuth, "Overlapping Pfaffians", *Electron. J. Combin.* 3(2) (1996), #R5). Skew-Hadamard / skew-conference matrices go back to Paley (1933) and Williamson (1944).
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest.
