# Bitwise Smith Normal Form Lifter - exact Smith normal forms of 2^k x 2^k carry, add-XOR and bitwise-AND matrices lifted from bit-slice engines (`bitwise-smith-normal-form-lifter`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a constructive Smith normal form engine (explicit GL_n(Z) unimodular equivalences, canonical divisibility chains) with five composable bit-slice lifters. Proves exact Smith normal forms for every k of carry-parity matrices (flat sign case with invariants 1 and 2), the add-XOR collapse matrix, the bitwise-AND matrix with invariants 2^i, and unimodularity of the 2^popcount(x AND y) matrix, together with the torsion obstruction and the Kummer carry identity.*

## For Mathematicians

**Mechanism:** **Constructive Unimodular Bit-Slice SNF Lifting Engine** (implemented standalone in core Lean 4.34.1, zero Mathlib, zero float, zero `sorry`, zero `native_decide`). **Pure-Silicon Principle (Finite $\to$ Infinite Bridge):** Rather than relying on rational Gaussian elimination, determinants, or floating-point spectral approximations, every unimodular transformation $U \in GL _ n(\mathbb{Z})$ is represented constructively by an explicit two-sided integer inverse pair `(val, inv : Mat n)` with $U U^{-1} = U^{-1} U = I _ n$, and canonical Smith Normal Form `HasSNF M d` requires both an explicit unimodular equivalence $U M V = \mathrm{diag}(d _ 0, \dots, d _ {n-1})$ ($d _ i \in \mathbb{N}$) and the full divisibility chain $d _ 0 \mid d _ 1 \mid \dots \mid d _ {n-1}$. To prove the **entire** $2^k \times 2^k$ SNF diagonal $\forall k \ge 1$ from finite $2 \times 2$ bit-slice structure, the engine provides **five c

## For Non-Mathematicians

A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a constructive Smith normal form engine (explicit GL_n(Z) unimodular equivalences, canonical divisibility chains) with five composable bit-slice lifters. Proves exact Smith normal forms for every k of carry-parity matrices (flat sign case with invariants 1 and 2), the add-XOR collapse matrix, the bitwise-AND matrix with invariants 2^i, and unimodularity of the 2^popcount(x AND y) matrix, together with the torsion obstruction and the Kummer carry identity.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BitwiseSmithNormalFormLifter/Theorems.lean`, definitions in `BitwiseSmithNormalFormLifter/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `hasSNF_torsion_obstruction` | Theorem 1 (Torsion obstruction): if M has Smith normal form d and some invariant d i exceeds 1, there is a right-hand side b not hit by M while d i times b is hit. |
| `carriesK_kummer` | Theorem 2 (Kummer carry identity): for x, y < 2^k and carry-in c <= 1, carries + popcount(x + y + c) = popcount x + popcount y + c. |
| `snf_affine_carry_parity` | Theorem 3 (Affine carry-parity SNF): for every k >= 1 and integers a, b, the affine carry-parity matrix has the explicit Smith normal form affineCarrySNFDiag. |
| `snf_carry_sign_flat` | Theorem 4 (Flat carry-sign SNF): for k >= 1 the (-1)^carries matrix has Smith normal form (1, 2, 2, ..., 2) on 2^k indices. |
| `snf_carry_parity_one_dichotomy` | Theorem 5 (Odd/even dichotomy): the carry-parity matrix at parameter 1 is unimodular for odd k and has a single zero invariant for even k. |
| `snf_DMat` | Theorem 6 (Add-XOR collapse): the add-XOR matrix DMat k has Smith normal form given by addXorSNFDiag for every k. |
| `snf_bitwise_and` | Theorem 7 (Bitwise-AND SNF): the 2^k x 2^k matrix x AND y has Smith normal form with invariants 2^i for i < k and 0 otherwise. |
| `snf_two_pow_popcount_and_unimod` | Theorem 8 (Unimodular popcount-AND): the matrix 2^popcount(x AND y) is unimodular (all invariants 1) for every k. |

## Prior-Art Context

- - **Classical prior art (explicitly credited):** Multiplicative Kronecker SNF (Newman 1972, *Integral Matrices*) and the binomial SNF $(2^j)^{\binom{k}{j}}$ of Sylvester/Walsh-Hadamard matrices are classical. Theorem 4 is included intentionally as a reusable Kronecker component and direct baseline against Theorem 1's carried counterpart. - **Anti-duplication check (CHARTER Section 4):** Distinct from `carry-determinants` and `carry-blocks-determinants` (base-$B$ Holte/Markov carry transition matrix determinants) and `clmul-lift-determinants` (carryless multiplication determinants; we do not use `clmul` at all). - **What is genuinely new:** 1.
- Hostile-verified PASS by `referee-3`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).