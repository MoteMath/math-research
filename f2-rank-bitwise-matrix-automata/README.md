# Exact F2-Rank and Corank Block-Elimination Automaton Engine (`f2-rank-bitwise-matrix-automata`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): exact $\mathbb{F} _ 2$ rank, nullity and kernel cardinality for arbitrary (not only power-of-two) $n \times n$ bit-indexed matrices via block elimination, including the exact nullity of the carry-free XOR-sum parity matrix and a base-4 automaton invertibility criterion, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Most bitwise linear-algebra theorems concern sizes $2 ^ k$ or determinants, which vanish identically on singular matrices and carry no information about rank or corank. For arbitrary $n \times n$ matrices over $\mathbb{F} _ 2$ we build a block-elimination engine (`HasRank`, `LinEquiv`, `hasRank_schur_inv`) proving rank uniqueness (`hasRank_unique`) and the exact kernel-count law $|\ker M| = 2 ^ {n - r}$ (`hasRank_kerCount`), plus an **isotropic rank-one decoupling** theorem: a symmetric block $A$ with an isotropic preimage $x$ of $u$ makes the coupled block matrix of rank $\mathrm{rank}(A) + \mathrm{rank}(B)$ (`hasRank_isotropic_rank1_decouple`).

Applications for all $n$: the carry-free XOR-sum parity matrix $M _ 0 (i, j) = \mathrm{popcount}((i + j) \mathbin{\&} (i \oplus j)) \bmod 2$ has nullity exactly $\mathrm{popcount}(\mathrm{gray}(n - 1)) - 1$ for $n \ge 2$, hence exactly $2 ^ {\mathrm{popcount}(\mathrm{gray}(n - 1)) - 1}$ kernel vectors, and is invertible if and only if $n = 2 ^ k$ with $k \ge 1$ (`M0_gray_nullity`, `M0_kerCount`, `M0_invertible_iff_pow2`); a Hamming-type family $H _ d$ has kernel size $2 ^ {\mathrm{hcNullity}(d, n)}$ and $H _ 0$ is invertible iff the base-4 digit DFA accepts $n$ (`H_kerCount`, `H0_invertible_iff_base4`).

## For Non-Mathematicians

A grid of ones and zeros is "invertible" if you can undo its action, and the question of how far from invertible it is (its rank) is hard for general grids. For grids defined by bit tricks we give exact answers for every size, whether or not it is a power of two: how many input patterns it sends to zero, and exactly which sizes give an invertible grid, namely the powers of two for the carry-free parity grid and a simple base-4 digit test for a second family.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `F2RankBitwiseMatrixAutomata/Theorems.lean`, definitions in `F2RankBitwiseMatrixAutomata/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `hasRank_kerCount` | If an $m \times n$ matrix $M$ over $\mathbb{F} _ 2$ has rank $r$, then it has exactly $2 ^ {n - r}$ kernel vectors. |
| `hasRank_unique` | The $\mathbb{F} _ 2$ rank of a matrix is unique: $\mathrm{HasRank}(M, r _ 1)$ and $\mathrm{HasRank}(M, r _ 2)$ imply $r _ 1 = r _ 2$. |
| `hasRank_isotropic_rank1_decouple` | For a symmetric $A$ with $A x = u$ and $u \cdot x = 0$, the block matrix with off-diagonal rank-one blocks $u v ^ T$ and $v u ^ T$ has rank $r _ A + r _ B$. |
| `M0_gray_nullity` | For every $n \ge 2$, the carry-free XOR-sum parity matrix $M _ 0 (n)$ has nullity $\mathrm{popcount}(\mathrm{gray}(n - 1)) - 1$. |
| `M0_kerCount` | For every $n \ge 2$, $M _ 0 (n)$ has exactly $2 ^ {\mathrm{popcount}(\mathrm{gray}(n - 1)) - 1}$ kernel vectors. |
| `M0_invertible_iff_pow2` | For every $n \ge 1$, $M _ 0 (n)$ has full rank over $\mathbb{F} _ 2$ if and only if $n = 2 ^ k$ for some $k \ge 1$. |
| `H_kerCount` | For every flag $d$ and every $n$, the kernel of the Hamming-type matrix $H _ d (n)$ has exactly $2 ^ {\mathrm{hcNullity}(d, n)}$ vectors. |
| `H0_invertible_iff_base4` | For every $n$, $H _ 0 (n)$ has full rank if and only if the base-4 digit automaton accepts $n$. |

## Proof Architecture

1. **Block-elimination chassis (`HasRank`, `LinEquiv`, `hasRank_schur_inv`):** rank is tracked through invertible row and column operations and Schur complements.
2. **Kernel-count law (`hasRank_kerCount`, `hasRank_unique`):** rank determines $|\ker M|$ exactly, so nullity theorems become exact solution counts.
3. **Isotropic decoupling (`hasRank_isotropic_rank1_decouple`):** an isotropic preimage cancels the rank-one coupling, so ranks add across the recursion in $n$.
4. **Parity and Hamming families (`M0_gray_nullity`, `M0_invertible_iff_pow2`, `H_kerCount`, `H0_invertible_iff_base4`, `sharp_*`):** closed forms by induction on the binary expansion of $n$, with kernel-checked counterexamples when carry-in, bitwise-or or Hamming distance 2 replace the hypotheses.

## Prior-Art Context

- **Classical background:** Kronecker, Walsh-Hadamard and Sierpinski-type bit matrices are classical for sizes $2 ^ k$; rank over $\mathbb{F} _ 2$ by Gaussian elimination and the Schur complement rank formula (Guttman 1946; Haynsworth 1968) are standard. Gray-code popcount identities are classical (Knuth, TAOCP Vol. 4A).
- **Contents (not independently reviewed; no prior-art search is recorded):** the exact rank, nullity and kernel-cardinality engine for arbitrary non-power-of-two $n$, the isotropic rank-one decoupling, the exact Gray-popcount nullity of $M _ 0$ and the base-4 DFA invertibility criterion for $H _ 0$.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
