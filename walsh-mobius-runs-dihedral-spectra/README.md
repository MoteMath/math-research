# Walsh-Hadamard and Boolean-Lattice Mobius Diagonalization Engine (`walsh-mobius-runs-dihedral-spectra`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): exact all-dimension determinants and characteristic polynomials of $2 ^ k \times 2 ^ k$ XOR-convolution and AND-lattice matrices through bit-automaton Walsh and Mobius transfer compilers, with a closed-form Pell-type spectrum for the runs kernel, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

For $f : \mathbb{N} \to \mathbb{Z}$, the XOR-convolution matrix $C _ f (x, y) = f(x \oplus y)$ on $[0, 2 ^ k)$ is diagonalized by the Walsh-Hadamard transform, and we prove $\det C _ f = \prod _ u \mathrm{wht} _ k (f)(u)$ and $\det(\lambda I - C _ f) = \prod _ u (\lambda - \mathrm{wht} _ k (f)(u))$ with a purely integer Leibniz determinant (`det_xorConv`, `charPoly_xorConv`). Likewise the AND-lattice (meet) matrix $g(x \mathbin{\&} y)$ has determinant equal to the product of the Mobius down-transform values (`det_andLattice`).

The new ingredient is a **bit-automaton transfer compiler** (`wht_transfer_compiler`, `mobiusDown_transfer_compiler`, `scaledDihedral_collapse`): if $f$ is computed by a $d$-state bit-automaton then so is its Walsh transform, with a state count independent of $k$. Applied to the runs kernel (number of runs of the bit string) this yields the closed-form spectrum $\prod _ u (1 - q) ^ r \cdot \mathrm{pellQ}(q, k + 1 - 2 r)$ (`det_runs_xorConv`), singularity at $q = -1$ for every odd exponent (`runs_xorConv_neg_one_singular_odd`), unimodularity $\det = -1$ of the two-runs AND-lattice for all $k \ge 2$ (`det_two_runs_andLattice_unimodular`), and a proof that the runs AND-lattice is never positive definite (`runs_andLattice_never_posdef`).

## For Non-Mathematicians

Take a grid whose entry in row $x$ and column $y$ depends only on the bitwise XOR (or AND) of the two row and column numbers. Such grids have a hidden structure that lets their determinant be read off from a quick transform of a single sequence. We prove the exact formula for every grid size at once, show that if the sequence is produced by a small bit-by-bit machine then so is its transform, and deduce exact answers for grids built from run counts, including exactly when they are singular, have determinant $-1$, or fail to be positive definite.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `WalshMobiusRunsDihedralSpectra/Theorems.lean`, definitions in `WalshMobiusRunsDihedralSpectra/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `det_xorConv` | For every $k$ and $f$, the determinant of the XOR-convolution matrix of $f$ on $2 ^ k$ points equals the product of the Walsh-Hadamard transform values of $f$. |
| `charPoly_xorConv` | For every $k$, $f$ and $\lambda$, $\det(\lambda I - C _ f) = \prod _ u (\lambda - \mathrm{wht} _ k (f)(u))$. |
| `det_andLattice` | For every $k$ and $g$, the determinant of the AND-lattice matrix of $g$ equals the product of the Mobius down-transform values of $g$. |
| `wht_transfer_compiler` | For any bit-automaton $A$ with $d$ states and every width $k$, the Walsh-Hadamard transform of the sequence computed by $A$ is computed by an explicit bit-automaton of the same size. |
| `det_runs_xorConv` | For every $q$ and $k$, the determinant of the XOR-convolution matrix of the runs kernel is the explicit product of Pell-type factors $(1 - q) ^ r \cdot \mathrm{pellQ}(q, k + 1 - 2 r)$ over $u$. |
| `runs_xorConv_neg_one_singular_odd` | For every $m$, the XOR-convolution matrix of the runs kernel at $q = -1$ on $2 ^ {2 m + 1}$ points is singular. |
| `det_two_runs_andLattice_unimodular` | For every $k \ge 2$, the AND-lattice matrix of the runs kernel at $q = 2$ has determinant exactly $-1$. |
| `runs_andLattice_never_posdef` | For every $q$ and $k \ge 2$ there is a nonzero integer vector with nonpositive quadratic form for the runs-kernel AND-lattice matrix. |

## Proof Architecture

1. **Exact integer determinant calculus (`det_mul`, `det_xorConv`, `charPoly_xorConv`, `det_andLattice`, `det_orLattice`):** Leibniz determinants with no reals, diagonalizing by exact Walsh and Mobius conjugations.
2. **Transfer compilers (`wht_transfer_compiler`, `mobiusDown_transfer_compiler`):** transform a $d$-state bit-automaton into the automaton of its Walsh or Mobius transform, so spectra are computed in $O(d)$ per width.
3. **Dihedral collapse (`scaledDihedral_collapse`):** a finite certificate certifies that scaled dihedral transforms stay in the automaton class for all widths.
4. **Runs-kernel spectrum and sharpness (`det_runs_xorConv`, `runs_xorConv_neg_one_singular_odd`, `det_two_runs_andLattice_unimodular`, `runs_andLattice_never_posdef`, `sharpness_*`):** closed-form Pell-type spectrum, singularity, unimodularity and failure of positive definiteness, with kernel-checked boundary cases.

## Prior-Art Context

- **Classical foundations:** diagonalization of XOR-convolution (dyadic circulant) matrices by Sylvester-Walsh-Hadamard matrices (Sylvester 1867; Walsh 1923), and determinant factorization of meet matrices $g(x \wedge y)$ on finite posets via the zeta-matrix congruence and Mobius function, the Smith-Lindstrom-Wilf theorem (Smith 1875; Wilf 1968; Lindstrom 1969).
- **Referee audit (referee-3 PASS #195; recorded in `REGISTRY.md`):** the bit-automaton Walsh and Mobius transfer compilers, the scaled-dihedral collapse certificate, the closed-form runs-kernel spectrum, odd-dimension singularity and unimodular two-runs AND-lattice are new; zero Section 4 overlap.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
