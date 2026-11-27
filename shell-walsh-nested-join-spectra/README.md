# The 2-Adic Shell-Walsh Nested-Join & Carry-Butterfly Spectral/Kirchhoff Engine (`shell-walsh-nested-join-spectra`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** *The 2-Adic Shell-Walsh Nested-Join & Carry-Butterfly Spectral/Kirchhoff Engine*.*

## For Mathematicians

**Mechanism Name:** *The 2-Adic Shell-Walsh Nested-Join & Carry-Butterfly Spectral/Kirchhoff Engine*.

## For Non-Mathematicians

**Mechanism Name:** *The 2-Adic Shell-Walsh Nested-Join & Carry-Butterfly Spectral/Kirchhoff Engine*.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `ShellWalshNestedJoinSpectra/Theorems.lean`, definitions in `ShellWalshNestedJoinSpectra/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `det_mul` | Multiplicativity of the exact integer determinant: `det (A * B) = det A * det B`. |
| `orthogonal_eigenbasis_kirchhoff` | **Master Orthogonal-Eigenbasis Kirchhoff Spanning-Tree Lifting Theorem**: For ANY `(m+1) x (m+1)` Laplacian `L` (zero row & column sums) diagonalized by an orthogonal integer matrix `Q` (`Q^T Q = diag d`, `d i ≠ 0`) whose column 0 is all 1s and `lam 0 = 0`, the exact Kirchhoff spanning-tree cofactor satisfies: `(m + 1) * det (L^{(0,0)}) = ∏_{j=1}^m lam j`. |
| `shellLaplacian_kirchhoff` | **REUSABLE ENGINE COROLLARY 2 (Exact Kirchhoff Spanning-Tree Cofactor of ALL 2-Adic Shell-Walsh Graphs)**: For ALL `k : Nat`, ALL `c : Nat -> Int`, ALL `phi : Nat -> Nat -> Int` (with `m = 2^k - 1` so `m + 1 = 2^k`): `2^k * det (minor00 (shellLaplacian k c phi)) = ∏_{j=1}^{2^k - 1} shellEig k c phi j`. |
| `carryXorLaplacian_kirchhoff` | **UNIVERSAL 2-VARIABLE CARRY-XOR KIRCHHOFF SPANNING-TREE THEOREM**: For EVERY `k : Nat` and EVERY arbitrary 2-variable weight function `h : Nat -> Nat -> Int`: `2^k * det (minor00 (carryXorLaplacian k h)) = ∏_{j=1}^{2^k - 1} shellEig k (carryXorC h) (carryXorPhi h) j`. |
| `dyadic_spanning_trees` | **THEOREM A2 (Exact Kirchhoff Spanning-Tree Weight Formula for `w(x,y) = 2^{v2(x+y)}`, ∀ k ≥ 1)**: `det (minor00 (dyadicLaplacian k)) = ∏_{j=1}^{k-1} ((j + 2) * (2k + 2 - j) * (2^{k-1})^2)^{2^{j-1}}`. |
| `evenSum_kirchhoff` | For every $k$, the spanning-tree identity of `carryXorLaplacian_kirchhoff` for the specific weight `evenSumH` (a one-line specialization of that theorem, valid for all $k$). |
| `sharpness_c3_charpoly` | Machine-checked finite instance: for all integers $x$, the characteristic polynomial of the fixed $4 \times 4$ matrix `shifted3Laplacian` is $x(x-2)(x^2-4x+2)$. |
| `witness_nonvacuous_engine` | Non-vacuity witness 4: constructive `Nonempty` witness inhabiting all hypotheses of `orthogonal_eigenbasis_kirchhoff`. |

## Prior-Art Context

- Formalizes a pure-Init Lean 4 infinite proof engine with zero Mathlib dependencies and independent `nanoda` kernel verification.
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Scope of the formal statement

The graphs are the weighted graph Laplacians on $2^k$ vertices defined in `Defs.lean` (`shellLaplacian`, `carryXorLaplacian`, `dyadicLaplacian` with $w(x,y) = 2^{v_2(x+y)}$), with integer determinants and matrices defined from scratch in `Init`. The Kirchhoff, orthogonal-eigenbasis and dyadic spanning-tree theorems are universal in $k$; `sharpness_c3_charpoly` is a statement about one fixed $4 \times 4$ matrix.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).