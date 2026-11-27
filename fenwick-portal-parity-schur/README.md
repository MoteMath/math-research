# Dual Pure-Silicon Mechanisms for Bit-Indexed Spectral & Inversion Towers: Division-Free 6-Tuple Portal-Transfer & Even/Odd Bit-Parity Schur Interleaving (`fenwick-portal-parity-schur`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): We introduce **two composable, division-free pure-silicon infinite proof mechanisms** formalized over an arbitrary commutative ring $R$ (instantiated on $\mathbb{Z}$ and the exact polynomial / formal power series ring $\mathbb{Z}[[X]]$):*

## For Mathematicians

We introduce **two composable, division-free pure-silicon infinite proof mechanisms** formalized over an arbitrary commutative ring $R$ (instantiated on $\mathbb{Z}$ and the exact polynomial / formal power series ring $\mathbb{Z}[[X]]$):

## For Non-Mathematicians

We introduce **two composable, division-free pure-silicon infinite proof mechanisms** formalized over an arbitrary commutative ring $R$ (instantiated on $\mathbb{Z}$ and the exact polynomial / formal power series ring $\mathbb{Z}[[X]]$):

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `FenwickPortalParitySchur/Theorems.lean`, definitions in `FenwickPortalParitySchur/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `portalTuple_perturb` | Machine-checked infinite theorem `portalTuple_perturb` proved in pure Lean 4 `Init`. |
| `bordered_schur_inv` | Bordered Dyadic/Scaled Inverse Lemma (Theorem B2): If `A` is a symmetric bordered matrix `[[0, u^T], [u, B]]` of size `n + 1`, `B * Binv = I_n`, `w = Binv * u`, and `u^T * w = σ`, then `J = [[-1, w^T], [w, σ * Binv - w * w^T]]` satisfies `A * J = σ * I_{n+1}`! |
| `fenwickUQ_unimodular` | Theorem 1b (Unimodularity): Deleting portal `0` yields `det(A(G_k(c)) \ {0}) = 1` for ALL `k ≥ 2`! |
| `fenwickUQLap_charpoly_fps` | Theorem 2d (Exact Laplacian Polynomial-Ring `Z[X]` Instantiation via `FPS`): |
| `fenwickUQLap_spanning_tree_square` | Theorem 4b (Spanning-Tree Perfect-Square Law): By Kirchhoff's Matrix-Tree Theorem, the spanning-tree count `τ(G_{k+1}) = det(L(G_{k+1}) \ {0})` is ALWAYS a perfect square `(tauSeq k + dSeq k)^2` for ALL `k ≥ 1`! |
| `inOrderHeap_charpoly_factorization` | Theorem 6b (Binary Heap `H_k` Characteristic Polynomial Factorization over ANY `CRing R`, `∀ k ≥ 1`): |
| `witness_dyadic_inv_k2` | Witness 6: Exact 1/4-dyadic inverse `A(G_2) * J_2 = 4 * I_5` and `A(G_3) * J_3 = 4 * I_9`. |
| `sharpness_asymmetric_weights_k2` | Counterexample 3 (query/update weights `1`/`2` instead of equal weights): giving query edges `(i, i - lowbit i)` weight `1` and update edges `(i, i + lowbit i)` weight `2` gives `det = -24 ≠ -4` already at `k = 2` (`5 × 5`)! |

## Prior-Art Context

- Formalizes a pure-Init Lean 4 infinite proof engine with zero Mathlib dependencies and independent `nanoda` kernel verification.
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).