# Soundness & Axiom Audit (`kronecker-cyclic-frustration`)

## Package Configuration

- **Toolchain**: `leanprover/lean4:v4.34.1`
- **Dependencies**: Pure `Init` only (`lake-manifest.json` has `"packages": []`, zero Mathlib)
- **Comparator Config**: `comparator.json` with `"enable_nanoda": true`, permitted axioms `["propext", "Classical.choice", "Quot.sound"]`
- **Challenge/Solution Separation**:
  - `Challenge.lean` contains ONLY the 6 headline theorem signatures in `KroneckerCyclicFrustrationChallenge` with `sorry` bodies, importing only `KroneckerCyclicFrustration.Defs`.
  - `Solution.lean` proves the exact same 6 theorem signatures in `KroneckerCyclicFrustrationChallenge` with ZERO `sorry`, `admit`, `axiom`, or `native_decide`.

## Verification Checklist

1. **Zero forbidden constructs outside `Challenge.lean`**:
   - No `sorry`, `admit`, `axiom`, `native_decide`, `lemma`, or `unsafe` anywhere in `KroneckerCyclicFrustration/` or `Solution.lean`.
2. **Universal & Non-Vacuous Theorem Statements**:
   - Theorem 1 (`sum_of_two_kronecker_optimal_cond_exact`): Universal over all dimensions $n, m \in \mathbb{N}$ and all positive rational eigenvalues $\alpha _ i, \beta _ j > 0$; both lower bound and closed-form Corner-Geometric-Mean upper/lower attainment are proved.
   - Theorem 2 (`multihead_two_head_zero_frustration_and_kfac_gap`): Universal over all $d \in \mathbb{N}$ and $b _ {1,j}, b _ {2,j} > 0$ for 2-head zero frustration, plus universal $M \ge 1$ K-FAC quadratic penalty $(1 + M)^2 / (4 M)$ and 5 exact rational instances.
   - Theorem 3 (`multihead_cyclic_frustration_karp_cycle_bound`): Universal over all $H, d, L \ge 1$ for cycle-product invariance and Karp cycle lower bound, plus universal $H \ge 2$, $M \ge 1$ cyclic witness separating pairwise $\kappa _ {\mathrm{pair}}^2 \le M^H$ from full $\kappa^H \ge M^{H(H-1)}$.
   - Theorem 4 (`monarch_coherence_factorization_and_lower_bound`): Universal over all $n _ 1, n _ 2 \in \mathbb{N}$ and integer matrices $A, B$ for orthogonality and squared coherence factorization, plus universal $n \in \mathbb{N}$ support lower bound.
   - Theorem 5 (`octonion_sparse_e2m1_monarch_blocks_exact`): Universal over all $a, b, c, d \in \mathbb{Z}$ (`quat4`) and all $c _ 0, \dots, c _ 7 \in \mathbb{Z}$ (`oct8`), plus kernel-checked (`decide`) orthogonality, sparsity, coherence, and `E2M1` grid membership for all $s \in \{1..4\}$ and $s \in \{1..8\}$.
   - Theorem 6 (`kfac_cross_scale_suboptimality_witness`): Universal over all $K > 0$ and all $C \in \mathbb{Q}$ (unbounded K-FAC gap), plus concrete exact rational witness at $K = 128$ (`> 1800x` worse $\kappa^2$).
3. **Axiom Footprint (`scripts/PrintAxioms.lean`)**:
   - Every headline theorem depends ONLY on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero `sorryAx` and zero `Lean.ofReduceBool`.
