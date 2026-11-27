# Pure-Silicon Spectral Conjugacy Engine: Walsh–Defect, Weyl–Heisenberg & Hyperplane-Rotation Lifting (`specmat-16`) (`walsh-gray-conjugacy-spectra`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **86 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** *The Walsh–Defect, Binary Weyl–Heisenberg & Hyperplane-Rotation Spectral Conjugacy Engine* (`SiliconSpectral` in [Proof.lean](file:///c:/Users/devin/Desktop/math/silicon-infinite-mechanisms-20261126/specmat-16/Proof.lean)). **Silicon Principle (Finite-Width Circuit $\to$ Infinite-Width $2^k \times 2^k$ Spectral Lift):** Directly computing matrix powers, eige*

## For Mathematicians

**Mechanism Name:** *The Walsh–Defect, Binary Weyl–Heisenberg & Hyperplane-Rotation Spectral Conjugacy Engine* (`SiliconSpectral` in [Proof.lean](file:///c:/Users/devin/Desktop/math/silicon-infinite-mechanisms-20261126/specmat-16/Proof.lean)). **Silicon Principle (Finite-Width Circuit $\to$ Infinite-Width $2^k \times 2^k$ Spectral Lift):** Directly computing matrix powers, eigenspace multiplicities, or power traces of a $2^k \times 2^k$ bit-indexed integer operator $W _ k P _ A \in M _ {2^k}(\mathbb{Z})$ (where $W _ k[x, y] = (-1)^{\langle x, y \rangle}$ is the unnormalized Walsh–Hadamard matrix and $P _ A$ is the permutation matrix of an invertible $\mathbb{F} _ 2$-linear bit-circuit $A \in \mathrm{GL} _ k(\mathbb{F} _ 2)$) faces exponential $2^k \times 2^k$ dimension blowup. Our reusable engine collapses this $2^k$-dimensional integer spectral problem to **$k$-bit pure-silicon circuit certificates** via three composable lifting pillar

## For Non-Mathematicians

**Mechanism Name:** *The Walsh–Defect, Binary Weyl–Heisenberg & Hyperplane-Rotation Spectral Conjugacy Engine* (`SiliconSpectral` in [Proof.lean](file:///c:/Users/devin/Desktop/math/silicon-infinite-mechanisms-20261126/specmat-16/Proof.lean)). **Silicon Principle (Finite-Width Circuit $\to$ Infinite-Width $2^k \times 2^k$ Spectral Lift):** Directly computing matrix powers, eige

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `WalshGrayConjugacySpectra/Theorems.lean`, definitions in `WalshGrayConjugacySpectra/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `walsh_perm_conj` | Contragredient Law: W_k P_A = P_{A^{-T}} W_k (exact over ℤ, ∀ k). |
| `spectral_period_lift` | Finite-to-Infinite Periodicity Lift: if Δ(A)^d = id on V_k, then (W_k P_A)^{2d} = 2^{kd} I. |
| `even_symmetric_projectors` | Machine-checked infinite theorem `even_symmetric_projectors` proved in pure Lean 4 `Init`. |
| `hyperplane_even_trace_lift` | Pillar 3c: Exact Even-Power Necklace Trace Formula! For any HyperplaneRotCert k n r A (n ≥ 1) and any m ∈ ℕ, letting g = gcd(m, n) and q = n / g: Tr((W_k P_A)^{2m}) = 2^{km + r + (if q % 2 = 0 then g else g - 1)}. |
| `walsh_gray_mod4_antisym` | THEOREM A4 (Gray–Walsh Mod-4 Spectral Symmetry & Odd-Trace Vanishing): ∀ r ∈ ℕ, at width k = 4r + 1, the explicit Weyl–Heisenberg operator U = D_{G_k b} T_b (with alternating b) anticommutes with W_k P_{G_k}, forcing Tr((W_k P_{G_k})^{2m+1}) = 0 ∀ m ∈ ℕ and E_λ ≅ E_{-λ}. |
| `walsh_bitrev_parity_dichotomy_odd` | THEOREM C1 (Bit-Reversal Spectral Parity Dichotomy): (W_k P_{R_k})^2 = 2^k I ∀ k, with: - Odd width k = 2r + 1: balanced (Tr = 0 via Weyl–Heisenberg anticommutator); - Even width k = 2r (r ≥ 1): asymmetric by 2^r, with exact integer projector traces giving m_+ = 2^{2r-1} + 2^{r-1} and m_- = 2^{2r-1} - 2^{r-1}. |
| `walsh_gray_rot_period` | THEOREM D1 (Gray ∘ Butterfly-Rotation 2k-Cycle Periodicity): ∀ k ≥ 2, (W_k P_{G_k C_k})^{2k} = 2^{k^2} I_{2^k}. |
| `sharp_nonlinear_inc2_not_scaled_perm` | Machine-checked infinite theorem `sharp_nonlinear_inc2_not_scaled_perm` proved in pure Lean 4 `Init`. |

## Prior-Art Context

- - **Classical Prior Art (Explicitly Credited):** 1. The contragredient relation $W _ k P _ A W _ k^{-1} = P _ {A^{-\top}}$ is classical Pontryagin duality for $\mathrm{GL} _ k(\mathbb{F} _ 2)$ acting on $\mathbb{F} _ 2^k$, and appears in Clifford/stabilizer circuit synthesis as transversal Hadamard conjugation of CNOT/linear reversible circuits ($H^{\otimes k} P _ A H^{\otimes k} = P _ {A^{-\top}}$). 2. The binary Weyl–Heisenberg (Pauli) commutation relation $T _ b D _ a = (-1)^{\langle a, b \rangle} D _ a T _ b$ and symplectic/Clifford anticommutation are standard foundations of Boolean harmonic analysis and stabilizer formalism. 3. The fixe
- Hostile-verified PASS by `referee-3`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).