# Pure-Silicon 2-Adic Dual-Basis Certificate Engine (`adic-1`) (`mahler-vanderput-2adic-certs`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism:** **2-Adic Dual-Basis Certificate Engine (Rooted Van der Put Basis + Discrete Mahler Forward-Difference Basis + Finite 2-Adic Lattice Contraction, Sharpness, and Kernel-Invariant Compilers)** **Silicon Principle (Finite $\to$ Infinite Bridge):** In standalone Lean 4.35.0 (zero Mathlib, zero floats), we model the ring of 2-adic integers $\mathbb{Z} _ 2$ natively as*

## For Mathematicians

**Mechanism:** **2-Adic Dual-Basis Certificate Engine (Rooted Van der Put Basis + Discrete Mahler Forward-Difference Basis + Finite 2-Adic Lattice Contraction, Sharpness, and Kernel-Invariant Compilers)** **Silicon Principle (Finite $\to$ Infinite Bridge):** In standalone Lean 4.35.0 (zero Mathlib, zero floats), we model the ring of 2-adic integers $\mathbb{Z} _ 2$ natively as coherent projective towers of silicon machine words: Ring operations (`+`, `-`, `*`, unary `-`) and bitwise operations (`^^^`, `&&&`, `lsbMask x = x &&& (-x)`) act componentwise on `BitVec w`. Continuity with explicit modulus $\mu : \mathbb{N} \to \mathbb{N}$ is simply the machine-word compatibility law: The engine lifts finite integer certificates to universally quantified theorems over **all** $x \in \mathbb{Z} _ 2$ (including non-natural 2-adic integers such as $-1 = \dots 1111 _ 2$ and $(1 - q)^{-1}$) via three interlocked layers: 1. **Rooted Van der Put Basis

## For Non-Mathematicians

**Mechanism:** **2-Adic Dual-Basis Certificate Engine (Rooted Van der Put Basis + Discrete Mahler Forward-Difference Basis + Finite 2-Adic Lattice Contraction, Sharpness, and Kernel-Invariant Compilers)** **Silicon Principle (Finite $\to$ Infinite Bridge):** In standalone Lean 4.35.0 (zero Mathlib, zero floats), we model the ring of 2-adic integers $\mathbb{Z} _ 2$ natively as

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `MahlerVanderput2adicCerts/Theorems.lean`, definitions in `MahlerVanderput2adicCerts/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `vdp_reconstruct` | Theorem 2A.1: Exact Finite Van der Put Reconstruction on `BitVec w`. |
| `z2_density_identity` | Universal Density Identity Principle on `Z2`: Any two continuous functions on `Z2` that agree on `Nat` agree on ALL of `Z2`. |
| `q_gray_alternating_duality_even` | THEOREM Ia (Infinite q-Deformed Gray-Alternating 2-Adic Duality — Even Branch): For EVERY even `q : Int` and EVERY `x : Z2`: `Θ_q((2x) ^^^ x) = -(q - 1) * Φ_q(x)`. |
| `theta2_bitwise_inverse_Z2` | COROLLARY (Exact Closed-Form Bitwise Inverse of Alternating Binary `Θ_2` on all of `Z2`): `∀ x : Z2, Θ_2((-2x) ^^^ (-x)) = x`. |
| `triadic_holder_2_3_sharp` | THEOREM IIa (Sharpness Lower Bound via Compiler B): NO extension of `u_tri · g_tri` to `Z2` can achieve modulus `μ(3k) > 2k` for ANY `k`! |
| `shear_carry_1lipschitz_sharp` | THEOREM IIb (Exact Period-2 Sharpness Lower Bound via Compiler B): NO extension can achieve modulus `μ(2k) > 2k`! |
| `exp2c_neg_one_inv` | Non-vacuity witness at `x = -1 ∈ Z2`: `(1 + 2c)^(-1) * (1 + 2c) = 1` in `Z2`! |
| `nonvacuity_all_compilers` | Explicit kernel-checked non-vacuity witnesses for all three finite certificate engines. |

## Prior-Art Context

- - **Classical Foundations (Distinguished Honestly):** - Mahler's continuity theorem (1958), the van der Put basis (1968), ultrametric $p$-adic calculus (Schikhof, *Ultrametric Calculus*, 1984), Anashin's 1-Lipschitz criteria in both bases (Anashin & Khrennikov, *Applied Algebraic Dynamics*, 2009), and Mahler/van der Put basis-conversion theory (Jeong, 2013) are classical theorems of $p$-adic analysis. - 2-regular integer sequences and matrix representations follow Allouche & Shallit (*Automatic Sequences*, 2003); bit-dilation / Z-order curves and lowbit carry tricks trace to Morton (1966), HAKMEM, and Warren (*Hacker's Delight*), and the $q =
- Hostile-verified PASS by `referee-4`; pure `leanprover/lean4:v4.35.0` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).