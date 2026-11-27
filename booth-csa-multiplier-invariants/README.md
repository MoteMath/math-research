# Bipartite Booth–CSA Infinite Proof Engine (`RadixTransducer` + `GuardNormalizerSpec`) (`booth-csa-multiplier-invariants`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): We construct a **two-engine pure-silicon infinite proof compiler** for arbitrary-width, arbitrary-depth Booth and Carry-Save multiplier architectures ($\forall k \ge 1,\; \forall w \ge 1,\; \forall m \ge 1$): 1. **Mechanism I — `RadixTransducer` & `FiniteRadixCert` (Finite-State Affine-Potential Compiler):** - A finite-state base-$B$ transducer $(Q, A, \mathrm{step}, \delta, \p*

## For Mathematicians

We construct a **two-engine pure-silicon infinite proof compiler** for arbitrary-width, arbitrary-depth Booth and Carry-Save multiplier architectures ($\forall k \ge 1,\; \forall w \ge 1,\; \forall m \ge 1$): 1. **Mechanism I — `RadixTransducer` & `FiniteRadixCert` (Finite-State Affine-Potential Compiler):** - A finite-state base-$B$ transducer $(Q, A, \mathrm{step}, \delta, \phi, \mathrm{inv})$ whose transitions satisfy a single finite local balance check: - **Finite $\to$ Infinite Lift (`RadixTransducer.lift_sum`, `FiniteRadixCert.lift_sum`):** Checking the finite transition table (automatically via kernel `decide` for `Fin nQ × Fin nA` tables in `FiniteRadixCert.check`, or symbolically for parametric radix $B = 2^k$) discharges the exact infinite-length telescoping identity for **all** $n \in \mathbb{N}$ and **all** input streams $a : \mathbb{N} \to A$: - Instantiated simultaneously on: - the 2-state **Universal Radix-$2^k$ Booth Ove

## For Non-Mathematicians

We construct a **two-engine pure-silicon infinite proof compiler** for arbitrary-width, arbitrary-depth Booth and Carry-Save multiplier architectures ($\forall k \ge 1,\; \forall w \ge 1,\; \forall m \ge 1$): 1. **Mechanism I — `RadixTransducer` & `FiniteRadixCert` (Finite-State Affine-Potential Compiler):** - A finite-state base-$B$ transducer $(Q, A, \mathrm{step}, \delta, \p

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BoothCsaMultiplierInvariants/Theorems.lean`, definitions in `BoothCsaMultiplierInvariants/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `csa3to2_exact_mod` | For all `W, a, b, c`: `(csaSum W a b c + csaCarry W a b c) mod 2^W = (a + b + c) mod 2^W` (correctness of the 3:2 carry-save compressor modulo `2^W`). |
| `lift_all_widths` | INFINITE-WIDTH LIFTING THEOREM (Mechanism II): Any finite top-`g`-bit guard specification lifts to EXACT unwrapped integer conservation `signedVal W S' + signedVal W C' = V` for ALL bit-widths `W ≥ g` and ALL pairs `(S, C)` whose modular sum lies in the allowed slabs! |
| `zeroCarryTop_exact` | THEOREM 1 (Exact g-Bit Zero-Carry-Top Normalizer, ∀ g ≥ 2, ∀ W ≥ g): For ANY `g ≥ 2`, ANY width `W ≥ g`, and ANY Carry-Save pair `(S, C)` whose modular sum `V` lies in the asymmetric range `[-2^(W-1) + 2^(W-g), 2^(W-1) - 1]`: 1. `signedVal W S' + signedVal W C' = V` EXACTLY IN `Int` (zero wraparound!) 2. `C' < 2^(W - g)` (top `g` bits of `C'` are identically zero, so `C'` is non-negative!). |
| `unnormalized_csa_rshift_fails` | Sharpness Corollary: Naive unnormalized CSA right-shift fails with error `-2^(W-1)` at `V = 0` ∀ W ≥ 3. |
| `sec_cancellation_exact` | THEOREM 6 (Universal 2-State Radix-`2^k` Sign-Extension Cancellation Law, ∀ k ≥ 1, ∀ W, ∀ m ≥ 1): Directly discharged by Mechanism I (`RadixTransducer.lift_sum`) on `secTransducer`: `∑_{j=0}^{m-1} secTerm_k(j > 0, s_j) * 2^(W + k*j) + ∑_{j=0}^{m-1} s_j * 2^(W + k*j) = 2^(W + k*m)`. |
| `radix4_booth_tree_exact` | THEOREM 8 (Complete Pure-Silicon Radix-4 Booth Tree + SEC Theorem, ∀ w ≥ 1, ∀ m ≥ 1): Combines Booth Transducer (Theorem 5) + Silicon PP (Theorem 7) + 2-State SEC (Theorem 6): 1. `boothTreeSum w m x_u y_u = signedVal w x_u * signedVal (2*m) y_u + 2^(w + 1 + 2*m)` EXACTLY IN `Int`! 2. Modulo `2^(w + 2*m)`, `boothTreeSum` equals the exact `(w + 2*m)`-bit signed product! |
| `booth_acc_endpoints_tight` | Sharpness / Tightness: BOTH `+2^(w+k-2)` and `-2^(w+k-2)` are attained by `A_j'`! |
| `badGuardCert_g2_rejected` | Machine-checked finite instance: the specific certificate `badGuardCert_g2_cutArc` (a deliberately wrong `g = 2` guard specification) is rejected by `check`. |

## Prior-Art Context

- - **Classical Literature Distinguished:** - Radix-2 Booth recoding (Booth 1951), Radix-4 Modified Booth recoding (MacSorley 1961), sign-extension elimination for Radix-4 (Bewick 1994; Fadavi-Ardekani 1993; Kuang–Wang–Guo 2009), redundant carry-save / signed-digit recoding & normalization (Kornerup 1994, 2009; Ercegovac–Lang; Burgess; Nannarelli) are classical hardware design techniques. - **Contribution (prior-art status not established; no search was recorded):** 1. **Unified Bipartite Finite-to-Infinite Proof Compilers (`RadixTransducer`/`FiniteRadixCert` + `GuardNormalizerSpec`/`FiniteGuardCert`):** Rather than hand-proving one fixed-width multiplier or transcribing prose proofs, fin
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).