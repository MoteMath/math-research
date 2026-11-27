# Cauchy-Hadamard-Frobenius Carryless Reflection Engine - doubly and triply infinite Binary Ito-Leibniz, scale-ladder and graded carryless-Hadamard convolution laws (`cauchy-hadamard-frobenius-reflect`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a finite-certificate carryless (F_2[x]) reflection compiler with dyadic lane-replication lifting (reflect_all_scales_and_widths), discharging the triple-infinite n-variable Binary Ito-Leibniz / quasi-shuffle law, dyadic scale-ladder identities, universal Z/2^r Z-graded carryless-Hadamard convolution splitting, Frobenius-Hadamard orthogonality, and Sierpinski carryless inverses.*

## For Mathematicians

**Mechanism:** *Cauchy–Hadamard–Frobenius Normal-Form Reflection Compiler (`CHReflect`)* — a kernel-verified, pure-data proof reflection engine for the **double algebra** $(\mathrm{BitVec}\ w, \oplus, \&, \mathrm{clmul}, \ll)$ combining pointwise Boolean-ring arithmetic (`^`, `&`) with carryless polynomial multiplication (`clmul` $\equiv \otimes$ in $\mathbb{F} _ 2[x]/(x^w)$) and logical left shifts (`<<<`). Every operation in this algebra is **strictly causal** (bit $k$ of the output depends only on input bits $0 \le j \le k$), so the entire infinite family of fixed-width silicon registers $\{\mathrm{BitVec}\ w\} _ {w \in \mathbb{N}}$ is the projective truncation system of a single infinite causal stream ring $\mathrm{Stream} := \mathbb{N} \to \mathrm{Bool} \cong \mathbb{F} _ 2[[x]]$ equipped with **two interacting products**: - the **Hadamard (bitwise AND) product** $(a \& b) _ k = a _ k \land b _ k$, and - the **Cauchy (carryless `cl

## For Non-Mathematicians

A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of a finite-certificate carryless (F_2[x]) reflection compiler with dyadic lane-replication lifting (reflect_all_scales_and_widths), discharging the triple-infinite n-variable Binary Ito-Leibniz / quasi-shuffle law, dyadic scale-ladder identities, universal Z/2^r Z-graded carryless-Hadamard convolution splitting, Frobenius-Hadamard orthogonality, and Sierpinski carryless inverses.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `CauchyHadamardFrobeniusReflect/Theorems.lean`, definitions in `CauchyHadamardFrobeniusReflect/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `reflect_all_bitvec` | Theorem 1 (finite certificate lifts to all bit-widths `w` and all `BitVec w` assignments). |
| `reflect_all_scales_and_widths` | Theorem 2 (dyadic lane-replication lifting: one finite certificate proves `dilate r e1 = dilate r e2` for all scales `r` and all widths `w`). |
| `binary_ito2_all_scales_widths` | Theorem 3 (doubly-infinite weight-1 Rota-Baxter / Binary Ito law for `bvPr r`). |
| `binary_ito_general_n` | Theorem 4 (triple-infinite `n`-variable Binary Ito-Leibniz / quasi-shuffle law for all `n ≥ 1`, `r`, `w`). |
| `self_scale_ladder_all_scales_widths` | Theorem 5 (doubly-infinite dyadic self-scale ladder identity). |
| `two_scale_ladder_all_scales_widths` | Theorem 6 (doubly-infinite two-scale dyadic ladder identity). |
| `residue_conv_split_all_r_w` | Theorem 7 (universal `Z/2^r Z`-graded carryless-Hadamard convolution splitting for all `r`, `t < 2^r`, `w`). |
| `frob_hadamard_orthogonal_all` | Theorem 8 (universal Frobenius-Hadamard residue orthogonality for all `r`, `s1 % 2^r ≠ s2 % 2^r`, `w`). |

## Prior-Art Context

- Builds on classical binary arithmetic and finite-state / algebraic verification methods; formalizes a pure-Init Lean 4 infinite proof engine with zero Mathlib dependencies.
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).