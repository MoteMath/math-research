# Verified Reversible-Circuit Commutation, Carry-Bisimulation & Coset-Table Compiler (`RevCert`) (`reversible-circuit-coset-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Name:** `RevCert` — **Three-Layer Causal Truncation, Carry-Slice Bisimulation & Coset-Table Reversible-Circuit Compiler***

## For Mathematicians

**Name:** `RevCert` — **Three-Layer Causal Truncation, Carry-Slice Bisimulation & Coset-Table Reversible-Circuit Compiler**

## For Non-Mathematicians

**Name:** `RevCert` — **Three-Layer Causal Truncation, Carry-Slice Bisimulation & Coset-Table Reversible-Circuit Compiler**

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `ReversibleCircuitCosetCompiler/Theorems.lean`, definitions in `ReversibleCircuitCosetCompiler/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `sound_checkWindowEq` | Layer 1A Soundness Meta-Theorem: lifts finite width-w0 equivalence to ALL w ≥ w0! |
| `sound_coset_order` | Layer 2B Meta-Theorem 3 (Universal Order & Modulo-d Power Reduction ∀ n : Nat, ∀ w ≥ w0!): If `repeatWord d word` returns to coset 0, then W^d = id AND W^n = W^(n % d) for EVERY exponent n : Nat and EVERY bit-width w ≥ w0! |
| `thm_d6_C_power_mod` | Theorem I.5 (Universal D6 Power-Mod-6 Reduction ∀ n : Nat, ∀ w ≥ 1): C^n = C^(n % 6). |
| `thm_b3_AST_power_mod` | Theorem II.3 (Universal Modulo-6 Power Reduction ∀ n : Nat, ∀ w ≥ 3): (bCnot(0,1) · bSwap(0,1) · bToff(0,1,2))^n = (bCnot(0,1) · bSwap(0,1) · bToff(0,1,2))^(n % 6). |
| `thm_ptoff_dihedral_family` | Theorem III.2 (Infinite Family of Hybrid Toffoli-Add Involutions ∀ n : Nat, ∀ w : Nat): (P_toff(0,1,3;2)^n · rNot(3))^2 = Id for ALL exponents n and ALL bit-widths w! |
| `thm_t3_sharp_collapse_w2` | Sharpness III.c (Width Threshold of T3): T3 = Id for w ≤ 2, while T3 ≠ Id for ALL w ≥ 3! |
| `mut_window_out_of_bounds` | Machine-checked infinite theorem `mut_window_out_of_bounds` proved in pure Lean 4 `Init`. |
| `mut_order_lower_inflated` | Machine-checked infinite theorem `mut_order_lower_inflated` proved in pure Lean 4 `Init`. |

## Prior-Art Context

- - **Distinction from CHARTER Section 4:** Completely disjoint from `binary-lyness-periods`, `bitrev-increment-cycles`, `clmul-lift-determinants`, `skew-thue-morse-pfaffian`, `zero-carry-spanning-trees`, `carry-determinants`, `arx-fibonacci-isospectrality`, `weak-bruhat-commutators`, and ML quantization packages. - **Distinction from Classical Literature:** - Classical reversible-circuit synthesis (Shende–Prasad–Markov–Hayes 2003; Iwama–Kambayashi–Yamashita 2002; Saeedi–Markov 2013) studies fixed-width NCT/CNOT/Toffoli circuit rewriting over a fixed finite wire count $w$, without kernel-verified width-polymorphic coset compilers or modular-add
- Hostile-verified PASS by `referee-5`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).