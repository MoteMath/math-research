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
| `sound_coset_order` | Layer 2B soundness (universal order bound): if the coset certificate checks and `repeatWord d word` returns to coset 0, then W^d = id for every bit-width w ≥ w0. Only W^d = id is stated in `Challenge.lean`; the power-reduction W^n = W^(n % d) is not stated there. |
| `thm_d6_C_power_mod` | Theorem I.5 (Universal D6 Power-Mod-6 Reduction ∀ n : Nat, ∀ w ≥ 1): C^n = C^(n % 6). |
| `thm_b3_AST_power_mod` | Theorem II.3 (Universal Modulo-6 Power Reduction ∀ n : Nat, ∀ w ≥ 3): (bCnot(0,1) · bSwap(0,1) · bToff(0,1,2))^n = (bCnot(0,1) · bSwap(0,1) · bToff(0,1,2))^(n % 6). |
| `thm_ptoff_dihedral_family` | Theorem III.2 (Infinite Family of Hybrid Toffoli-Add Involutions ∀ n : Nat, ∀ w : Nat): (P_toff(0,1,3;2)^n · rNot(3))^2 = Id for ALL exponents n and ALL bit-widths w! |
| `thm_t3_sharp_collapse_w2` | Sharpness III.c (width threshold of T3), collapse half only: T3 = Id at width w = 2. The T3 ≠ Id for w ≥ 3 half is `thm_t3_nontrivial_ge3` in `Theorems.lean`, not in `Challenge.lean`. |
| `mut_window_out_of_bounds` | Machine-checked finite instance (a single `decide` fact): `checkWindowEq 1 2 [gT] [gT] = false`, a mutation check that the window check rejects an out-of-bounds window. |
| `mut_order_lower_inflated` | Machine-checked finite instance (a single `decide` fact): `checkOrderLowerAt 2 2 12 circC = false`, a mutation check that an inflated order lower bound is rejected. |

## Prior-Art Context

- - **Distinction from CHARTER Section 4:** Completely disjoint from `binary-lyness-periods`, `bitrev-increment-cycles`, `clmul-lift-determinants`, `skew-thue-morse-pfaffian`, `zero-carry-spanning-trees`, `carry-determinants`, `arx-fibonacci-isospectrality`, `weak-bruhat-commutators`, and ML quantization packages. - **Distinction from Classical Literature:** - Classical reversible-circuit synthesis (Shende–Prasad–Markov–Hayes 2003; Iwama–Kambayashi–Yamashita 2002; Saeedi–Markov 2013) studies fixed-width NCT/CNOT/Toffoli circuit rewriting over a fixed finite wire count $w$, without kernel-verified width-polymorphic coset compilers or modular-add
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Scope of the formal statement

The circuits are the hand-written gate lists in `Defs.lean` over `State r w` (r registers of w-bit words) with the evaluator `evalCircuit`; the universal statements are about that model. The two `mut_*` rows are single finite instances, and `sound_coset_order` states only W^d = id.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).