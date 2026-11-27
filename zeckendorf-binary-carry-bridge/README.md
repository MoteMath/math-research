# Zeckendorf-to-Binary Carry-Bridge Transducer Engine (`zeckendorf-binary-carry-bridge`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **87 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism:** **The $(r + 1)$-State Carry-Bridge Transducer & Difference-Basis Certificate Compiler (`CarryBridgeEngine`)** Every bitmask $x \in \mathbb{N}$ can be read simultaneously in base $2$ ($\sum b _ i 2^i$) and in any binary-weight linear-recurrence numeration system $G _ {k+r} = \sum _ {j \in S} G _ {k+j}$ specified by a finite bitmask certificate `RecCert = (r, maskS*

## For Mathematicians

**Mechanism:** **The $(r + 1)$-State Carry-Bridge Transducer & Difference-Basis Certificate Compiler (`CarryBridgeEngine`)** Every bitmask $x \in \mathbb{N}$ can be read simultaneously in base $2$ ($\sum b _ i 2^i$) and in any binary-weight linear-recurrence numeration system $G _ {k+r} = \sum _ {j \in S} G _ {k+j}$ specified by a finite bitmask certificate `RecCert = (r, maskS)` ($r \ge 2$, $0 \in S \subseteq \{0, \dots, r-1\}$). Replacing a single redex (`0` at bit $k + r$ and `1` at all bits $k + j$ for $j \in S$) with `1` at bit $k + r$ and `0` at $k + S$ adds $m _ S \cdot 2^k$ in base $2$, where $m _ S = 2^r - \mathrm{mask} _ S$. **Pure-Silicon Finite $\to$ Infinite Bridge:** 1. **Universal Two's-Complement Carry-Eigenvalue Law:** Because $0 \in S$, both $\mathrm{mask} _ S$ and $m _ S$ are odd and satisfy $\mathrm{mask} _ S + m _ S = 2^r$. Therefore the base-2 binary carry-in bitmask $K _ {\mathrm{bin}}(a, b) := (a + b) \oplus a \o

## For Non-Mathematicians

**Mechanism:** **The $(r + 1)$-State Carry-Bridge Transducer & Difference-Basis Certificate Compiler (`CarryBridgeEngine`)** Every bitmask $x \in \mathbb{N}$ can be read simultaneously in base $2$ ($\sum b _ i 2^i$) and in any binary-weight linear-recurrence numeration system $G _ {k+r} = \sum _ {j \in S} G _ {k+j}$ specified by a finite bitmask certificate `RecCert = (r, maskS

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `ZeckendorfBinaryCarryBridge/Theorems.lean`, definitions in `ZeckendorfBinaryCarryBridge/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `popcount_add_carry` | Kummer-Legendre Binary Carry-Count Identity: `popcount a + popcount b = popcount (a + b) + popcount (carryInMask a b)`. |
| `master_carry_bridge_iff` | **MASTER CARRY-BRIDGE EQUIVALENCE (Transducer ↔ Binary Carry-Eigenvalue ↔ Bit-Balance):** For any valid `RecCert c`, any `x p : Nat`, and any `r`-spaced `d : Nat`: `TransducerAccepts c x p d ↔ (p = x + c.mS * d ∧ carryInMask x (c.mS * d) = (2^(c.r+1) - 2) * d)`. |
| `not_diff_basis_refutation` | **CONVERSE / SHARPNESS DIRECTION OF THE DICHOTOMY:** If `c` is valid (`r ≥ 2`, `0 ∈ S`, `maskS < 2^r`) and NOT a difference basis (`c.isDiffBasis = false`), then there is an explicit 2-step derivation `x →_δ w1 →_0 p` at `x = maskS /// (maskS <<< δ)` with `d = 2^δ + 1` that VIOLATES both `r`-spacing AND the binary carry-eigenvalue law! |
| `rbonacci_uniqueness` | **CANONICAL `r`-BONACCI UNIQUENESS THEOREM (ALL `r ≥ 2`):** Two canonical `r`-Zeckendorf bitmasks with the same `r`-bonacci value MUST be equal! |
| `rbonacci_master_invariants` | **COMPLETE SUITE OF COROLLARIES FOR CANONICAL `r`-BONACCI NORMALIZATION (ALL `r ≥ 2`):** For EVERY `r ≥ 2` and EVERY `x : Nat`, there exists a UNIQUE canonical `(p, d)` with `noROnes r p ∧ evalRecNat (rBonacciWeight r) p = evalRecNat (rBonacciWeight r) x ∧ p = x + d`, and it satisfies ALL SEVEN pure-silicon invariants simultaneously! |
| `sparse_r6_diff_basis_infinite_law` | Infinite theorem instantiated automatically from `certDB6A_ok` (`decide`) via the Carry-Bridge Engine: for the sparse difference-basis recurrence `G_{k+6} = G_{k+5} + G_{k+3} + G_{k+1} + G_k` (`m_S = 21`), EVERY rewrite derivation `x →* p` obeys `carryInMask x (21 * d) = 126 * d`, `p ^^^ x = clmul 107 d`, `popcount x = popcount p + 3 * popcount d`, and `popcount (carryInMask x (21 * d)) = 6 * popcount d`! |
| `witness_nonvacuity_sparse_r6` | Non-vacuity witness 3: non-`r`-bonacci sparse difference basis `certDB6A` (`r=6, S={0,1,3,5}, m_S=21`) has a genuine non-trivial 2-step derivation `x = 0b101011101011 = 2795 → 4139 → p = 4160` (`d = 65 = 2^6 + 1`)! |
| `sharpness_non_confluence_still_obeys_carry_bridge` | **SHARPNESS 3 (Difference-Basis Carry-Bridge Holds Even Under Non-Confluence!):** For `certDB4A` (`r = 4, S = {0, 1, 3}, m_S = 5`, a genuine difference basis), starting from `x = 47 (0b101111)`, firing `k = 2` reaches `67` while firing `k = 0` reaches `52` (`67 ≠ 52`: non-confluent!), YET BOTH derivations satisfy `carryInMask x (5 * d) = 30 * d`! |

## Prior-Art Context

- - **Classical foundations (explicitly distinguished):** - Ostrowski (1922) and Berthé (2001): Ostrowski numeration systems associated with continued fractions and Sturmian words. - Zeckendorf (1972) and Fraenkel (1985): existence/uniqueness of canonical $r$-bonacci / linear-recurrence representations. - Frougny (1992) and Shallit (1994): automaticity and finite-state bimachine (two-pass transducer) normalization/addition in Fibonacci, Pisot, and linear-recurrence numeration systems. - Arndt (*Matters Computational*) / OEIS A003714: fibbinary bitmask test $x \mathbin{\&} 2x = 0$ and successor formula via `x / (x >> 1)`. - Kummer (1852) / Legen
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).