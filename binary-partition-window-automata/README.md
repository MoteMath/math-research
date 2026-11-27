# Binary Partition Window-Automaton Compiler & Symbolic 2-Adic Decimation Engine (`binary-partition-window-automata`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism:** **Dual-Layer Binary Partition Congruence Automaton Engine** (`WindowAutomatonCert` + Symbolic 2-Adic Decimation Lifting). For any finite duplicate-free digit set $D \subseteq \mathbb{N}$ containing $0$ with $L = \max(D) \ge 1$, the $D$-restricted binary partition function $B _ D(n)$ counts representations $n = \sum _ {i \ge 0} d _ i 2^i$ with $d _ i \in D$. Rathe*

## For Mathematicians

**Mechanism:** **Dual-Layer Binary Partition Congruence Automaton Engine** (`WindowAutomatonCert` + Symbolic 2-Adic Decimation Lifting). For any finite duplicate-free digit set $D \subseteq \mathbb{N}$ containing $0$ with $L = \max(D) \ge 1$, the $D$-restricted binary partition function $B _ D(n)$ counts representations $n = \sum _ {i \ge 0} d _ i 2^i$ with $d _ i \in D$. Rather than working over formal power series, it is defined directly in pure silicon via the bit-shift recurrence: The **$r$-restricted binary partition function** is the contiguous specialization $b _ r(n) := B _ {\{0, 1, \dots, r\}}(n)$.

## For Non-Mathematicians

**Mechanism:** **Dual-Layer Binary Partition Congruence Automaton Engine** (`WindowAutomatonCert` + Symbolic 2-Adic Decimation Lifting). For any finite duplicate-free digit set $D \subseteq \mathbb{N}$ containing $0$ with $L = \max(D) \ge 1$, the $D$-restricted binary partition function $B _ D(n)$ counts representations $n = \sum _ {i \ge 0} d _ i 2^i$ with $d _ i \in D$. Rathe

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BinaryPartitionWindowAutomata/Theorems.lean`, definitions in `BinaryPartitionWindowAutomata/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `soundness` | **Master Automaton Lifting Soundness Theorem (Finite Certificate → ∀ n : Nat).** |
| `b5_forbids_three_mod4_via_dfa` | For every `n`, the 5-restricted binary partition number `b_5(n)` (`br 5 n`) is never congruent to `3` modulo `4`. |
| `b4_coupled_8n_5_mod4` | For every `n`, `b_4(8n + 5) = 3 * b_4(8n) (mod 4)`. |
| `mutation_rejects_bad_q0` | Hostile mutation tests: corrupting `q0`, `d1`, or `D` makes `isValid = false` (non-vacuous checker). |
| `br_universal_mod4_carry_law` | **Theorem B (Universal Carry-Valuation Law for All Odd `r = 2^t * u - 1`):** For every `t ≥ 1`, every odd `u`, and every `j : Nat`, `b_{2^t * u - 1}(2 * u * j) mod 4 = Φ_t(j mod 2^t)` — strictly periodic of period `2^t`, independent of the odd factor `u`, and governed by the parity of `v_2(j mod 2^t)`. |
| `sharpness_r3_even_v2` | Machine-checked finite instance: `b_3(4) mod 4 = 3` (the boundary case `r = 3`, where `v_2(r+1)` is even, does hit `3 mod 4`). |
| `sharpness_b5_fails_mod8` | Machine-checked finite instance: `b_5(6) = 5`, so `b_5(6) mod 8 != 1` although `b_5(6) = 1 (mod 4)`. |
| `sharpness_gap023_offset17_fails` | Machine-checked finite instance: for the digit set `{0, 2, 3}`, `B(17) mod 4 != 3 * B(0) mod 4`, i.e. the offset-17 analogue of the coupled law fails. |

## Prior-Art Context

- - **Classical literature:** - Churchhouse (1969) and Rødseth (1970) proved congruences modulo $2^k$ for *unrestricted* binary partitions $b(n)$ (including $b(2n)/2 \bmod 2$ governed by $v _ 2(n)$); Rødseth–Sellers (2005) further studied $m$-ary and restricted binary partition congruences modulo powers of $m$ (including $2$). - Reznick (1990, *"Some binary partition functions"*) studied hyperbinary ($b _ 2$, Stern's diatomic) and $r$-restricted binary partitions $b _ r(n)$, establishing mod-$2$ periodicity (Theorem A here is re-proved purely elementarily via our `sumShift` telescoping lemma as an input to Theorems B and C).
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).