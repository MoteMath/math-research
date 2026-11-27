# Carry-Lookahead Prefix Monoid with the Threshold-Step Semigroup (`carry-prefix-threshold-monoid`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **8 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a sharp width threshold $M \ge U - L$ at which every multi-input, signed-borrow, mixed-radix or modular carry map collapses faithfully into a finite aperiodic semigroup of exactly $N ^ 2 - N + 1$ elements, valid for every parallel-prefix tree shape and every word width, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Multi-operand, signed-borrow, mixed-radix and modulo-$m$ carry transitions are Euclidean floor-division maps $c \mapsto \lfloor (c + S) / M \rfloor$. Their composition lives in the unbounded semidirect product $(\mathbb{N} _ {> 0}, \times) \ltimes (\mathbb{Z}, +)$, whose shift $S$ grows linearly with the word width. We prove that on every carry window $[L, U]$ and every block with $M \ge U - L$ the map **collapses faithfully** into the finite semigroup $\mathcal{T} _ {[L, U]}$ of threshold steps $c \mapsto q + [c \ge t]$ and constants, and that `collapse` is an exact semigroup homomorphism on window-preserving blocks. The semigroup is aperiodic ($e ^ 3 = e ^ 2$) and has exactly $N ^ 2 - N + 1$ elements for $N = U - L + 1$ carry states ($N = 2$ recovers the classical generate/propagate monoid with $3$ elements, $N = 3$ gives $7$).

Everything lifts to **all** prefix-tree topologies (ripple, Sklansky, Kogge-Stone, Brent-Kung, arbitrary unbalanced trees) and all widths through one generic associative `PrefixTree` chassis: two trees with the same fringe evaluate equally in any semigroup. Below the critical modulus the collapse is provably impossible. Global carry absorption reduces to a local adjacent condition (a two-state subshift of finite type): a tree absorbs the carry iff its fringe is not a resonant chain, giving exact counts for three-operand sums ($2 \cdot 4 ^ w$ resonant weighted triples out of $8 ^ w$), and modulo an odd $m > 1$ no binary block ever absorbs.

## For Non-Mathematicians

A multi-input adder has to pass a "carry" from digit to digit, and with many inputs the carry can be larger than a single bit. Engineers combine blocks of digits in a tree to go fast, and one would expect the bookkeeping to blow up with the width. It does not: past an explicit, sharp block size, each block's effect on the carry is one of only $N ^ 2 - N + 1$ tiny behaviours, forever. For three-input sums the "bad" digit strings that let a carry sneak through the whole word can be counted exactly, at every length.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `CarryPrefixThresholdMonoid/Theorems.lean`, definitions in `CarryPrefixThresholdMonoid/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `collapse_tree_universality` | For every prefix tree whose leaf blocks have modulus at least $U - L$ and preserve the window $[L, U]$, evaluating the tree in the finite threshold-step semigroup and applying it to any carry $c \in [L, U]$ equals the exact floor-division carry action. |
| `collapse_sharpness_obstruction` | If $0 < M < U - L$ there is a block of modulus $M$ whose action on $[L, U]$ is represented by no threshold-step element, so the width threshold is sharp. |
| `aperiodic` | Every threshold-step element satisfies $e ^ 3 = e ^ 2$ (the semigroup is aperiodic of index at most $2$). |
| `enumBounded_length` | The bounded threshold-step semigroup on $N \ge 1$ carry states has exactly $N ^ 2 - N + 1$ elements. |
| `tree_exact_carry_absorption` | A prefix tree of threshold-step elements evaluates to a constant (absorbs every incoming carry) if and only if its fringe is not a resonant chain. |
| `three_input_exact_absorption` | For every prefix tree of three-operand digit sums $s \le 3$, absorption holds iff the digit string is not bit-resonant, for both the unsigned and the signed-borrow encodings. |
| `three_input_resonant_triple_count` | For every width $w \ge 1$ the resonant digit strings carry total weight $2 \cdot 4 ^ w$ (out of $8 ^ w$ operand triples). |
| `odd_modulus_never_absorbs` | For every odd $m > 1$, every width $w$ and residue $r < m$, the base-$2$ block of width $w$ is not carry-absorbing modulo $m$. |

## Proof Architecture

1. **Generic prefix chassis (`PrefixTree`):** `associative_tree_universality` and `action_universality` show that any associative encoding evaluates identically on all trees with the same fringe, so correctness for one topology is correctness for all.
2. **Collapse homomorphism (`collapse_homomorphism`, `collapse_tree_universality`):** floor-division blocks with $M \ge U - L$ that preserve $[L, U]$ map to threshold steps; the map respects composition, so whole trees collapse.
3. **Sharpness and finiteness (`collapse_sharpness_obstruction`, `aperiodic`, `enumBounded_length`):** a universal obstruction for $M < U - L$, aperiodicity, and the exact cardinality via injectivity of the semantics on the bounded part.
4. **Resonance lock (`tree_exact_carry_absorption`, `three_input_exact_absorption`, `three_input_resonant_triple_count`):** non-absorption reduces to the adjacent condition $q _ i + 1 = t _ {i + 1}$; the three-operand case is counted by a two-state transfer recurrence.
5. **Modular feedback (`AffMod`, `crandall_feedback_dichotomy`, `fermat_feedback_dichotomy`):** end-around Crandall/Mersenne feedback has a dual fixed-point band while Fermat feedback has an exact period-$2$ limit cycle; `odd_modulus_never_absorbs` is the contrasting non-absorption law.

## Prior-Art Context

- **Classical carry-lookahead and parallel prefix:** the two-input generate/propagate monoid and its flip-flop semigroup $U _ 2$ (Brent-Kung 1982, Ladner-Fischer 1980, Kogge-Stone 1973) and modulo $2 ^ n \pm 1$ adders (Zimmermann 1999) are credited as the $N = 2$ background. As the referee notes recommend, the $U _ 2$ flip-flop monoid and the CFL83 reference are credited as the closest classical antecedents.
- **Crandall primes:** the feedback dichotomies concern end-around carry for moduli of the form $2 ^ n \pm \delta$ in the sense of Crandall's special-form moduli.
- **Referee audit (referee-1, referee-6, referee-10; recorded in `REGISTRY.md` and `TOP_MECHANISMS.md`):** the generalization of the $U _ 2$ / CFL83-style monoid to unbounded multi-input carries with an exact collapse-width threshold, resonance-lock subshift counts and Crandall/Fermat dichotomies is new; zero overlap with the other packages of this repository.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
