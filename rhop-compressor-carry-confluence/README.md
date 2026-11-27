# r-Hop Compressor Capacity & Carry-Save Confluence (`rhop-compressor-carry-confluence`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): exact capacity dichotomies for carry-free compressor cells at every hop depth $r$, a 64-cell classification of 1-hop carry-free 4:2 compressors (surjectivity of the mask map in the Challenge), depth-invariant per-column carry laws for arbitrary mixed compressor networks, and a minimal $(2h - 1)$-state carry-defect transducer that certifies confluence of carry-save trees, all formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

A `CarryFreeCell p v M` is a finite truth-table certificate for a $p$-input binary compressor whose horizontal carry-out depends only on the current column and takes values in $\{0, \dots, M\}$, with at most $v$ vertical carries. A `RHopCompressor p v r` is the generalization where the horizontal carry-out is a function of a sliding window of $r$ columns. We prove sharp, unbounded dichotomies for all parameters:

1. **1-hop dichotomy:** for $p \ge 1$, $\mathrm{Nonempty}(\mathrm{CarryFreeCell}\; p\; v\; M) \iff M \le 2v \land p \le M + 2v + 1$. In particular $p \le 4v + 1$, and no 1-hop carry-free 6:2 compressor exists for any $M$.
2. **$r$-hop dichotomy:** $\mathrm{Nonempty}(\mathrm{RHopCompressor}\; p\; v\; r) \iff p \le 2 v \cdot 2^r + 1$ for all $r \ge 0$. 6:2 first unlocks at $r = 2$, and 3-hop 17:2 exists while 18:2 is impossible.
3. **4:2 classification:** every valid 1-hop carry-free 4:2 horizontal-carry function is `h42OfMask m` for one of the 64 binary masks on the six weight-2 input patterns (`cell42_bijection_right`, the surjectivity half; this is all that `Challenge.lean` states). That each mask gives a valid function and that distinct masks give distinct functions (`h42OfMask_valid`, `cell42_bijection_left`) are in `Defs.lean`, so the masks biject in the library, but those two are not in the Challenge.
4. **Network laws:** for any compressor network `NetW w d X Y K` built from arbitrary routing permutations, parallel layers and mixtures of 1-hop and $r$-hop cells, with cumulative carry ledger $K$, the exact identity $\mathrm{popListW}(Y, w) + \sum _ {k < w - 1} K(k) + 2 K(w - 1) = \mathrm{popListW}(X, w)$ holds for all widths, arities and depths.
5. **Confluence:** two arbitrary networks reaching column heights at most $h$ are accepted by a deterministic $(2h - 1)$-state transducer over $\{-(h-1), \dots, h-1\}$ whose state at column $j$ is the exact carry-ledger difference; for CSA trees ($h = 2$) there are exactly 3 states $\{-1, 0, +1\}$, and every state is hit for every $h$ (`transducer_state_minimality`).

Plus (in `Theorems.lean`, not all in the Palomar challenge): schedule-invariance of the whole carry spectrum at height 1, overflow-immune carry parity, and lexicographic Lyapunov descent for every active $p:2$ step.

## For Non-Mathematicians

Fast multipliers add many numbers at once by feeding bits into small circuits called *compressors* (such as the 3:2 full adder or the 4:2 compressor) that squeeze several bits into two. A natural question is how many input bits a compressor can swallow if its internal carry wiring may only look back a fixed number of columns. We prove exact answers for every possible circuit size, not just those anyone has built: one-column-lookback cells top out at $4v + 1$ inputs, and each additional column of lookback doubles the capacity. We also pin down all 64 possible 4:2 compressors, and show that no matter how an adder tree is wired, the bit totals obey the same exact bookkeeping law, and any two ways of wiring the same tree differ by a tiny three-valued carry difference at each column. Everything is checked by Lean's kernel for all bit-widths at once, with no sampling.

## Prior Art & Credit

- **Compressor trees:** Wallace (1964), Dadda (1965), Weinberger (1981) and Santoro–Horowitz (1989) introduced 3:2 and 4:2 compressor trees; higher-order hardware compressors use multi-hop horizontal carries.
- **Redundant-digit zero automata:** the $\mathcal{A} _ h$ transducer is the redundant-base zero automaton of Frougny (1992) and Chow–Robertson (1978), re-targeted here to track exact carry-ledger differences across arbitrary mixed $r$-hop networks.
- **What we believe is new (not independently reviewed):** the universal $r$-hop dichotomy $p \le 2 v \cdot 2^r + 1$ and the 1-hop $(M, p)$ dichotomy with the 64-cell classification, the finite-table-to-infinite-DAG lifting engine with schedule-invariance of the entire carry spectrum, and the formal kernel-checked statements. No prior record of these exact capacity theorems was found by the authors; the search was not recorded.

## Scope of the formal statement

The compressor cells, networks and the carry-ledger transducer are the definitions in `Defs.lean` (finite truth-table certificates and arbitrary routing networks), not a hardware netlist or a library cell. Within that model the capacity dichotomies, the popcount carry-ledger law and the confluence statements are universal in the parameters; the 4:2 classification row in `Challenge.lean` is the surjectivity half only.

## Contents

| Theorem | Module |
| :--- | :--- |
| `carry_free_capacity_dichotomy`, `no_carry_free_6_2`, `cell42_bijection_right`, `rhop_capacity_dichotomy`, `no_3hop_18_2`, `netW_popcount_carry_conservation`, `confluence_csa_3state`, `transducer_state_minimality` | `RhopCompressorCarryConfluence.Defs` and `RhopCompressorCarryConfluence.Theorems` |

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
python scripts/explore_and_verify.py
```

See [`AUDIT.md`](AUDIT.md) for the verbatim `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. Fixed-width or finite computations in `scripts/explore_and_verify.py` are illustrative only; the infinite claims are exactly the Lean theorems.
