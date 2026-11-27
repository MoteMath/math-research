# Two-Way Bit-Transducer Tile-Witness Inversion and Coxeter-6 Phase Transition (`two-way-bit-transducer-inverses`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): pure-data finite tile-witness crossing-sequence certificate engine (`FiniteTileCert`) certifying exact all-width two-way bit-transducer inversion and periodicity on `BitVec w`, proving period-3 vs. exponential-$2 ^ w$ bidirectional collapse, a parametric Coxeter-6 phase transition for all run-length thresholds $m \ge 2$, and coupled parity-delay inversion, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

We introduce a pure-data **Finite Tile-Witness Crossing-Sequence Certificate** (`FiniteTileCert Q`, `checkCert_sound_bv`) for compositions of forward (LSB-to-MSB) and backward (MSB-to-LSB) bit-transducers. A finite local compatibility check on single-bit tiles lifts via inductive crossing-sequence witnesses to exact identity laws `sweepsBV cert.sws x = x` on `BitVec w` for **every** width $w \in \mathbb{N}$.

Instantiating the engine yields striking bidirectional periodicity laws: (1) `skipFlip2TwoWay` has **universal period 3** on `BitVec w` for all $w$ (`skipFlip2_period3_bv`), while its unidirectional forward sweep has **exponential period $2 ^ w$** (`skipFlip2_fwd_period_pow2`); (2) shifting by one state yields universal period 6 (`skipFlip2_shifted_period6_bv`); (3) for every run-length threshold $m \ge 2$, both `runTriggerTwoWay m` and `runSkipFlip m` undergo a **Coxeter-6 phase transition** with exact period 6 across all widths (`runTrigger_period6_all_m_bv`, `runSkipFlip_period6_all_m_bv`) and explicit two-way left inverses (`runTriggerTwoWay_left_inv`); and (4) coupled parity-delay forward sweeps are exactly inverted by Gray-difference backward sweeps (`coupled_parityDelay_exact_inv`).

## For Non-Mathematicians

Run a simple bit-flipping rule from right to left across a $w$-bit word, and it can take $2 ^ w$ repetitions to return to the start. Now follow every right-to-left pass with a left-to-right pass: suddenly, for every word length from 1 bit to a million bits, the entire transformation snaps back to the start in just 3 or 6 passes! Our finite tile-witness verifier proves these all-width inversion and periodicity miracles automatically from a tiny local check.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `TwoWayBitTransducerInverses/Theorems.lean`, definitions in `TwoWayBitTransducerInverses/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `checkCert_sound_bv` | Any finite tile-witness certificate `cert` passing `checkCert cert = true` proves `sweepsBV cert.sws x = x` on `BitVec w` for every width $w$. |
| `skipFlip2_period3_bv` | The bidirectional skip-flip transducer `skipFlip2TwoWay` satisfies $T ^ 3(x) = x$ on `BitVec w` for every width $w$. |
| `skipFlip2_shifted_period6_bv` | The shifted bidirectional skip-flip transducer satisfies $T ^ 6(x) = x$ on `BitVec w` for every width $w$. |
| `skipFlip2_fwd_period_pow2` | The unidirectional forward sweep of `skipFlip2` has period $2 ^ w$ on `BitVec w`, contrasting the bidirectional period 3. |
| `runTriggerTwoWay_left_inv` | For every threshold $m$ and width $w$, `runTriggerTwoWay m` admits an explicit two-way left inverse. |
| `runTrigger_period6_all_m_bv` | For every threshold $m \ge 2$ and every width $w$, `runTriggerTwoWay m` has exact universal period 6 on `BitVec w`. |
| `runSkipFlip_period6_all_m_bv` | For every $m \ge 2$ and every width $w$, the symmetric two-way `runSkipFlip m` transducer has universal period 6 on `BitVec w`. |
| `coupled_parityDelay_exact_inv` | The coupled parity-delay forward sweep is inverted on every bit list by the Gray-difference backward sweep. |

## Proof Architecture

1. **Tile-witness crossing-sequence engine (`tileWitness_sound`, `checkCert_sound_bv`):** verifies local single-bit tile transitions and lifts them inductively to all bit-widths $w$.
2. **Period-3 vs. $2 ^ w$ separation (`skipFlip2_period3_bv`, `skipFlip2_fwd_period_pow2`, `skipFlip2_shifted_period6_bv`):** proves exponential-to-constant period collapse under bidirectional composition.
3. **Parametric Coxeter-6 family (`runTriggerTwoWay_left_inv`, `runTrigger_period6_all_m_bv`, `runSkipFlip_period6_all_m_bv`):** proves universal period 6 and explicit inverses for all thresholds $m \ge 2$ and all widths $w$.
4. **Coupled inversion & sharpness (`coupled_parityDelay_exact_inv`, `badCert*_rejected`, `sharpness_*`):** proves Gray-difference inversion alongside kernel-checked hostile certificate rejections and perturbation counterexamples.

## Prior-Art Context

- **Classical two-way automata & crossing sequences:** Shepherdson (1959) and Rabin & Scott (1959) introduced crossing-sequence arguments for two-way finite automata; dihedral / Coxeter-group involutions and Gray-code differentiation are classical.
- **Referee audit (referee-1 PASS #175; recorded in `REGISTRY.md`):** the pure-data `FiniteTileCert` crossing-sequence compiler for `BitVec w`, the bidirectional period-3 vs. forward-$2 ^ w$ collapse, the parametric $m \ge 2$ Coxeter-6 phase transition, and coupled parity-delay inversion are new; zero Section 4 overlap.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
