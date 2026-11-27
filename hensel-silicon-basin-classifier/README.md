# 2-Adic Hensel-Contraction Fixed-Point and Basin Classifier (`hensel-silicon-basin-classifier`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): 3-valued bit-derivative abstract-interpretation compiler unifying carried `*`, carry-less `clmul`, and bitwise operations, together with a contraction-free universal fixed-point depth law ($\le w$), cycle-localized 2-adic Hensel basin lifting, non-power-of-two basins $3 \cdot 2 ^ {w - 3}$, a 7-fixed-point bitwise-quadratic map, and exact $2 w - 2$ cycle transient depth, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

We introduce an algebraic DSL `BPoly` mixing $+$, $-$, carried multiplication $*$, carry-less polynomial multiplication `clmul`, and non-$\mathbb{Z} _ 2$-differentiable bitwise operators (`&`, `|`, `^`, `~`), together with a **3-valued abstract bit-derivative** (`BPoly.absDeriv_sound`) and static bit-support analyzer (`vanishesAbove` / `allOnesAbove`). Under a single bit-0 Leibniz rule, this statically certifies 2-adic local contraction across all widths $w \ge m$ without any floating-point or real-analytic approximations.

On the dynamical side, we prove three sharp infinite laws: (1) the **contraction-free universal fixed-point depth theorem** (`tfunc_fixedPoint_depth_le_width`), showing that for *every* T-function $F$, any $w$-bit state that ever reaches a fixed point reaches it in at most $w$ steps (sharp at `x ^ (x + 1)`); (2) **cycle-localized Hensel lifting** (`henselLift_periodic`, `henselLift_basin_convergence`, `fixedPointCount_lift`), lifting periodic orbits, counts, and attracting basins from base width $m$ to all $w \ge m$; and (3) concrete bitwise-quadratic phenomena including an asymmetric non-power-of-two basin of size $3 \cdot 2 ^ {w - 3}$ (`mapAsym_basin_4_nonPowerOfTwo`), a 7-fixed-point map (`mapSeven_fixedPointCount`), a carried+`clmul` hybrid 2-cycle (`mapClmulHybrid_unique_twoCycle`), and **exact $2 w - 2$ cycle transient depth** (`mapHalfCycle_depth_exact_sharp`), strictly separating cycle depth from fixed-point depth $w$.

## For Non-Mathematicians

If you feed a $w$-bit number repeatedly into a circuit made of additions, multiplications, XORs, and ANDs, how long can it take to settle down, and how many numbers fall into each attractor? We prove a universal speed limit: if a number is going to settle on a single fixed value under *any* such bit-sliced circuit, it must get there in at most $w$ steps. Using a finite base-width certificate, our Hensel lifter automatically predicts the exact number of fixed points and exact basin sizes (even non-powers of 2 like $3 \cdot 2 ^ {w - 3}$) for every bit-width $w$ at once, and exhibits a 2-cycle whose settling time is exactly $2 w - 2$ steps.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `HenselSiliconBasinClassifier/Theorems.lean`, definitions in `HenselSiliconBasinClassifier/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `bPoly_absDeriv_sound` | The 3-valued static bit-derivative of any `BPoly` (mixing $+, *, \mathrm{clmul}, \&, |, \oplus, \sim$) soundly tracks bit-$k$ sensitivity across every width $w > k \ge m$. |
| `tfunc_fixedPoint_depth_le_width` | For *any* T-function $F$ on $\mathrm{BitVec}\; w$, every state that reaches a fixed point reaches it in at most $w$ steps (no contraction hypothesis required). |
| `henselLift_periodic` | Any locally contracting $L$-cycle at base width $m$ lifts via `henselLift` to an exact $L$-cycle at every width $w \ge m$. |
| `henselLift_basin_convergence` | Every $w$-bit state whose $m$-bit truncation reaches a contracting $L$-cycle converges to the lifted $L$-cycle in explicit Hensel rounds. |
| `fixedPointCount_lift` | When every base fixed point at width $m$ is locally contracting, the total number of fixed points is constant across all widths $w \ge m$. |
| `mapAsym_basin_4_nonPowerOfTwo` | The bitwise-quadratic map `mapAsym` has an attracting basin of exact non-power-of-two cardinality $3 \cdot 2 ^ {w - 3}$ at every width $w \ge 3$. |
| `mapSeven_fixedPointCount` | The bitwise-quadratic map `mapSeven` has exactly $7$ fixed points at every width $w \ge 3$. |
| `mapHalfCycle_depth_exact_sharp` | `mapHalfCycle` achieves exact transient depth $2 w - 2$ into its 2-cycle at every width $w \ge 2$, strictly exceeding the universal fixed-point depth bound $w$. |

## Proof Architecture

1. **3-valued bit-derivative abstract interpreter (`BPoly.support_sound`, `BPoly.absDeriv_sound`):** unifies carried `*`, carry-less `clmul`, and bitwise operators under one bit-0 Leibniz rule.
2. **Contraction-free fixed-point depth (`tfunc_fixedPoint_depth_le_width`):** proves by width induction that any trajectory reaching a fixed point locks at least one new bit per step.
3. **Cycle-localized Hensel lifter (`henselLift_periodic`, `henselLift_unique`, `henselLift_basin_convergence`, `fixedPointCount_lift`):** lifts base-width periodic orbits and basins to all $w \ge m$ with exact round bounds.
4. **Sharpness & concrete families (`mapAsym`, `mapSeven`, `mapClmulHybrid`, `mapHalfCycle`, `counterexample_*`):** demonstrates non-power-of-two basins, 7 fixed points, carried+`clmul` 2-cycles, exact $2 w - 2$ depth separation, and kernel-checked counterexamples when hypotheses are dropped.

## Prior-Art Context

- **Classical $p$-adic dynamics & Hensel lifting lineage:** discrete $2 ^ {w - m}$ clopen-ball attracting-basin lifting sits in the $p$-adic Banach-Hensel dynamical systems lineage of **Silverman** (*The Arithmetic of Dynamical Systems*, Springer 2007), **Anashin & Khrennikov** (*Applied Algebraic Dynamics*, De Gruyter 2009), and **Benedetto** (*Dynamics in One Non-Archimedean Variable*, AMS 2019).
- **Contents (not independently reviewed; no prior-art search is recorded):** the 3-valued bit-derivative abstract-interpretation compiler for bitwise operations, carried `*` and carry-less `clmul`, the contraction-free universal fixed-point depth law ($\le w$), the bitwise-quadratic 7-fixed-point and $3 \cdot 2 ^ {w - 3}$ basin statements, and the cycle-localized $2 w - 2$ transient depth separation.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
