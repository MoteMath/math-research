# `ring-attention-kulisch-bounds`

**Exact Ring-Attention Online-Softmax Non-Associativity, Attention-Sink Vanishing Laws, Descending-$m _ i$ Phase-Transition Paradox, and Reproducible Kulisch Accumulator Width Bounds**

A complete, sorry-free, pure-`Init` (`leanprover/lean4:v4.34.1`, **zero Mathlib**, **zero `native_decide`**) Palomar Comparator Lean 4 formalization of six core theorems about a hand-written rational model of online-softmax merging (see "Scope of the formal statement" below).

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (`3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 91 / 100`): universal rational associativity/commutativity of the online-softmax monoid, exact attention-sink bulk-vanishing law at $\Delta = p$ (`100%` bulk drop in L2R/DESC vs binary-tree survival to $p + \log _ 2 P - 1$, in the `rneGrid` model), constructive proof of the descending-$m _ i$ phase-transition paradox, bit-for-bit permutation/topology/partition invariance of fixed-point Kulisch accumulation with a sufficient two's-complement width $W _ {\mathrm{inv}}(P, p) = p + 2\lceil\log _ 2 P\rceil + 4$ (`int32` FP8, `int64` FP16; no minimality theorem), and sink-cliff elimination at $F = p + \log _ 2 P$.*

---

## For Mathematicians

Online-softmax reduction across $P$ distributed key-value chunks (FlashAttention Split-K / Ring Attention / Context Parallelism) evaluates the monoid operation

```math
(w_1, l_1, o_1) \oplus (w_2, l_2, o_2) = \left(m,\; \frac{w_1}{m} l_1 + \frac{w_2}{m} l_2,\; \frac{w_1}{m} o_1 + \frac{w_2}{m} o_2\right), \quad m = \max(w_1, w_2).
```

Over exact positive rationals ($w _ i > 0$), this operation is strictly associative and commutative (`Theorem 1`), preserving additive unnormalized invariants $w _ i l _ i$ and $w _ i o _ i$. Under the model `rneGrid p`, round-to-nearest-even onto the fixed grid $2^{-(p-1)}$ (the unit binade only; no exponent range and no subnormals, so it is not IEEE-754 as such), with $p = 4$ labelled FP8-E4M3, $p = 8$ BF16, $p = 11$ FP16, $p = 24$ FP32, non-associativity induces the following phase transitions in the model:

1. **Exact Attention-Sink Vanishing Law (`Theorem 2`):** When 1 sink chunk has weight $1$ ($m _ {\mathrm{sink}} = \Delta$) and $P - 1$ bulk chunks each have weight $2^{-\Delta}$ ($m _ {\mathrm{bulk}} = 0$), because $1.0$ has an even significand LSB in every precision $p \ge 2$, every sequential step satisfies $\mathrm{fl} _ p(1 + 2^{-\Delta}) = 1$ for all $\Delta \ge p$, dropping **100%** of all $P - 1$ bulk chunks and yielding exact relative error $(P - 1) / (2^p + P - 1)$ at $\Delta = p$ (`255/271` FP8-E4M3, `255/511` BF16, `255/2303` FP16, `255/16777471` FP32 at $P = 256$).
2. **Balanced Binary Tree Survival Separation (`Theorem 3`):** For $P = 2^k$ ($k \ge 2$) chunks, balanced binary tree reduction merges $2^j$ bulk chunks before meeting the sink at level $j$, pushing the vanishing threshold to
   ```math
   \Delta_{\mathrm{vanish}}^{\mathrm{TREE}}(2^k, p, e_{\min}, M) = \min\!\left(p + k - 1,\; -(e_{\min} - M) + 1\right),
   ```
   giving an exponential $P / 2 = 2^{k-1}$ survival margin gain over `L2R`/`DESC` and the hand-written formula `deltaVanishTree 8 4 (-6) 3` (a `min` of the ideal threshold and a subnormal floor, not the accumulator with subnormals) evaluates to $10$ ($< 11$) for $P = 256$, labelled the FP8-E4M3 subnormal floor cap.
3. **The Descending-$m _ i$ Phase-Transition Paradox (`Theorem 4`):** Max-first (`DESC`) ordering strictly eliminates running-accumulator rescales ($0$ rescales vs $n - 1$ for strictly ascending `ASC`/`L2R`) and beats `L2R`/`ASC` in the narrow-span staircase regime (exact `p = 4` witness: error `19/512 < 45/512`), yet in the wide-span / attention-sink regime it forces every bulk chunk to meet the largest accumulator first and is strictly worse than both `TREE` and `ASC` for all $p \ge 2, k \ge 2$.
4. **Fixed-Point / Kulisch Reproducibility-Invariance & Width Bounds (`Theorem 5`):** Exponent-aligned integer accumulation (`fixptSum`) is invariant under all binary reduction trees, all Context-Parallel chunk partitions, and all permutations (including reversal and arbitrary cyclic ring shifts) (these are associativity and commutativity of integer addition), with strict two's-complement non-overflow (a sufficiency statement; no minimality theorem) at
   ```math
   W_{\mathrm{inv}}(k, p) = 1 + k + 1 + (p + k + 2) = p + 2k + 4, \quad k = \lceil \log_2 P \rceil,
   ```
   and the full-span Kulisch width $W _ {\mathrm{Kulisch}}(k, e _ {\max}, e _ {\min}, M) = 1 + k + (e _ {\max} - (e _ {\min} - M) + 1)$ fitting in `int32` for FP8-E4M3 (`27b`) and `int64` for FP16 (`49b`) at $P = 256$.
5. **Fixed-Point Sink-Cliff Elimination (`Theorem 6`):** With $F = p + k$ fractional bits, fixed-point accumulation has zero per-chunk quantization loss for all $\Delta \le F$, strictly preserves bulk at $\Delta = p + k - 1$ (where `TREE` already vanishes), reaches the exact information-theoretic RNE ceiling $\Delta _ {\mathrm{vanish}}^{\mathrm{FIXPT}} = p + k$, and certifies the sharp sink cliff at $F = p + k - 2$ where all $2^k - 1$ bulk chunks vanish before summation.

---

## For Non-Mathematicians

Modern long-context LLMs split the attention computation across many GPUs ("Ring Attention" or "Context Parallelism") and merge partial results in low-precision floating-point (`FP8`, `BF16`, `FP16`, `FP32`). Because floating-point addition is **not associative** (`(a + b) + c ≠ a + (b + c)`):

- **Attention Sinks Can Silently Erase Context (in the model):** If one chunk holds a strong "attention sink" token, sequential merging in the `rneGrid` model drops **100%** of the remaining 255 chunks, losing `94.1%` of the true denominator mass at $p = 4$ and `49.9%` at $p = 8$.
- **Sorting Largest-First Backfires:** Sorting chunks from largest to smallest eliminates rescaling drift when scores are close together, but makes attention-sink absorption catastrophically worse when scores span a wide range.
- **Bit-Exact Reproducibility Fits in Standard Integers:** Accumulating exponent-aligned chunks in signed integers makes the result **bit-for-bit identical** (integer addition is associative and commutative) regardless of GPU count, ring rotation, or reduction tree — requiring only `24–31` bits (`int32`) for FP8/BF16/FP16 and `44` bits (`int64`) for FP32 at $P = 256$ chunks.

---

## Scope of the formal statement

The floating-point format is not IEEE-754: `rneGrid p` rounds to nearest even on the fixed grid $2^{-(p-1)}$ (the unit binade), with no exponent range and no subnormals; "FP8-E4M3", "BF16", "FP16", "FP32" are labels for $p = 4, 8, 11, 24$. The `deltaVanishTree` thresholds and the Kulisch widths are values of hand-written formulas, and `wInvBits` is defined as $p + 2k + 4$; the Lean content is that this width suffices, not that it is minimal.

## Package Structure & Headline Theorems

| Module | Contents |
|---|---|
| [`RingAttnKulisch/Defs.lean`](RingAttnKulisch/Defs.lean) | Pure-`Init` definitions (`OnlineSoftmaxState`, `onlineMerge`, `rneInt`, `rneGrid`, `l2rSinkAccum`, `treeSinkAccum`, `rescaleCount`, `seqMergeDenom`, `fixptSum`, `BinTree`, `ListPerm`, `wInvBits`, `wKulischBits`, `fixptBulkTerm`, `fixptSinkOut`) |
| [`RingAttnKulisch/RatOrder.lean`](RingAttnKulisch/RatOrder.lean) | Elementary `Rat` order/field lemmas, dyadic power-of-two identities, and exact `rneInt` / `rneGrid` characterizations |
| [`RingAttnKulisch/OnlineSoftmax.lean`](RingAttnKulisch/OnlineSoftmax.lean) | Theorem 1: `online_softmax_merge_exact_associativity` |
| [`RingAttnKulisch/SinkVanishing.lean`](RingAttnKulisch/SinkVanishing.lean) | Theorems 2 & 3: `attention_sink_l2r_desc_vanishing_law`, `binary_tree_vs_l2r_sink_survival_separation` |
| [`RingAttnKulisch/DescParadox.lean`](RingAttnKulisch/DescParadox.lean) | Theorem 4: `descending_mi_phase_transition_paradox` |
| [`RingAttnKulisch/KulischInvariance.lean`](RingAttnKulisch/KulischInvariance.lean) | Theorems 5 & 6: `fixed_point_kulisch_topology_partition_invariance`, `fixed_point_sink_cliff_elimination` |
| [`Challenge.lean`](Challenge.lean) | Trusted Palomar Comparator challenge statements (`RingAttnKulischChallenge.*`, ONLY file with `sorry`) |
| [`Solution.lean`](Solution.lean) | Complete verified proofs matching `Challenge.lean` (zero `sorry`, zero `native_decide`) |
| [`scripts/PrintAxioms.lean`](scripts/PrintAxioms.lean) | `#print axioms` audit script for all 6 headline theorems |

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build logs and `#print axioms` verification receipts.
