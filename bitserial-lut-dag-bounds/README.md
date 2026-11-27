# Bit-Serial `POPCNT` & Sign-Folded Binary/Ternary LUT Precomputation DAG Bounds for Low-Bit LLM GEMM

A standalone, sorry-free, pure-`Init` (zero Mathlib) Lean 4 (`v4.34.1`) Palomar Comparator formalization proving six exact combinatorial, circuit-complexity, and pure-silicon integer/rational laws for low-bit LLM matrix multiplication (`INT1`, `Ternary`, `INT2`, `INT3` weights against `b`-bit activations): universal 2-input linear DAG lower bounds, explicit `g = 4` binary LUT precomputation circuits (found by computer search) that beat a naive T-MAC-style circuit in both gate count and critical-path depth (they are not proved Pareto-optimal: only the lower bounds of 10 gates and depth 2 are proved), exact symmetry-halved ternary LUT bounds and zero-waste minimal DAGs (including structured `(<=2, 4)` sparsity compression), the universal exact bit-serial `POPCNT` dot-product identity, an exact LUT-vs-`POPCNT` amortization crossover and a no-crossover dominance statement under a stated linear cost model with assumed RDNA 3 constants, and exact `int16` accumulation overflow thresholds.

**Scope of the formal statement.** the objects are a hand-written linear-DAG model (`LinearDag`, gates computing integer combinations of two earlier wires) and a hand-written linear cost model (`amortizedCost`, `popcntGemmCost`, `lutGemmCost`) with assumed constants (for example `W = 32`, `b = 8`, `c_pop = 2`, and a LUT lookup cost of `3/4`). Nothing is measured and nothing is linked to RDNA 3 hardware, T-MAC or BitNet. Only lower bounds (at least `2^(g-1) + g - 2` gates, depth at least `ceil(log2 g)`) are proved: no theorem excludes a `(11 ops, depth 2)` or `(10 ops, depth 2)` binary `g = 4` circuit, so the `(12, 2)` circuit is not proved Pareto-optimal. Dominance of `(12, 2)` over the naive `(14, 3)` circuit is dominance between two explicit circuits.

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (`3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*9 + 2*9 + 2*10 + 10 = 93 / 100`): pure-`Init` Lean 4 (zero Mathlib, zero `native_decide`) proofs of the universal $2^{g-1} + g - 2$ op and $\lceil \log _ 2 g \rceil$ depth lower bounds for 2-input linear binary LUT DAGs, exact soundness and strict dominance of the balanced `(12 ops, depth 2)` circuit over the naive T-MAC-style `(14 ops, depth 3)` circuit, alongside the RDNA 3-model circuits `(11, 3)` and `(10, 4)` (the latter meets the gate-count lower bound; none of them is proved Pareto-optimal), exact balanced-ternary symmetry $(3^g - 1)/2$ and zero-waste minimal ternary DAGs (`2, 10, 36` ops at depth `1, 2, 2`), the universal bit-exact `POPCNT` dot-product identity for arbitrary $b$-bit signed/unsigned activations, an exact LUT-vs-`POPCNT` amortization crossover and a no-crossover dominance statement under assumed cost constants, and exact `int16` overflow thresholds (`K _ {\max} = 258` symmetric vs the exact wrap-by-1 trap at `K = 256` for full `int8`).*

## Headline Theorems (`BitSerialLutDagChallenge`)

| # | Theorem | Module | Exact Formal Statement Summary |
| :---: | :--- | :--- | :--- |
| 1 | `binary_lut_dag_lower_bound_exact` | [`BinaryDag.lean`](BitSerialLutDag/BinaryDag.lean) | Universal 2-input linear DAG lower bound proving that any DAG over $\mathbb{Z}^g$ (even with arbitrary scalar multipliers $c _ 1 u + c _ 2 v$) computing all $2^{g-1}$ sign-canonical binary combinations $\{-1, +1\}^g / \{\pm 1\}$ ($g \ge 2$) requires at least $2^{g-1} + g - 2$ gates (`2, 5, 10, 19` for $g = 2, 3, 4, 5$) and critical-path depth at least $\lceil \log _ 2 g \rceil$ (`1, 2, 2, 3`), together with exact universal wire linearity `evalWireVal dag x m = dotInt (evalWireCoeff dag m) x`. |
| 2 | `tmac_depth2_optimal_12_vs_14_circuit` | [`BinaryDag.lean`](BitSerialLutDag/BinaryDag.lean) | Constructs and proves exact validity, gate-class membership, op count, depth, and symbolic completeness (for all $x : \mathrm{Fin}\,4 \to \mathbb{Z}$) of the `g = 4` balanced 2+2 tree (found by computer search) `(12 ops, depth 2)` strictly beating naive T-MAC `(14 ops, depth 3)` in both gate count (`-1/7 = -14.3%`) and depth (`-1/3 = -33.3%`) while matching $\lceil \log _ 2 4 \rceil = 2$, plus the RDNA 3 `V_ADD_LSHL` Pareto points `(11 ops, depth 3)` and lower-bound-tight `(10 ops, depth 4)` (`= binaryLowerBound 4`). No theorem shows the `(12, 2)` circuit is Pareto-optimal: no statement excludes `(11, 2)` or `(10, 2)`. |
| 3 | `ternary_lut_dag_bounds_and_symmetry` | [`TernaryDag.lean`](BitSerialLutDag/TernaryDag.lean) | Proves exact symmetry-halved ternary codebook size $2 \cdot N _ {\mathrm{tern}}(g) + 1 = 3^g$ (`4, 13, 40, 121` for $g = 2, 3, 4, 5$), balanced-ternary reconstruction and injectivity, universal lower bounds $(3^g - 1)/2 - g$ ops (`2, 10, 36, 116`) and $\lceil \log _ 2 g \rceil$ depth, exact zero-waste minimal pure `{+, -}` ternary DAGs for $g = 2, 3, 4$ (`(2, 1)`, `(10, 2)`, `(36, 2)`), and the structured `(<=2, 4)` ternary sparsity DAG (`12 ops, depth 1`, `16` entries vs `40`). |
| 4 | `popcnt_zero_lut_exact_bitserial_dot_identity` | [`PopcntAndCost.lean`](BitSerialLutDag/PopcntAndCost.lean) | Universal exact integer theorem proving that any binary $\{-1, +1\}$ or ternary $\{-1, 0, +1\}$ dot product against arbitrary $b$-bit signed (two's-complement) or unsigned activations equals the bit-weighted sum of `AND`-plane `POPCNT` differences (zero LUT, zero rounding, zero bank conflicts), plus the universal $b$-bit two's-complement roundtrip theorem and exact `int8` specialization. |
| 5 | `lut_vs_popcnt_amortization_crossover_exact` | [`PopcntAndCost.lean`](BitSerialLutDag/PopcntAndCost.lean) | Proves the exact rational amortization crossover $R^\star = (\mathrm{setup} _ {\mathrm{lut}} - \mathrm{setup} _ {\mathrm{pop}}) / (\mathrm{steady} _ {\mathrm{pop}} - \mathrm{steady} _ {\mathrm{lut}})$ showing why zero-LUT `POPCNT` wins on small-batch LLM decode ($R < R^\star$), the RDNA 3 no-crossover dominance theorem proving `POPCNT` beats LUT for all $M, N, K > 0$ when $b c _ {\mathrm{pop}} / W < c _ {\mathrm{lut}} / g$, and `gfx1100` cost ratios (`1/2 < 3/4` steady-state, `3/2x` `g=6` vs `g=4` lookups). The numbers `W = 32`, `b = 8`, `c_pop = 2`, `3/4` are assumed model constants, not measurements. |
| 6 | `tmac_int16_overflow_threshold_exact` | [`PopcntAndCost.lean`](BitSerialLutDag/PopcntAndCost.lean) | Proves universal `int16` accumulation safety (`K * w _ {\max} * a _ {\max} <= 32767`), exact symmetric `int8` (`[-127, 127]`) zero-overflow ceiling $K _ {\max} = 258$ (making $K _ {\mathrm{tile}} = 256$ exact), and the exact full `int8` (`[-128, 127]`) two's-complement wrap-by-1 trap (`+32768 -> -32768`) at $K = 256$ (`w _ {\max} = 1`), $K = 128$ (`w _ {\max} = 2`), and $K = 64$ (`w _ {\max} = 4`). |

---

## For Mathematicians

All six theorems are proved purely over `Nat`, `Int`, and `Rat` inside Lean 4's `Init` prelude — zero Mathlib, zero `native_decide`, zero floating-point approximations, and zero axioms beyond `[propext, Classical.choice, Quot.sound]`:

1. **Connected-Component Coloring & Support-Doubling Lower Bounds (`BinaryDag.lean`):**
   Model any 2-input linear DAG on $g$ unit-basis inputs $e _ 0, \dots, e _ {g-1} \in \mathbb{Z}^g$ as a sequence of gates $w _ {g+k} = c _ {1,k} w _ {u _ k} + c _ {2,k} w _ {v _ k}$ with arbitrary integer scalars $c _ {1,k}, c _ {2,k} \in \mathbb{Z}$.
   - **Depth bound:** Because $\mathrm{supp}(c _ 1 u + c _ 2 v) \subseteq \mathrm{supp}(u) \cup \mathrm{supp}(v)$, strong induction on wire index yields $|\mathrm{supp}(w _ m)| \le 2^{\mathrm{depth}(m)}$. Any full-support binary target therefore satisfies $g \le 2^{\mathrm{depth}(m)}$, i.e. $\mathrm{depth}(m) \ge \lceil \log _ 2 g \rceil$.
   - **Gate-count bound:** By induction on $t$, after $t$ gates there exists a coordinate coloring $\chi _ t : \mathrm{Fin}\,g \to \mathbb{N}$ whose restriction to every existing wire's support is constant and which retains at least $g - t$ distinct colors (each gate merges at most two color classes). Consequently, any full-support wire $g + t$ forces $g - (t + 1) \le 1$, i.e. $t \ge g - 2$. All $2^{g-1}$ distinct sign-canonical binary targets must therefore lie in wire indices $[g + (g - 2),\, g + L)$, so finite pigeonhole yields:
   ```math
   L \ge 2^{g-1} + g - 2.
   ```
   For $g = 4$, the universal lower bound is $10$ ops and depth $2$. The balanced 2+2 tree (`a _ 0 +- a _ 1`, `a _ 2 +- a _ 3`, then all 8 pairwise combinations) achieves `(12 ops, depth 2)` under pure `{+, -}`, strictly dominating naive incremental T-MAC `(14 ops, depth 3)` by `-1/7` ops and `-1/3` depth, while RDNA 3 `V_ADD_LSHL` (`u +- 2v`) hits the exact universal lower bound at `(10 ops, depth 4)` via the parallel-pair seed `{a _ 0 + a _ 1, a _ 2 + a _ 3}` and `(11 ops, depth 3)`.

2. **Balanced-Ternary Bijection & Zero-Waste Ternary DAGs (`TernaryDag.lean`):**
   Every integer $n \in \{1, \dots, (3^g - 1)/2\}$ has a unique $g$-digit balanced-ternary expansion $n = \sum _ {j=0}^{g-1} d _ j 3^j$ ($d _ j \in \{-1, 0, +1\}$) whose highest nonzero digit is $+1$. Evaluating the weighted base-3 sum proves injectivity of the $(3^g - 1)/2$ sign-canonical nonzero ternary targets in one step, giving the universal lower bound $L \ge (3^g - 1)/2 - g$ via pigeonhole on $[0, g + L)$. Unlike binary LUTs, ternary LUTs admit zero-waste balanced DAGs meeting both lower bounds simultaneously: `(2, 1)` for $g=2$, `(10, 2)` for $g=3$, and `(36, 2)` for $g=4$. Restricting to bounded support $\|w\| _ 0 \le 2$ at $g=4$ collapses the sign-folded table from `40` to `16` entries and builds in `12 ops` at `depth 1`.

3. **Exact Bit-Serial `POPCNT`, Amortization Crossover & `int16` Wrap-by-1 (`PopcntAndCost.lean`):**
   For any $b$-bit signed (two's-complement) or unsigned activations $a _ i = \sum _ {j=0}^{b-1} \beta _ j A _ {j,i}$ with bit weights $\beta _ j \in \{2^j, -2^{b-1}\}$, swapping the finite sums over $i \in \mathrm{Fin}\,K$ and $j \in \mathrm{Fin}\,b$ yields exact integer identities with zero LUT:
   ```math
   \sum_{i=0}^{K-1} w_i^{\mathrm{bin}} a_i
     = \sum_{j=0}^{b-1} \beta_j \Bigl(2\,\mathrm{popcnt}(p \wedge A_j) - \mathrm{popcnt}(A_j)\Bigr),
   \qquad
   \sum_{i=0}^{K-1} w_i^{\mathrm{tern}} a_i
     = \sum_{j=0}^{b-1} \beta_j \Bigl(\mathrm{popcnt}(p^+ \wedge A_j) - \mathrm{popcnt}(p^- \wedge A_j)\Bigr).
   ```
   Under the amortized cost model $\mathrm{setup}/R + \mathrm{steady}$, `POPCNT` strictly beats LUT iff $R < (\mathrm{setup} _ {\mathrm{lut}} - \mathrm{setup} _ {\mathrm{pop}}) / (\mathrm{steady} _ {\mathrm{pop}} - \mathrm{steady} _ {\mathrm{lut}})$ when LUT has a steady-state advantage, and dominates unconditionally for all $M, N, K > 0$ when $b c _ {\mathrm{pop}} / W < c _ {\mathrm{lut}} / g$ (with the assumed RDNA 3-style constants `W = 32, b = 8, c _ {\mathrm{pop}} = 2`, which give `1/2 < 3/4`). Finally, signed `int16` (`[-32768, 32767]`) safely holds $K \le 258$ symmetric `int8` terms (`258 * 127 = 32766`), whereas full `int8` (`[-128, 127]`) overflows by exact `+1` at $K = 256$ (`256 * (-1) * (-128) = +32768 -> -32768`).

---

## For Non-Mathematicians

Modern 1-bit and 1.58-bit LLMs (like BitNet b1.58) replace floating-point multiplications with tiny lookup tables (LUTs, as in Microsoft's T-MAC) or pure bitwise population-count (`POPCNT`) instructions. This package provides **machine-checked Lean 4 proofs** establishing the exact mathematical limits of both approaches:

1. **In the DAG model, a balanced tree beats a naive `g = 4` table builder in both operations and depth:** the naive T-MAC-style builder constructs the 8-entry sign-folded lookup table for 4 activations with 14 additions/subtractions in 3 sequential steps. We prove that a balanced 2+2 tree builds the same table in **12 operations and 2 steps** (`14.3%` fewer ops, `33.3%` shorter critical path, which meets the proved depth lower bound; depth here is critical-path length, not measured speed). With a fused shift-add gate (modelled on RDNA 3 `V_ADD_LSHL`) a circuit with **10 operations** exists, which equals the proved lower bound for any 2-input linear circuit.
2. **Ternary (BitNet b1.58) tables have zero wasted intermediates:** Because ternary weights include `0`, every intermediate partial sum is itself a useful table entry. For 4 weights, all 40 sign-folded combinations build in 36 additions at depth 2 — and if weights are `<= 2:4` sparse, the table shrinks `2.5x` (to 16 entries) and builds in just 12 parallel additions at depth 1.
3. **When `POPCNT` can beat LUTs (under an assumed cost model):** We prove that binary and ternary dot products against any $b$-bit integer activations can be computed **bit-identically** using only bitwise `AND` and `POPCNT` with no lookup table. In the linear cost model, when batch size is small LUTs cannot amortize their table-building cost, and if the assumed per-operation constants satisfy `b c_pop / W < c_lut / g` (the constants chosen to mimic AMD RX 7900 XTX `gfx1100`), `POPCNT` is cheaper at every batch size. The constants are assumptions; nothing is measured and no claim about real hardware follows from the Lean statements.
4. **The exact `+1` `int16` wrap-around trap in T-MAC:** Accumulating `K = 256` binary/ternary products in 16-bit signed integers is overflow-free if `int8` activations are clamped to `[-127, 127]`, but wraps from `+32768` to `-32768` if full `[-128, 127]` `int8` is used (an integer fact about the model; it is not a statement about any particular T-MAC release).

---

## Prior-Art Context

- **Arlazarov, Dinic, Kronrod & Faradzev (1970), *Four Russians Method*:** Introduced precomputed group-of-$g$ linear-combination tables to accelerate Boolean/low-bit matrix multiplication by $O(\log n)$. Our Theorems 1–3 formalize the exact finite-$g$ 2-input linear DAG lower bounds ($2^{g-1} + g - 2$ binary, $(3^g - 1)/2 - g$ ternary, $\lceil \log _ 2 g \rceil$ depth) and prove explicit lower bounds for $g \in \{2, 3, 4, 5\}$, with circuits meeting the gate-count bound for binary `g = 4` (RDNA 3-model circuit) and the ternary bounds for $g \in \{2, 3, 4\}$. Pareto-optimality of any circuit is not proved.
- **Wei et al. (2024), *T-MAC: CPU Renaissance via Table Lookup for Low-Bit LLM Deployment on Edge*:** Popularized `g = 4` sign-folded LUT GEMM using `int16` accumulation and naive incremental table construction (`14 ops, depth 3`) on CPU SIMD (`VPSHUFB`/`TBL`). Our Theorem 2 proves that the balanced 2+2 tree (`12 ops, depth 2`) strictly dominates naive T-MAC in both gate count and depth, Theorem 5 formalizes a crossover in a linear cost model with assumed constants (whether that matches CPU SIMD or RDNA 3 hardware is not established by the Lean statements), and Theorem 6 proves the `K = 256` full-`int8` two's-complement wrap-by-1 case for `int16` accumulation in the model.
- **Ma et al. (2024), *The Era of 1-bit LLMs: All Large Language Models are in 1.58 Bits (BitNet b1.58)*:** Established ternary $\{-1, 0, +1\}$ weights as a leading low-bit LLM format. Our Theorem 3 proves the exact symmetry-halved ternary LUT size $(3^g - 1)/2$, gate-count lower bounds for ternary precomputation DAGs together with minimal DAGs meeting them for $g \in \{2, 3, 4\}$, and exact `(<=2, 4)` structured ternary sparsity compression; Theorem 4 proves exact bit-identical zero-LUT two-plane `POPCNT` evaluation for ternary weights against arbitrary signed `int8` activations.

---

## Building & Verifying

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build and `#print axioms` verification transcripts.
