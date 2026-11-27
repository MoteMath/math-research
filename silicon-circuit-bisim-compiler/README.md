# SiliconBisim: Bit-Slice & Recursive Circuit-Generator Bisimulation Compiler (`silicon-circuit-bisim-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): four-engine kernel-verified gate-DAG circuit-generator bisimulation compiler discharging infinite-width equivalences for linear/block-speculative adders, 4-topology parallel-prefix trees (with reachable-subset associativity), logarithmic/recursive shifters, Omega/butterfly networks, and Batcher Bitonic vs Odd-Even sorting networks + Knuth 0-1 Principle in pure Lean 4 Init.*

## For Mathematicians

We build **`SiliconBisim`**, a four-engine, kernel-verified circuit-generator bisimulation compiler over an explicit first-order Boolean gate-DAG DSL (`GateNet`). Rather than proving each hardware family equivalent by hand, each engine accepts concrete gate netlists plus a pure-data finite binary certificate (`BitVec` relation masks, reachable-token masks, or finite truth-table checks, zero `Prop` fields), checks it via kernel `decide` (zero `native_decide`), and lifts it to universally quantified equivalence across all widths ($\forall w \in \mathbb{N}$ or $\forall k \in \mathbb{N}$ at width $2^k$):

1. **Engine 1 (`slice_bisim_sound`, `block2_bisim_sound`):** Arbitrary-state-width linear bisimulation and 2-bit speculative block synchronization, certifying ripple-carry $\equiv$ dual-rail complementary-carry and ripple-carry $\equiv$ 2-bit carry-select adders for all widths.
2. **Engine 2 (`prefix_all_topologies_sound`, `four_way_prefix_adder_equiv`, `parallel_gray_decoder_equiv`):** Reachable-subset associativity + monoid-action homomorphism certifies **Serial, Sklansky, Brent–Kung, and Kogge–Stone** topologies simultaneously — including don't-care-optimized glitched cells that fail global associativity on $\mathrm{BitVec}\; 2$ yet are sound on the reachable 3-state XOR-propagate subsemigroup.
3. **Engine 3 (`three_way_shifter_equiv`):** Gate-level 8-case mux reflection certifies recursive tree rotators $\equiv$ logarithmic barrel rotators $\equiv$ unary iterated rotators across differing gate netlists (SOP, NAND-only, XOR-AND) and arbitrary non-power-of-two widths.
4. **Engine 4 (`reed_muller_anf_butterfly_all_k`, `gf4_butterfly_inverse_all_k`, `bitonic_andOr_eq_oddEven_nand_all_k`):** 4-wire interchange lifting, 2-wire inverse cancellation, unconditional Pease/Omega constant-geometry equivalence, and Batcher Bitonic $\equiv$ Batcher Odd-Even $\equiv$ Threshold Sort paired with a kernel-verified Knuth 0–1 Principle.

## For Non-Mathematicians

Real computer chips rarely use the slow textbook ripple-carry adder or naive shifter: they use intricate recursive parallel trees like Sklansky, Brent–Kung, and Kogge–Stone adders, logarithmic barrel rotators, Omega butterfly networks, and Batcher sorting networks built from raw NAND/XOR/MUX gates. Instead of writing a separate mathematical proof for every gate layout, we built a verified Lean 4 compiler that checks a tiny finite binary certificate on the building-block gate cell and automatically proves that the entire parallel circuit is bit-for-bit identical to the simple reference specification for **every** word width ($8, 32, 64, 2^{100}$ bits) — even for clever "glitched" hardware cells that only work on reachable carry states!

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of **`SiliconBisim`**, a four-engine gate-DAG bisimulation compiler certifying infinite-width equivalences for adders, 4-topology parallel-prefix trees, shifters, butterfly/Omega networks, and Batcher sorting networks.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `slice_bisim_sound` | Engine 1 soundness: a finite binary relation mask `SliceBisimCert` certifies bit-for-bit equivalence of two gate-level slice generators (even with different state widths) for all input lengths $w \in \mathbb{N}$. |
| `prefix_all_topologies_sound` | Engine 2 soundness: a reachable-token mask `PrefixToSliceCert` certifies Serial, Sklansky, Brent–Kung, and Kogge–Stone prefix trees simultaneously for all $k \in \mathbb{N}$ (width $2^k$). |
| `four_way_prefix_adder_equiv` | 4-way cross-encoding equivalence of Sklansky (XOR-prop + glitched cell), Brent–Kung (OR-prop), Kogge–Stone (active-low NAND), and Ripple-Carry adders for all $k \in \mathbb{N}$. |
| `parallel_gray_decoder_equiv` | For all $k \in \mathbb{N}$, Sklansky, Brent–Kung, Kogge–Stone, and Serial XOR-chain Gray-to-Binary decoders are bit-for-bit identical. |
| `three_way_shifter_equiv` | For all $k \in \mathbb{N}$, the NAND-only recursive tree rotator, XOR-AND barrel rotator, and unary iterated rotator are bit-for-bit identical. |
| `reed_muller_anf_butterfly_all_k` | For all $k \in \mathbb{N}$, the Fast Reed–Muller / ANF butterfly satisfies `omegaNet = fwdButterfly = bwdButterfly` and `fwdButterfly ∘ fwdButterfly = id`. |
| `gf4_butterfly_inverse_all_k` | For all $k \in \mathbb{N}$, the non-involutive order-3 $\mathrm{GF}(4)$ linear butterfly and its inverse satisfy `fwdButterfly inv ∘ fwdButterfly fwd = id` and `omegaNet = bwdButterfly`. |
| `bitonic_andOr_eq_oddEven_nand_all_k` | For all $k \in \mathbb{N}$, Batcher Bitonic Sort (AND/OR comparators) $\equiv$ Batcher Odd-Even Mergesort (5-gate NAND-only comparators) $\equiv$ Threshold Sort. |

## Proof Architecture

1. **Explicit Gate-DAG DSL (`GateNet`) & Linear/Block Bisimulation (`slice_bisim_sound`, `block2_bisim_sound`):** Models 10 hardware primitives directly and lifts finite `BitVec` relation masks checked by `decide` to arbitrary-width sequential and 2-bit speculative block equivalence.

2. **Reachable-Subset Prefix-Tree Compiler (`prefix_all_topologies_sound`):** Restricts associativity and monoid-action obligations to a finite reachable bitmask $V$, certifying don't-care-optimized glitched cells across Serial, Sklansky, Brent–Kung, and Kogge–Stone topologies.

3. **Shifter & Butterfly/Omega Algebraic Lifters (`three_way_shifter_equiv`, `omega_eq_fwdButterfly_sound`):** Lifts 8-case mux checks, 64-case 4-wire interchange checks, and 8-case 2-wire inverse checks to width-$2^k$ recursive trees and constant-geometry Omega networks.

4. **Batcher Sorting Networks & Knuth 0–1 Principle (`bitonic_andOr_eq_oddEven_nand_all_k`, `zero_one_principle`):** Certifies cross-netlist Bitonic vs Odd-Even equivalence for all $k \in \mathbb{N}$ alongside a standalone kernel-verified Knuth 0–1 Principle and 18 rejected hostile mutations.

## Prior-Art Context

- **Classical hardware architectures:** Sklansky (1960), Pease (1968), Batcher (1968), Kogge–Stone (1973), Knuth (1973), and Brent–Kung (1982) introduced the parallel-prefix, Omega, and sorting network topologies.
- **Novel contribution:** A unified, pure-Init Lean 4 certificate-compiler architecture over an explicit gate-DAG DSL supporting reachable-subset restricted associativity (certifying non-globally-associative glitched cells), an exhaustive 256-cell butterfly interchange taxonomy (separating 2-wire inversion from 4-wire interchange), and four recursive hardware topology engines discharged by kernel `decide`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build logs and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. `scripts/explore_and_verify.py` replays the finite certificates and sharpness counterexamples in exact integer arithmetic (zero floats).
