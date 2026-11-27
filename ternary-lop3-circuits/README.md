# Minimal-`LOP3` Ternary Bit-Plane Unpacking, INT4/FP4 Dot Products, and CSA Conservation (`ternary-lop3-circuits`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **8 / 10** | **9 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): co-designed minimal-`LOP3` bit-plane unpacking circuits for packed 1.58-bit ternary weights — a 6-`LOP3` depth-2 3-trit/5-bit circuit together with a counting lower bound (no output lane is an input literal; informally 6 gates, no gate count is formalised), a 14-`LOP3` depth-4 escape-cube 5-trit/8-bit circuit with a pigeonhole 4-variable support impossibility theorem, exact 9-`LOP3` ternary $\times$ signed INT4 and 4+10-`LOP3` zero-offset ternary $\times$ FP4 (E2M1) dot-product circuits, and universal 3:2 Carry-Save-Adder `popcnt` conservation over unbounded $\mathbb{N}$ — formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Represent a ternary weight $w \in \{-1, 0, +1\}$ as a disjoint bit-plane pair $(p, n) \in \{0, 1\}^2$ with $p \land n = 0$ and value $w = p - n$. Packing $m$ trits into $b$ bits ($3^m \le 2^b$) and co-designing the offline encoding $E : \{-1, 0, +1\}^m \to \{0, 1\}^b$ for 3-input Boolean lookup gates $\mathrm{LOP3}(a, b, c, \mathrm{imm8})$ (PTX `lop3.b32`) yields sharp circuit-complexity and arithmetic identities:

1. **3-trit / 5-bit unpacking ($1.667$ bits/trit, 6 `LOP3` gates, depth 2):** We exhibit an explicit 6-`LOP3` depth-2 circuit `unpack3t5b` on $\mathrm{Fin}\;32$ whose outputs are disjoint on all $32$ inputs and cover all $27$ ternary triples **outside** the 4-codeword escape cube $x _ 0 \land \neg x _ 1 \land x _ 3$. Conversely, for *any* surjective disjoint decoder $D : \mathrm{Fin}\;32 \to (\mathrm{Bool} \times \mathrm{Bool})^3$, each of the $6$ output lanes takes value `true` on at least $9$ inputs and `false` on at least $18$ inputs; since every input literal $x _ j$ or $\neg x _ j$ is `false` on exactly $16 < 18$ inputs, **no** output lane can be a direct input pass-through. Informally, if each non-wire output lane costs one gate, this gives $6$ gates; the gate-cost step is not formalised.
2. **Escape-cube 5-trit / 8-bit unpacking ($1.600$ bits/trit, 14 `LOP3` gates, depth 4):** Using the 4-codeword escape cube `esc = x0 && !x1 && x3` ($32$ escape codewords in $\mathrm{Fin}\;256$) to multiplex `(x0, x1, x3)` with `(x5, x6, x7)`, we obtain a 14-`LOP3` depth-4 circuit `unpack5t8b` that is disjoint on all $256$ inputs and surjective onto all $3^5 = 243$ ternary 5-tuples. Conversely, for *any* surjective disjoint decoder $D : \mathrm{Fin}\;256 \to (\mathrm{Bool} \times \mathrm{Bool})^5$, every output lane has Hamming weight in $[81, 256 - 162] = [81, 94]$. Because any Boolean function on $\mathrm{Fin}\;256$ depending on at most $4$ input bits has Hamming weight divisible by $2^{8 - 4} = 16$, and no multiple of $16$ lies in $[81, 94]$ ($80 < 81$ and $94 < 96$), **no** output lane can depend on $\le 4$ input bits.
3. **Exact bit-sliced ternary $\times$ INT4 & FP4 (E2M1) products and CSA conservation:** A 9-`LOP3` circuit computes $(y _ 0, \dots, y _ 4)$ with $y _ 0 + 2 y _ 1 + 4 y _ 2 + 8 y _ 3 + 16 y _ 4 = w \cdot x + 8$ for all $w \in \{-1, 0, 1\}$ and signed 4-bit $x \in [-8, 7]$, with $y _ 4 \equiv 0$ on symmetric $[-7, 7]$ (8 `LOP3`s, 4 `POPCNT`s). A 4-`LOP3` FP4 (E2M1) magnitude decoder paired with a 10-`LOP3` sign-magnitude product computes $y _ 0 + 2 y _ 1 + 4 y _ 2 + 8 y _ 3 - 16 t _ 4 = w \cdot (2 x _ {\mathrm{FP4}})$ with zero floating-point instructions and zero constant offset. Finally, the 3:2 Carry-Save Adder identity $\mathrm{popcnt}(a) + \mathrm{popcnt}(b) + \mathrm{popcnt}(c) = \mathrm{popcnt}(a \oplus b \oplus c) + 2 \cdot \mathrm{popcnt}((a \land b) \lor (b \land c) \lor (a \land c))$ holds universally for all $a, b, c \in \mathbb{N}$.

## For Non-Mathematicians

Modern "1.58-bit" AI models (like BitNet) store every weight as just $-1$, $0$, or $+1$. The naive way to store these weights uses $2$ bits per weight, wasting $20\%$ of precious GPU memory bandwidth. Standard compression packs $5$ weights into $8$ bits (or $3$ into $5$), but unpacking them with division and modulo is slow on GPUs. Instead, we redesign the weight encoding so a GPU can unpack $32$ weights at a time using nothing but a handful of single-cycle 3-input logic instructions (`LOP3`) — no multiplies, no divides, no lookup tables. We prove in Lean 4 that, in the 3-weight/5-bit unpacking, no output bit can be a plain input bit (so, informally, six gates are needed; Lean has no gate-count theorem), that our $14$-gate 5-weight/8-bit unpacker covers all $243$ combinations without a single invalid state, that no 5-weight/8-bit output bit can ever depend on $4$ or fewer input bits, and that our bitwise dot-product circuits for 4-bit integers and 4-bit floating-point numbers (FP4) — plus the Carry-Save Adder bit-counting shortcut — are exact on every possible input (checked exhaustively).

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of minimal-`LOP3` packed ternary bit-plane unpacking, exact information-theoretic lower bounds, bit-sliced ternary $\times$ INT4/FP4 dot-product circuits, and universal 3:2 CSA `popcnt` conservation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `unpack_3t5b_sound_and_surjective` | The 6-`LOP3` depth-2 circuit `unpack3t5b` has zero invalid `(true, true)` lanes on all `x : Fin 32` and hits all $27$ ternary triples outside the 4-codeword escape cube `x0 && !x1 && x3`. |
| `unpack_3t5b_six_gate_lower_bound` | (Counting bound; "six gate" is an informal reading, no gate count is stated in Lean.) For any disjoint surjective decoder `D : Fin 32 → (Bool × Bool)^3`, every output lane is `true` on $\ge 9$ inputs and `false` on $\ge 18$ inputs, so no output lane equals any input literal `x_j` or `!x_j`. |
| `unpack_5t8b_sound_and_surjective` | The 14-`LOP3` depth-4 escape-cube circuit `unpack5t8b` has zero invalid `(true, true)` lanes on all `x : Fin 256` and hits all $243$ ternary 5-tuples. |
| `unpack_5t8b_four_var_impossibility` | For any disjoint surjective decoder `D : Fin 256 → (Bool × Bool)^5`, every output lane has weight in $[81, 94]$, so no output lane satisfies `DependsOnAtMost4` (weight must be a multiple of $16$). |
| `ternary_int4_exact5_sound` | For all disjoint `(p, n)` and 4-bit two's-complement `x ∈ [-8, 7]`, the 9-`LOP3` circuit satisfies $y _ 0 + 2 y _ 1 + 4 y _ 2 + 8 y _ 3 + 16 y _ 4 = w \cdot x + 8$, and $x \neq -8 \to y _ 4 = \mathrm{false}$. |
| `ternary_fp4_exact5_sound` | For all disjoint `(p, n)` and FP4 (E2M1) codes `(s, e1, e0, m0)`, the 4+10-`LOP3` circuit satisfies $y _ 0 + 2 y _ 1 + 4 y _ 2 + 8 y _ 3 - 16 t _ 4 = w \cdot (2 x _ {\mathrm{FP4}})$ with zero offset and zero FP ops. |
| `csa32_popcnt_conservation` | For all $a, b, c \in \mathbb{N}$, $\mathrm{popcnt}(a) + \mathrm{popcnt}(b) + \mathrm{popcnt}(c) = \mathrm{popcnt}(a \oplus b \oplus c) + 2 \cdot \mathrm{popcnt}((a \land b) \lor (b \land c) \lor (a \land c))$. |

## Proof Architecture

1. **Shallow Kernel-Verified Circuit Correctness (`unpack_3t5b_sound_and_surjective`, `unpack_5t8b_sound_and_surjective`, `ternary_int4_exact5_sound`, `ternary_fp4_exact5_sound`):**
   - `unpack3t5b` is verified exhaustively on all $32$ inputs and all $27$ ternary triples by `decide` in the Lean 4 kernel (zero `native_decide`).
   - `unpack5t8b` disjointness is split across `Fin 16 × Fin 16` ($16 \times 16 = 256$) so `decide` stays within default recursion depth; 243/243 surjectivity is certified by exhibiting an explicit right-inverse encoder `encode5t8b` partitioned into nine 27-entry blocks and verifying `unpack5t8b (encode5t8b t0 t1 t2 t3 t4) = (t0, t1, t2, t3, t4)` by `decide`.
   - The INT4 and FP4 dot-product circuits are verified on all $2^6 = 64$ Boolean input combinations by case splitting and `simp_all`.
2. **General Pigeonhole Cardinality Framework (`unpack_3t5b_six_gate_lower_bound`, `unpack_5t8b_four_var_impossibility`):**
   - Using `length_le_of_nodup_subset` over `List.finRange`, any surjective map onto $m$ distinct targets forces at least $m$ inputs to satisfy any predicate implied by those targets (`le_countTrue_of_exists`).
   - For `Fin 32`, this forces $\ge 9$ true and $\ge 18$ false inputs per lane, ruling out all $10$ input literals (`countTrue_not_lit5` = $16 < 18$).
   - For `Fin 256`, this forces $\ge 81$ true and $\ge 162$ false inputs per lane (hence Hamming weight $\in [81, 94]$). Any function satisfying `DependsOnAtMost4` is invariant under flipping $4$ distinct bit positions outside its support (`exists_four_distinct_outside`), and each flip-invariant bit halves the true-count via the involution `flipBit` (`countTrue_double_of_flip_inv`), proving $16 \mid \mathrm{countTrue}(f)$ — impossible in $[81, 94]$.
3. **Universal Inductive CSA Conservation (`csa32_popcnt_conservation`):**
   - Proved for all unbounded $a, b, c \in \mathbb{N}$ by well-founded induction on $a + b + c$: unfolding `popcnt` into bit $0$ plus `popcnt (n / 2)`, pushing `% 2` and `/ 2` through `^^^`, `&&&`, and `|||`, and combining the 8-case full-adder LSB identity `csa32_bit_identity` with the inductive hypothesis.

## Prior-Art Context

- **BitNet b1.58 (Ma et al., 2024, *"The Era of 1-bit LLMs: All Large Language Models are in 1.58 Bits"*):** Popularized ternary $\{-1, 0, +1\}$ weights ($\log _ 2 3 \approx 1.585$ bits/weight) and 5-trit/byte packing, typically decoded via base-3 arithmetic (multiplies/shifts/modulo) rather than co-designed bitwise `LOP3` bit-plane circuits.
- **T-MAC (Wei et al., 2024, *"T-MAC: CPU Renaissance via Table Lookup for Low-Bit LLM Deployment on Edge"*):** Replaces multiply-accumulate with byte-indexed lookup tables (LUTs) over groups of weights, trading arithmetic for shared-memory/register LUT pressure and 2.00 bits/trit storage for 4-trit/byte layouts. Our co-designed `LOP3` bit-plane decoders eliminate LUTs entirely while achieving $1.600$–$1.667$ bits/trit.
- **NVIDIA PTX `lop3.b32` & Harley-Seal Carry-Save Adders (CSA):** Single-instruction 3-input arbitrary Boolean lookup (`LOP3`) and Harley-Seal 3:2 CSA bit-heap compression (`XOR3` + `MAJ3`) are classical high-throughput SIMD/GPU primitives for `popcnt` reduction. Combining them with co-designed escape-cube ternary encodings yields unpacking circuits with the counting lower bounds above (optimality is not proved) and verified bit-exact INT4/FP4 dot-product pipelines.

## Scope of the formal statement

Lean has no gate model here. The `LOP3` circuits are explicit tables evaluated exhaustively, and the lower bounds are counting facts about output lanes (weights $9/18$ and $81/162$). "At least 6 gates" and "no lane depends on $\le 4$ inputs implies depth" are informal readings, and no optimality of the 6-gate or 14-gate circuits is proved. The FP4 circuit refers to the decode `fp4Scaled2` in `Defs.lean`, not to hardware.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` output, and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
