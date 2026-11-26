# Sub-Byte E2M1, Quinary, Asymmetric 2-Bit & `LOP3` Compressor Circuits (`subbyte-e2m1-lop3`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **8 / 10** | **9 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (`3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 89 / 100`): pure Lean 4 `Init` (zero Mathlib) formalization of the four surviving Cluster 10 pure-silicon sub-byte circuit breakthroughs — 0-`LOP3` 2-trit/4-bit and optimal 4-`LOP3` 3-trit/5-bit $\to$ OCP E2M1 (FP4) unpackers with an exact $\ge 3$-gate lower bound (`I093`), a $\ge 5$-variable support impossibility barrier for all 3-quinary/7-bit decoders (`I091`/`I100`), a bijective 2-bit asymmetric `{-2, -1, 0, +1}` codebook with free signed-scale polarity flip (`I100`/`I098`), and the `LOP3` depth inversion between 4:2 and 3:2 carry-save compressors (`I098`/`I091`).*

## For Mathematicians

Let $\mathrm{e2m1TwiceVal} : \mathrm{BitVec}\;4 \to \mathbb{Z}$ denote the exact scaled OCP MXFP4 (E2M1) decoding $2 \cdot \mathrm{value}(S, E _ 1, E _ 0, M _ 0) \in \{0, \pm 1, \pm 2, \pm 3, \pm 4, \pm 6, \pm 8, \pm 12\}$, and let $\mathrm{lop3}(\mathrm{imm8}, a, b, c)$ denote the 3-input Boolean lookup gate (PTX `lop3.b32`).

1. **Direct Ternary $\to$ E2M1 Unpacking (`I093`, Theorems 1–3):**
   Because ternary weights $w \in \{-1, 0, +1\}$ embed into E2M1 as $2 w \in \{-2, 0, +2\}$ with $E _ 1 = M _ 0 = 0$ constant and sign $S$ don't-care on zero ($\pm 0.0 \mapsto 0$):
   - **2-trit / 4-bit (`unpack2t4b`):** pure bit-wire routing (**0 `LOP3` gates**) decodes all $3^2 = 9$ ternary pairs exactly.
   - **3-trit / 5-bit (`unpack3t5b`, $1.667$ bits/weight, $-58.33\%$ VRAM vs FP4):** co-designing direct sign wires $(S _ 0, S _ 1, S _ 2) = (c _ 0, c _ 1, c _ 2)$ with 4 `LOP3` gates (`0x73`, `0xC7`, `0x3B`, `0x71`) decodes all $3^3 = 27$ ternary triples exactly.
   - **General $\ge 3$-gate lower bound:** for *any* surjective 3-trit/5-bit $\to$ E2M1 decoder $D : \mathrm{BitVec}\;5 \to (\mathrm{BitVec}\;4)^3$, every nonzero-magnitude indicator $f _ i(x) := (\mathrm{e2m1TwiceVal}(D(x) _ i) \neq 0)$ has Hamming weight $w(f _ i) \in [18, 23]$. Every Boolean function on $\mathrm{BitVec}\;5$ depending on $\le 2$ input bits is invariant under flipping $3$ distinct bit coordinates, forcing $8 \mid w(g)$. Hence no $f _ i$ depends on $\le 2$ inputs, and surjectivity onto $(1, 0, 0), (0, 1, 0), (0, 0, 1)$ forces $f _ 0, f _ 1, f _ 2$ to be pairwise distinct — requiring at least $3$ distinct `LOP3` gates.
2. **3-Quinary / 7-Bit Support Barrier (`I091`/`I100`, Theorem 4):**
   For *any* surjective 3-quinary/7-bit decoder $D : \mathrm{BitVec}\;7 \to (\mathrm{Fin}\;5)^3$, any slot $s \in \mathrm{Fin}\;3$, and any non-constant predicate $P : \mathrm{Fin}\;5 \to \mathrm{Bool}$ with $k = |P^{-1}(\mathrm{true})| \in \{1, 2, 3, 4\}$, the Boolean output $f(x) := P(\mathrm{slot} _ s(D(x)))$ satisfies
   ```math
   25 k \le w(f) \le 25 k + 3 \implies w(f) \not\equiv 0 \pmod{8}.
   ```
   By the same 3-bit flip-involution lemma on $\mathrm{BitVec}\;7$, every function depending on $\le 4$ input bits has $8 \mid w(g)$. Thus every non-trivial output bit requires $\ge 5$ essential input variables (`LOP3` depth $\ge 2$).
3. **Bijective 2-Bit Asymmetric Codebook & Free Polarity Flip (`I100`/`I098`, Theorem 5):**
   The 2-bit two's-complement map $\mathrm{asym2Val}(b _ 1, b _ 0) = -2 b _ 1 + b _ 0$ is a bijection onto $\{-2, -1, 0, +1\}$ with exact zero $(0, 0) \mapsto 0$, its negation $-\mathrm{asym2Val}$ is a bijection onto $\{-1, 0, +1, +2\}$ (implementing a free codebook polarity flip via the block scale sign $s \to -s$), and for every list of $(b _ 1, b _ 0, a) \in \mathrm{Bool} \times \mathrm{Bool} \times \mathbb{Z}$,
   ```math
   \sum ( -2 b _ 1 + b _ 0 ) \cdot a = \sum _ {b _ 0 = 1} a - 2 \sum _ {b _ 1 = 1} a,
   ```
   matching the 2-bit-plane dot-product cost of ternary weights while gaining a fourth quantization level.
4. **`LOP3` Depth Inversion for 4:2 vs 3:2 Compressors (`I098`/`I091`, Theorem 6):**
   The 5-input parity bit $\mathrm{sum4to2}(x _ 0, x _ 1, x _ 2, x _ 3, c _ {\mathrm{in}}) = x _ 0 \oplus x _ 1 \oplus x _ 2 \oplus x _ 3 \oplus c _ {\mathrm{in}}$ of any 4:2 compressor cannot be computed by any single `LOP3` gate over any 3 of its 5 inputs (forcing `LOP3` depth $\ge 2$, height compression $\sqrt{2} \approx 1.414\times$ per stage), whereas the 3:2 carry-save adder (`lop3 0x96` for sum, `lop3 0xE8` for carry) is exact in $2$ `LOP3` gates at depth $1$ (height compression $3/2 = 1.500\times$ per stage, inverting the classical 2-input CMOS rule).

## For Non-Mathematicians

Modern quantized AI models squeeze weights down to 1.5–2.3 bits each to fit larger models into GPU memory, but unpacking packed bits back into GPU-friendly formats (like 4-bit FP4 / E2M1) can easily become a compute bottleneck. Instead of slow division and modulo arithmetic, we use single-cycle 3-input GPU logic instructions (`LOP3`) and prove four exact hardware laws in Lean 4:

- **Direct Ternary $\to$ FP4 (`I093`):** Because FP4 treats `-0.0` and `+0.0` identically, 2 ternary weights pack into 4 bits with **zero logic gates** (just wiring bits), and 3 ternary weights pack into 5 bits (**58.33% less VRAM than FP4**) using only **4 `LOP3` gates** — and we prove no decoder can ever use fewer than 3.
- **Why 2.33-bit Quinary Weights Need Multi-Stage Unpacking (`I091`):** Packing 3 five-level weights into 7 bits leaves only 3 spare codes out of 128; we prove that *no matter how you encode them*, every single output bit must look at at least 5 of the 7 input bits, so a single 3-input `LOP3` gate is mathematically impossible.
- **A Free Extra Weight Level at 2 Bits (`I100`):** Using `{-2, -1, 0, +1}` instead of ternary `{-1, 0, +1}` keeps exact zero, costs the exact same 2 bit-planes in dot products, and flips to `{-1, 0, +1, +2}` for free just by negating the block's scale factor.
- **Why 3:2 Adders Beat 4:2 Compressors on GPUs (`I098`):** In classic 2-input chip design, 4:2 compressors are faster than 3:2 adders. On GPUs with 3-input `LOP3` gates, the rule flips: a 3:2 adder finishes in 1 logic stage (shrinking bit-heaps by $1.5\times$ per stage), while a 4:2 compressor's 5-way XOR provably takes at least 2 stages ($\sqrt{2} \approx 1.414\times$ per stage).

---

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `unpack_2t4b_to_e2m1_zero_lop3` | The 0-`LOP3` pure-wire unpacker `unpack2t4b` and encoder `encode2t4b` decode all $9$ ternary pairs to exact E2M1 nibbles $(2 w _ 0, 2 w _ 1)$. |
| `unpack_3t5b_to_e2m1_four_lop3` | The 4-`LOP3` unpacker `unpack3t5b` (`0x73`, `0xC7`, `0x3B`, `0x71`) and encoder `encode3t5b` decode all $27$ ternary triples to exact E2M1 nibbles $(2 w _ 0, 2 w _ 1, 2 w _ 2)$. |
| `unpack_3t5b_to_e2m1_three_gate_lower_bound` | For any surjective 3-trit/5-bit $\to$ E2M1 decoder, every nonzero indicator has weight in $[18, 23]$, every $\le 2$-variable function has weight $\equiv 0 \pmod{8}$, so no indicator depends on $\le 2$ bits and all three are pairwise distinct ($\ge 3$ `LOP3` gates). |
| `quinary_3w7b_five_var_impossibility` | For any surjective 3-quinary/7-bit decoder, every non-trivial output bit has weight in $[25 k, 25 k + 3]$ ($k \in \{1, 2, 3, 4\}$), hence $\not\equiv 0 \pmod{8}$, ruling out any $\le 4$-variable dependence (`LOP3` depth $\ge 2$). |
| `asymmetric_2bit_polarity_flip_exact` | `asym2Val` is a bijection onto $\{-2, -1, 0, +1\}$ with exact zero, `-asym2Val` is a bijection onto $\{-1, 0, +1, +2\}$, and the 2-plane `foldl` dot-product identity holds for all lists. |
| `compressor_4to2_lop3_depth_inversion` | No single `LOP3` gate over any 3 of 5 inputs computes `sum4to2` (`LOP3` depth $\ge 2$), while 3:2 CSA (`lop3 0x96`, `lop3 0xE8`) is exact in 2 `LOP3` gates at depth $1$. |

## Prior-Art Context

- **OCP Microscaling Formats (MXFP4 / E2M1, Rouhani et al., 2023):** Standardized the 4-bit E2M1 floating-point nibble (`S, E1, E0, M0`) now natively accelerated in Blackwell-class Tensor Cores. Existing ternary-to-FP4 unpacking kernels (e.g. BitNet / Marlin-style dequantizers) typically unpack via shifts, masks, and lookup tables; exploiting E2M1's signed-zero don't-care (`-0.0 = +0.0`) with co-designed direct-sign `LOP3` circuits reduces 3-trit/5-bit unpacking to 4 `LOP3` instructions (`0.0417 LOP3/trit` in 32-wide bit-slicing).
- **BitNet b1.58 (Ma et al., 2024) & Quinary / 2-Bit LLM Quantization:** Standard 2-bit symmetric mid-riser codebooks `{-3, -1, +1, +3}` omit exact zero, while ternary `{-1, 0, +1}` leaves one of four 2-bit states unused. The bijective asymmetric `{-2, -1, 0, +1}` codebook with signed-scale polarity flip restores all 4 states and exact zero at zero extra bit-plane cost.
- **Wallace / Dadda 3:2 CSA vs 4:2 Compressors (Weinberger, 1981; Oklobdzija et al., 1996) & NVIDIA PTX `lop3.b32`:** In 2-input CMOS logic, 4:2 compressors (3 XOR delays for 2:1 reduction) are preferred over 3:2 CSAs (2 XOR delays for 3:2 reduction) for regular tree routing. Under 3-input `LOP3` primitives, 3:2 CSA collapses to depth $1$ (`XOR3` + `MAJ3`), whereas 4:2's 5-input parity remains depth $\ge 2$, reversing the depth-efficiency ordering.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build timings and `#print axioms` output, and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest.
