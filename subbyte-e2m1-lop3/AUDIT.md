# Formal Verification Audit (`subbyte-e2m1-lop3`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib, zero external dependencies)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **8 / 10** | **9 / 10** | **10 / 10** | **89 / 100** |

Weighted formula: `3 * 9 + 2 * 9 + 2 * 8 + 2 * 9 + 1 * 10 = 89 / 100`.

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built SubbyteE2M1Lop3.Defs (1.3s)
✔ [3/7] Built SubbyteE2M1Lop3.Theorems (2.7s)
✔ [4/7] Built SubbyteE2M1Lop3 (1.1s)
✔ [6/7] Built Solution (1.3s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:70:8: declaration uses `sorry`
warning: Challenge.lean:88:8: declaration uses `sorry`
warning: Challenge.lean:103:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry` / `admit` / `axiom` / `native_decide` anywhere in `SubbyteE2M1Lop3/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SubbyteE2M1Lop3Challenge.unpack_2t4b_to_e2m1_zero_lop3' depends on axioms: [propext]
'SubbyteE2M1Lop3Challenge.unpack_3t5b_to_e2m1_four_lop3' depends on axioms: [propext]
'SubbyteE2M1Lop3Challenge.unpack_3t5b_to_e2m1_three_gate_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SubbyteE2M1Lop3Challenge.quinary_3w7b_five_var_impossibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SubbyteE2M1Lop3Challenge.asymmetric_2bit_polarity_flip_exact' depends on axioms: [propext, Quot.sound]
'SubbyteE2M1Lop3Challenge.compressor_4to2_lop3_depth_inversion' depends on axioms: [propext, Quot.sound]
```

Four of the six headline theorems (`unpack_2t4b_to_e2m1_zero_lop3`, `unpack_3t5b_to_e2m1_four_lop3`, `asymmetric_2bit_polarity_flip_exact`, `compressor_4to2_lop3_depth_inversion`) are completely constructive (zero `Classical.choice`), and all six depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` (`"enable_nanoda": true`, zero `Lean.ofReduceBool`).

## For Mathematicians

All six theorems are proved directly over Lean 4's `Init` (`BitVec`, `UInt8`, `Fin`, `Int`, `List`) with no external libraries:
- Finite circuit verifications (`unpack_2t4b_to_e2m1_zero_lop3`, `unpack_3t5b_to_e2m1_four_lop3`, and the 3:2 CSA part of `compressor_4to2_lop3_depth_inversion`) reduce in the kernel via `decide` (zero `native_decide`).
- Both information-theoretic lower bounds (`unpack_3t5b_to_e2m1_three_gate_lower_bound` on $\mathrm{BitVec}\;5$ and `quinary_3w7b_five_var_impossibility` on $\mathrm{BitVec}\;7$) share a single unified `flipBit` involution lemma (`weight_mod_eight_of_three_flip_inv`) and `Nodup` list-filter pigeonhole lemma (`length_le_of_nodup_subset`), proving $8 \mid w(g)$ for any function invariant under $3$ distinct bit flips.
- The 2-bit asymmetric dot-product identity is proved universally over all `List (Bool × Bool × Int)` by structural induction (`asym2_foldl_aux`), and the 4:2 compressor impossibility is proved without enumerating `UInt8` by exhibiting a missing coordinate $m \in \mathrm{Fin}\;5 \setminus \{i, j, k\}$ whose single-bit toggle flips `sum4to2` while leaving `lop3 imm (v i) (v j) (v k)` invariant.

## For Non-Mathematicians

Every single claim in this repository — from the 0-gate and 4-gate ternary-to-FP4 unpackers, to the mathematical impossibility proofs for smaller ternary and quinary circuits, to the exact 2-bit asymmetric dot-product formula and the GPU 3:2 vs 4:2 adder depth reversal — has been machine-checked line by line by the Lean 4 proof kernel in under 7 seconds total, with zero gaps (`sorry`), zero trust shortcuts (`native_decide`), and zero external dependencies.

## Prior-Art Context

- **OCP MXFP4 (E2M1) & BitNet b1.58 (Rouhani et al., 2023; Ma et al., 2024):** Establishes E2M1 hardware decoding and 1.58-bit ternary weights; this package formally verifies the minimal-`LOP3` direct unpackers (`I093`) and general lower bounds.
- **2-Bit Asymmetric Quantization & Quinary Packing (`I091`, `I100`):** Formalizes the $\ge 5$-variable support barrier for 3-quinary/7-bit decoders and the exact 2-plane dot-product / free polarity-flip duality of `{-2, -1, 0, +1}`.
- **Carry-Save Adders vs 4:2 Compressors under PTX `lop3.b32` (`I098`):** Formally establishes the depth-1 vs depth-$\ge 2$ reversal between 3:2 CSAs and 4:2 compressors on 3-input lookup hardware.
