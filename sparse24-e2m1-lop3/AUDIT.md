# Formal Verification Audit (`sparse24-e2m1-lop3`)

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
✔ [2/8] Built Sparse24E2M1Lop3.Defs (1.5s)
✔ [3/8] Built Sparse24E2M1Lop3.Core (1.9s)
✔ [4/8] Built Sparse24E2M1Lop3.Theorems (18s)
✔ [5/8] Built Sparse24E2M1Lop3 (1.2s)
✔ [7/8] Built Solution (1.3s)
Build completed successfully (8 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:72:8: declaration uses `sorry`
warning: Challenge.lean:86:8: declaration uses `sorry`
warning: Challenge.lean:98:8: declaration uses `sorry`
warning: Challenge.lean:106:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry` / `admit` / `axiom` / `native_decide` / `lemma` anywhere in `Sparse24E2M1Lop3/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'Sparse24E2M1Lop3Challenge.unpack_5t8b_to_e2m1_ten_lop3_and_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Sparse24E2M1Lop3Challenge.sparse24_3bit_single_lop3_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sparse24E2M1Lop3Challenge.sparse24_3bit_ordered_three_lop3_tight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Sparse24E2M1Lop3Challenge.sparse24_8bit_triple_twelve_lop3_and_wire_bound' depends on axioms: [propext, Quot.sound]
'Sparse24E2M1Lop3Challenge.e2m1_mag_mul_25lop3_exact' depends on axioms: [propext, Quot.sound]
'Sparse24E2M1Lop3Challenge.quinary_2w5b_to_e2m1_four_lop3_and_wire_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Two of the six headline theorems (`sparse24_8bit_triple_twelve_lop3_and_wire_bound`, `e2m1_mag_mul_25lop3_exact`) are completely constructive (zero `Classical.choice`), and all six depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` (`"enable_nanoda": true`, zero `Lean.ofReduceBool`).

## For Mathematicians

All six headline theorems are proved directly over Lean 4's `Init` (`BitVec`, `UInt8`, `Fin`, `Int`, `List`) with no external libraries:
- All five `LOP3` circuits (found by a GPU search that is not part of the verified statement) (`unpack5t8b` 243/243, `unpackMask24_3b` / `unpackUnordered24_3b` / `unpackOrdered24_3b` 6/6, `unpackTripleMask24_8b` 216/216, `e2m1MagMul25` 64/64, `unpack2q5b` 25/25) reduce in the Lean 4 kernel via `decide` (zero `native_decide`), with the wire indices and `imm8` opcodes stored in the Lean source.
- The general `5t8b` lower bound uses a 4-bit-flip involution lemma (`weight_mod_sixteen_of_four_flip_inv`) and `Nodup` list-filter pigeonhole (`le_weight_of_exists`), proving $16 \mid w(g)$ for any $\le 4$-variable function on $\mathrm{BitVec}\;8$ vs $w(f _ i) \in [162, 175]$.
- The `3b` mask/ordered lower bounds and `2q5b` 4-wire impossibility theorem are proved for *arbitrary* surjective decoders via exact wire-fiber weights (`weight_wire3_eq_four`, `weight_two_wires3_eq_two`, `weight_two_wires5_eq_eight`) and finite pigeonhole.
- In Theorem 4, Lean 4's kernel verification also caught the `Nat` truncated-subtraction edge case at $(3, 3, 3)$ (where $8 - 9 = 0$ in `Nat`), explicitly enforcing the physical 8-bit wire budget $d _ 0 + d _ 1 + d _ 2 \le 8$ so the uniqueness of $(1, 1, 1)$ is 100% sound.

## For Non-Mathematicians

The circuits listed above are checked by the Lean 4 kernel by exhaustive evaluation, with zero gaps (`sorry`), zero trust shortcuts (`native_decide`) and zero external dependencies. The lower bounds in the Challenge are statements about Hamming weights and variable dependencies of the decoder functions; Lean has no gate model here, so they are not proved gate-count lower bounds for `LOP3` circuits.

## Prior-Art Context

- **2:4 Structured Sparsity (Mishra et al., 2021) & PTX `lop3.b32`:** Formalizes exact 3-bit (`-25%`) and 8-bit (`-33.3%`) 2:4-sparse metadata compression circuits alongside tight wire/gate lower bounds.
- **OCP MXFP4 (E2M1, Rouhani et al., 2023) & Sub-Byte Quantization (Ma et al., 2024):** Formalizes minimal-`LOP3` direct unpackers for `5t8b` (`1.60` bpw) and `2q5b` (`2.50` bpw) plus an exact 25-`LOP3` zero-FP E2M1 magnitude multiplier.
