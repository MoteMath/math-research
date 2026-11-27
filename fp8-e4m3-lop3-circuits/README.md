# OCP `FP8-E4M3FN` SFU-Free & `E4M3 × E2M1` Zero-FP `LOP3` Circuits (`fp8-e4m3-lop3-circuits`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **8 / 10** | **9 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (`3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 89 / 100`): pure Lean 4 `Init` (zero Mathlib) formalization of GPU-synthesized `LOP3` bit-sliced circuits that agree with the reference tables on every code of their domains and universal fan-in lower bounds on OCP `FP8-E4M3FN` and `FP4-E2M1`: a 15-`LOP3` positive `rsqrt` circuit certified directly against the exact pure-integer RNE Voronoi optimality law for $1/\sqrt{x}$, a 33-`LOP3` full-domain `rsqrt` circuit, exact 0-ULP circuits for `exp` (67 `LOP3`), `gelu` (82 `LOP3`, tight 1-`LOP3` $y _ 6$), and `silu` (93 `LOP3`, tight 0-`LOP3` $y _ 7$), a 28-`LOP3` zero-FP `FP8-E4M3FN × FP4-E2M1` exact aligned product verified over all $4{,}096$ input pairs, universal `LOP3` DAG gate-count and depth lower bounds ($k \le 2g + 1$ and $k \le 3^d$), and the exact OCP `FP8-E4M3FN` dyadic value law.*

**Scope of the formal statement.** Theorems 1-4 and 6 are finite, exhaustive checks over 8-bit or 12-bit input domains (126, 254, 256 or 4,096 inputs); only Theorem 5 (the fan-in and depth lower bounds) quantifies over all circuits. The `rsqrt` circuits are judged against an independent pure-integer Voronoi test; the `exp`, `gelu` and `silu` circuits are judged against reference tables that are embedded in the Lean files and were generated outside Lean (the README text below mentions 60-digit `mpmath`), so for those three the statement is agreement with that table, not a derivation of the function.

## For Mathematicians

Let $\mathrm{e4m3ScaledVal} : \mathrm{BitVec}\;8 \to \mathbb{Z}$ denote the exact scaled OCP `FP8-E4M3FN` decoding $512 \cdot \mathrm{val}(x) \in [-229{,}376, 229{,}376]$ (with min subnormal $2^{-9} = 1/512$, max finite normal $\pm 448 = \pm 229{,}376 / 512$, and NaN codes `0x7F`, `0xFF`), let $\mathrm{e2m1TwiceVal} : \mathrm{BitVec}\;4 \to \mathbb{Z}$ denote $2 \cdot \mathrm{val}(b) \in [-12, 12]$ for OCP `FP4-E2M1`, and let $\mathrm{lop3}(\mathrm{imm8}, a, b, c)$ denote the 3-input Boolean lookup gate (PTX `lop3.b32`).

1. **Exact 15-`LOP3` Positive `rsqrt` & Algebraic RNE Voronoi Certification (Theorem 1):**
   For every positive finite `FP8-E4M3FN` code $x \in [1, 126]$ with $\mathrm{val}(x) = v _ x / 512$, the round-to-nearest-even (RNE) rounding $y = \mathrm{RNE}(1 / \sqrt{\mathrm{val}(x)})$ is characterized without any transcendental axioms by the pure-integer Voronoi inequality:
   ```math
   (\mathrm{val}(y - 1) + \mathrm{val}(y))^2 \cdot \mathrm{val}(x) \le 4 \le (\mathrm{val}(y) + \mathrm{val}(y + 1))^2 \cdot \mathrm{val}(x)
   ```
   (strict when $y$ is odd, and upper-unbounded at saturation $y = 126$), which clears denominators to $l _ y^2 \cdot v _ x \le 536{,}870{,}912 \le u _ y^2 \cdot v _ x$ in $\mathbb{N}$. We prove that the 15-`LOP3`, depth-8 DAG `e4m3RsqrtPosDag` (`0.469` `LOP3`/elem at 32-wide bit-sliced) satisfies this exact algebraic RNE law on all $126 / 126$ positive finite inputs with $y _ 7 = 0$ (0 gates).
2. **Exact 33-`LOP3` Full-Domain `rsqrt` (Theorem 2):**
   The 33-`LOP3`, depth-14 DAG `e4m3RsqrtFullDag` agrees identically with `e4m3RsqrtPosDag` (and the exact algebraic RNE law) on all $126$ positive finite codes and outputs canonical NaN `0x7F` on all $130$ non-positive and NaN codes (`0x00`, `0x7F`, `0x80..0xFF`).
3. **Exact 0-ULP `exp`, `gelu`, and `silu` `LOP3` DAGs (Theorem 3):**
   Across all $254$ finite `FP8-E4M3FN` codes, we verify 0-ULP equivalence against 60-digit `mpmath` RNE ground truth for `e4m3ExpDag` (67 `LOP3`, depth 9), `e4m3GeluDag` (82 `LOP3`, depth 15), and `e4m3SiluDag` (93 `LOP3`, depth 16). We also certify two tight single-bit structural laws: for `gelu`, output bit $y _ 6 = (\neg x _ 7) \land x _ 6 = \mathrm{lop3}(\mathrm{0x04}, x _ 7, x _ 6, x _ 7)$ (1 gate, tight); for `silu`, sign bit $y _ 7 = x _ 7$ identically (0 gates, tight).
4. **Exact 28-`LOP3` Zero-FP `FP8-E4M3FN × FP4-E2M1` Aligned Product (Theorem 4):**
   Combining $1$ `LOP3` sign XOR (`0x3C`), $3$ `LOP3` implicit-bit flags (`0xFE`, `0xFC`, `0xFC`), a 14-`LOP3` exact $4\text{-bit} \times 2\text{-bit}$ significand product $P = s _ a \cdot s _ b \in [0, 45]$, and a 10-`LOP3` exact 5-bit aligned exponent sum $E _ {\mathrm{sum}} = \max(e _ a, 1) + \max(e _ b, 1) - 1 \in [1, 17]$ yields a 28-`LOP3` (`0.875` `LOP3`/elem at 32-wide) zero-FP product circuit satisfying the exact integer dyadic identity
   ```math
   (-1)^{\mathrm{sign}} \cdot P \cdot 2^{E _ {\mathrm{sum}} - 1} = \mathrm{e4m3ScaledVal}(a) \cdot \mathrm{e2m1TwiceVal}(b)
   ```
   for all $256 \times 16 = 4{,}096$ input pairs $(a, b) \in \mathrm{BitVec}\;8 \times \mathrm{BitVec}\;4$.
5. **Universal `LOP3` DAG Fan-In & Depth Lower Bounds (Theorem 5):**
   For *any* $n$-input single-output `LOP3` DAG $d$ (with arbitrary gate sharing and fan-out) and *any* care domain $P : \mathrm{BitVec}\;n \to \mathrm{Bool}$, backward frontier expansion and forward support-size induction prove
   ```math
   k \le 2 g + 1 \qquad \text{and} \qquad k \le 3^D,
   ```
   where $k = \mathrm{essentialVarCountOn}(P, d.\mathrm{eval})$, $g = d.\mathrm{gates.length}$, and $D = d.\mathrm{depth}$. Instantiating on `FP8-E4M3FN` certifies the exact essential-variable profiles `[7, 7, 7, 7, 6, 7, 7, 0]` for `rsqrt_pos` ($\ge 3$ `LOP3` and depth $\ge 2$ on every active bit), `[8, 8, 8, 8, 7, 8, 8, 0]` for `rsqrt_full` ($\ge 4$ `LOP3` on 6 bits), $k = 2$ for `gelu` $y _ 6$ ($\ge 1$ `LOP3`, tight), and $k = 1$ for `silu` $y _ 7$ (0 `LOP3`, tight).
6. **Universal OCP `FP8-E4M3FN` Dyadic Value Law (Theorem 6):**
   Certifies max normal $448$ (`0x7E`), min positive subnormal $2^{-9}$ (`0x01`), exact sign symmetry $\mathrm{val}(x \oplus \mathrm{0x80}) = -\mathrm{val}(x)$, strict order-preserving monotonicity on `0x01..0x7E`, exact signed-zero characterization (`0x00`, `0x80`), and exact code partition $126 + 126 + 2 + 2 = 256$.

## For Non-Mathematicians

Modern AI accelerators run low-precision 8-bit (`FP8-E4M3FN`) and 4-bit (`FP4-E2M1`) math, but computing nonlinear functions like `rsqrt`, `exp`, `gelu`, and `silu` normally requires converting to 32-bit floating point (`FP32`), waiting on bottlenecked Special Function Units (SFUs), and converting back. By packing 32 FP8 numbers into bit-sliced 32-bit integer registers and using 3-input GPU logic instructions (`LOP3`), each of these functions is computed by a circuit with **no floating-point operations and no lookup tables**, and agrees with the reference table on every code of its domain (0-ULP). This repository machine-checks six statements about these circuits in Lean 4's kernel with zero external libraries; it makes no speed claim.

## Circuit sizes

| Function | Care Domain | `LOP3` | Depth | `LOP3` / elem (32-wide) | Lean 4 Kernel Status |
| :--- | ---: | ---: | ---: | ---: | :--- |
| `e4m3_rsqrt_pos` | `126` (`0x01..0x7E`) | 15 | 8 | 0.469 | Proved (exact integer RNE Voronoi law) |
| `e4m3_rsqrt_full` | `256` (all codes) | 33 | 14 | 1.031 | Proved (Voronoi law + NaN) |
| `e4m3_exp` | `254` (finite) | 67 | 9 | 2.094 | Proved (exhaustive against the reference table) |
| `e4m3_gelu` | `254` (finite) | 82 | 15 | 2.563 | Proved (exhaustive against the reference table + tight $y _ 6$) |
| `e4m3_silu` | `254` (finite) | 93 | 16 | 2.906 | Proved (exhaustive against the reference table + tight $y _ 7$) |
| `E4M3 × E2M1` aligned | `4,096` pairs | 28 | 8 | 0.875 | Proved (exact integer law) |

Throughput and speedup figures against a hardware special-function unit that were quoted in earlier versions of this README (for example "2.95x" for `e4m3_rsqrt_pos`) were measurements made outside this repository; nothing here reproduces or backs them, so they were removed. The theorems below are about the circuits' input-output behaviour, not about speed.
---

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `fp8_e4m3_rsqrt_15_lop3_exact` | 15-`LOP3` (depth 8) `e4m3RsqrtPosDag` satisfies the exact pure-integer RNE Voronoi law for $1/\sqrt{\mathrm{val}(x)}$ on all $126$ positive finite codes with $y _ 7 = 0$. |
| `fp8_e4m3_rsqrt_full_33_lop3_exact` | 33-`LOP3` (depth 14) `e4m3RsqrtFullDag` matches `e4m3RsqrtPosDag` (and the exact RNE law) on all $126$ positive finite codes and returns `0x7F` on all $130$ remaining codes. |
| `fp8_e4m3_activations_lop3_exact` | 0-ULP exactness over all $254$ finite codes for `exp` (67 `LOP3`, depth 9), `gelu` (82 `LOP3`, depth 15, tight 1-`LOP3` $y _ 6$), and `silu` (93 `LOP3`, depth 16, tight 0-`LOP3` $y _ 7$). |
| `fp8_e4m3_times_e2m1_28_lop3_exact` | 28-`LOP3` zero-FP `E4M3 × E2M1` aligned product (`1 + 3 + 14 + 10`) satisfies the exact integer product law over all $4{,}096$ pairs `(a, b) : BitVec 8 × BitVec 4`. |
| `fp8_e4m3_lop3_fanin_lower_bound` | Universal `LOP3` DAG lower bounds $k \le 2g + 1$ and $k \le 3^D$ for any `SingleOutLop3Dag n`, instantiated on the exact OCP `FP8-E4M3FN` essential-variable profiles. |
| `fp8_e4m3_exact_dyadic_value_law` | Universal OCP `FP8-E4M3FN` dyadic characterization: max normal $448$, min subnormal $2^{-9}$, sign symmetry, strict monotonicity on `0x01..0x7E`, signed zeros, and $126+126+2+2=256$. |

## Prior-Art Context

- **OCP FP8 (`E4M3FN`) & Microscaling Formats (`MXFP4` / `E2M1`, Micikevicius et al., 2022; Rouhani et al., 2023):** Standardizes 8-bit (`E4M3FN`, no infinities, max finite `±448`) and 4-bit (`E2M1`) inference/training formats; hardware transcendental units remain FP32-SFU bound.
- **Bit-Sliced `LOP3` Synthesis (PTX `lop3.b32`, the `sparse24-e2m1-lop3` package):** Extends bit-sliced `LOP3` DAG synthesis from sub-byte unpackers to full 8-bit transcendental operators (`rsqrt`, `exp`, `gelu`, `silu`) and mixed-precision `E4M3 × E2M1` multiplication with machine-checked 0-ULP correctness and universal DAG fan-in bounds.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build timings and `#print axioms` output, and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest.
