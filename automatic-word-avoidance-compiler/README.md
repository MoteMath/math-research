# Automatic-Word Pattern-Avoidance & Carry-Offset Overlap-Graph Certificate Engine (`automatic-word-avoidance-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): four-layer pure-data DFAO carry-offset compiler, LSB-indexed BTree overlap-graph invariant engine, bitmask parity-synchronization k-power compiler, and parity-conditioned overlap compiler in pure Lean 4 Init, discharging sharp unbounded avoidance and abelian balance theorems for five carry-bitwise/Gray automatic words.*

## For Mathematicians

We introduce a four-layer pure-data certificate compiler (`SiliconAvoidance`) in standalone Lean 4 `Init` that bridges raw `Nat` bitwise/carry arithmetic (`*`, `^^^`, `&&&`, `/ 2`, `popcount`) directly to universally quantified unbounded pattern-avoidance theorems ($\forall n, p \in \mathbb{N},\; p \ge 1$) inside the Lean kernel (zero `native_decide`, zero external Walnut/Büchi solvers):

1. **Layer 0 — Carry-Offset Vector Compiler:** Finite state-vector tables checked by `decide` compile $\mathrm{carryXor}(K, n) = \mathrm{popcount}((Kn) \oplus n) \bmod 2$, $\mathrm{carryAnd}(K, n) = \mathrm{popcount}((Kn) \mathbin{\&} n) \bmod 2$, and $\mathrm{grayMod4}(n) = \mathrm{popcount}(n \oplus \lfloor n/2 \rfloor) \bmod 4$ directly to minimal MSB-first DFAOs.
2. **Layer 1 — LSB-Indexed `BTree` Overlap-Graph Engine (`windowCert_sound`):** Certifies window invariants (forbidden factors, abelian/Hamming-weight balance bounds, and finite base-period exclusions) in $O(\log N)$ kernel lookup time.
3. **Layer 2 — Bitmask Parity-Synchronization & Even-Halving $k$-Power Compiler (`powerAvoidCert_sound`):** Combines a parity-tagged synchronization graph `SyncCert`, an even-index decoder `invEven`, and finite base-period certificates to descend every period $p \ge p _ {\mathrm{sync}}$ to $p/2$ by strong induction.
4. **Layer 3 — Parity-Conditioned Both-Bit Halving Overlap Compiler (`overlapAvoidCert_sound`):** Handles words where unconditional single-bit halving fails (such as `grayMod4`), proving full overlap-freeness.

The compiler discharges sharp unbounded theorems for five distinct pure-silicon sequences: `carryXor 3` is 4-power-free (sharp: has cube `000`), `carryAnd 3` is 5-power-free (sharp: has 4th power `1111`), `carryAnd 5` is 4-power-free (sharp: has $(7/2)$-power), `carryXor 5` is 6-power-free (sharp: avoids 4-runs at $p=1$ yet attains a 5th power `(010)^5` at $p=3$!), and `grayMod4` is overlap-free (sharp: has square `1212`), plus sharp abelian window balance bounds.

## For Non-Mathematicians

Write down an infinite sequence of $0$s and $1$s by taking each whole number $n$, multiplying by $3$ or $5$, XORing or ANDing with $n$, and checking whether the result has an even or odd number of $1$-bits. Can the same block of digits repeat $4$, $5$, or $6$ times in a row anywhere in this infinite sequence — even a billion digits out? We built a self-verifying Lean 4 compiler that compiles these binary arithmetic formulas directly into finite automata, verifies a compact overlap-graph and parity-synchronization certificate inside the kernel, and proves exact, sharp repetition limits for five different carry-bitwise and Gray-code sequences — including one (`carryXor 5`) that never has four identical digits in a row, yet secretly contains a 5-fold repetition of a 3-digit block at position $153$, and never a 6-fold repetition anywhere!

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of **`SiliconAvoidance`**, a four-layer carry-offset DFAO and synchronized overlap-graph certificate compiler discharging sharp unbounded power-avoidance, overlap-freeness, and abelian balance theorems.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `windowCert_sound` | Layer-1 soundness: an LSB-indexed `BTree` overlap-graph certificate `WindowCert` certifies $\forall n \in \mathbb{N},\; \mathrm{ok}(\mathrm{outputWindow}\; M\; W\; n) = \mathrm{true}$. |
| `powerAvoidCert_sound` | Layer-2 soundness: a `PowerAvoidCert` (sync graph + even-halving decoder + base periods) certifies $k$-power-freeness $\forall n, p \ge 1$. |
| `overlapAvoidCert_sound` | Layer-3 soundness: an `OverlapAvoidCert` (parity-conditioned both-bit halving) certifies full overlap-freeness $\forall n, p \ge 1$. |
| `carryXor3_four_power_free` | For all $n \in \mathbb{N}$ and $p \ge 1$, $\mathrm{carryXor}(3, \cdot)$ avoids all 4th powers (sharp: attains cube `000` at $n=5, p=1$). |
| `carryAnd3_five_power_free` | For all $n \in \mathbb{N}$ and $p \ge 1$, $\mathrm{carryAnd}(3, \cdot)$ avoids all 5th powers (sharp: attains 4th power `1111` at $n=1, p=1$). |
| `carryAnd5_four_power_free` | For all $n \in \mathbb{N}$ and $p \ge 1$, $\mathrm{carryAnd}(5, \cdot)$ avoids all 4th powers (sharp: attains $(7/2)$-power at $n=37, p=2$). |
| `carryXor5_six_power_free` | For all $n \in \mathbb{N}$ and $p \ge 1$, $\mathrm{carryXor}(5, \cdot)$ avoids all 6th powers (sharp: avoids 4-runs at $p=1$ yet attains 5th power `(010)^5` at $n=153, p=3$). |
| `grayMod4_overlap_free` | For all $n \in \mathbb{N}$ and $p \ge 1$, $\mathrm{grayMod4}(n) = \mathrm{popcount}(n \oplus \lfloor n/2 \rfloor) \bmod 4$ is overlap-free (sharp: attains square `1212`). |

## Proof Architecture

1. **Carry-Offset Vector DFAO Compiler (`carryXorModel_sound`, `carryAndModel_sound`):** Compiles raw `Nat` bitwise-carry formulas into minimal MSB-first DFAOs via kernel-checked state-vector closure tables.

2. **LSB-Indexed `BTree` Overlap-Graph Engine (`windowCert_sound`):** Stores closed $W$-window invariant graphs in a pure-data binary tree for $O(\log N)$ lookup inside kernel `decide`.

3. **Synchronization & Parity-Conditioned Halving (`powerAvoidCert_sound`, `overlapAvoidCert_sound`):** Strong induction on period $p$ uses bitmask parity synchronization to force $p = 2p'$ and descends to a strictly smaller witness at $p' < p$.

4. **Sharpness & 11 Kernel Hostile Mutations:** Every avoidance theorem is paired with a kernel-checked sharpness witness attaining the next lower exponent, plus 11 `= false := by decide` hostile certificate rejections across all four layers.

## Prior-Art Context

- **Classical combinatorics on words & Walnut:** Thue (1906) proved overlap-freeness of Thue–Morse, Allouche–Shallit / Rampersad analyzed Rudin–Shapiro, and Walnut (Mousavi 2016; Shallit 2022) decides automatic-sequence properties via external unverified Büchi automata.
- **Contribution (prior-art status not established):** A kernel-checked Lean 4 certificate compiler from raw `Nat` bitwise-carry arithmetic through DFAO compilation to universal $k$-power and overlap avoidance, discharging avoidance theorems (with finite sharpness witnesses) for five distinct carry-bitwise and Gray automatic words (`carryXor 3/5`, `carryAnd 3/5`, `grayMod4`).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build logs and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. `scripts/explore_and_verify.py` replays the finite certificates and sharpness counterexamples in exact integer arithmetic (zero floats).
