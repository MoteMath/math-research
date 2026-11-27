# Hybrid Carry-AND NLFSR Holonomy & De Bruijn Engine (`nlfsr-holonomy-lasso-debruijn`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a finite-to-infinite $\mathbb{F} _ 2$ carry-transducer eigencycle compiler (`CarryTransducer` + `LassoCert`) and return-map carry-barrier engine for hybrid carry-AND NLFSRs, proving exact 2-cycle splitting of `H111`, De Bruijn completeness of `K_map` and `H121`, universal coexistence of exponential carry-pump giant cycles and hermetic logarithmic carry-barrier sectors across all 2-delayed nonlinear feedbacks, and non-prefix De Bruijn completeness with sharp prefix-tap cycle splitting, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

For causal bit-sliced invertible maps $f$ with bit-$w$ toggle $\delta _ w(x \bmod 2^w)$, the orbit holonomy parity $H _ w$ governs an exact width-lifting dichotomy: odd holonomy doubles the minimal period ($L \to 2L$), while even holonomy splits the cycle into two disjoint cycles of length $L$. Three mechanisms lift finite checks to all widths $w \to \infty$:

1. **$\mathbb{F} _ 2$ Carry-Transducer Eigencycle Compiler (`transducer_cert_period_doubling`):** When carries couple nonlinear AND/OR terms across all bit positions (defeating XOR-ANF degree bounds), a finite $S$-state carry transducer $T$ tracks $\delta _ w$, and cylinder state-parity masks evolve linearly in $\mathbb{F} _ 2^S$ into a finite lasso checked by `decide`. This certifies exact 2-cycle splitting of $H _ {1,1,1}(x) = x + 2(x \mathbin{\&} (x \ll 1)) + 1$ into two disjoint $2^{w-1}$-cycles for all $w \ge 3$ (via a period-3 eigencycle), and universal De Bruijn completeness of $K(x) = (x \oplus (x \ll 1)) + 2(x \mathbin{|} (x \ll 1)) + 1$ and $H _ {1,2,1}(x) = x + 2(x \mathbin{\&} (x \ll 2)) + 1$ for all $w \ge 1$.
2. **Universal Carry-Barrier & Frobenius Carry-Pump Bifurcation:** For $F _ {N, c}(x) = (x \oplus (x \ll 1) \oplus N(x)) + c$ with **any** 2-delayed nonlinear feedback $N$ satisfying $\mathrm{bit} _ 2(N(0)) = \mathrm{bit} _ 2(N(1))$ and $c \equiv 1 \pmod 4$, every state with $\mathrm{bit} _ 1(x) = 0$ lies on a single exponential giant cycle of exact length $2^{w-1}$ for all $w \ge 2$. Simultaneously, at $c = 1$, every state with $\mathrm{bit} _ 1(x) = 1$ stays trapped behind a **hermetic carry barrier** (zero carries cross bit 1), and for $F _ 0(x) = (x \oplus (x \ll 1)) + 1$ every state in that sector has exact logarithmic period $2^{\lceil \log _ 2(w - 1) \rceil}$ for all $w \ge 3$.
3. **Non-Prefix De Bruijn Completeness & Prefix-Tap Sharpness:** Any finite collection $M$ of non-prefix multi-way shift-AND taps gives a single De Bruijn cycle of length $2^w$ for all $w \ge 1$ and every odd $c$, whereas the contiguous prefix tap $\{1, \dots, d\}$ is De Bruijn up to $w = d$ and undergoes exact 2-way cycle splitting into two $2^d$-cycles at $w = d + 1$.

## For Non-Mathematicians

Feedback shift registers with nonlinear logic and binary addition are widely used to generate long pseudo-random bit sequences, ideally visiting every w-bit state in one giant "De Bruijn" cycle. When binary addition carries interact with nonlinear AND/OR gates, standard polynomial tests break down. This package builds a finite-state carry-transducer compiler: a small finite lasso check, verified once by the proof assistant, proves exact cycle lengths for every bit width forever. It certifies that one classic hybrid register splits cleanly into two equal half-space cycles at every width from 3 bits up while two close cousins form a single full cycle at every width. Even more strikingly, for a whole infinite family of two-gate nonlinear registers, the state space splits down the middle into two coexisting worlds: one half pumps carries into an exponentially long cycle of length 2^(w-1), while the other half erects an airtight carry barrier where every cycle has tiny logarithmic length.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of an $\mathbb{F} _ 2$ carry-transducer eigencycle compiler, hermetic carry-barrier coexistence, and non-prefix De Bruijn completeness for hybrid carry-AND NLFSRs.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `transducer_cert_period_doubling` | End-to-end engine: a finite `decide`-checked `LassoCert` for a valid `CarryTransducer` lifts base period $L _ 0$ at width $w _ 0$ to exact period $L _ 0 \cdot 2^d$ at width $w _ 0 + d$ for all $d$. |
| `theorem1_H111_exact_two_cycles` | For every $w \ge 3$, $H _ {1,1,1}(x) = x + 2(x \mathbin{\&} (x \ll 1)) + 1$ partitions mod $2^w$ into two disjoint cycles of exact minimal period $2^{w-1}$ separated by bit $2$. |
| `theorem1b_H121_debruijn` | For every $w \ge 1$, $H _ {1,2,1}(x) = x + 2(x \mathbin{\&} (x \ll 2)) + 1$ is De Bruijn complete (single cycle of length $2^w$). |
| `theorem2a_carry_pump_universal_giant_cycle` | For any 2-delayed nonlinear feedback $N$ with $\mathrm{bit} _ 2(N(0)) = \mathrm{bit} _ 2(N(1))$ and $c \equiv 1 \pmod 4$, every state with $\mathrm{bit} _ 1(x) = 0$ has exact period $2^{w-1}$ for all $w \ge 2$. |
| `theorem2b_carry_barrier_hermetic` | For any 2-delayed $N$ and every $x$ with $\mathrm{bit} _ 1(x) = 1$, bit 1 stays $1$ and zero carries propagate past bit 1 under `hybridCarryNLFSR N 1`. |
| `theorem2c_linear_carry_barrier_exact_log_period` | For every $w \ge 3$ and $k = \lceil \log _ 2(w - 1) \rceil$, every state with $\mathrm{bit} _ 1(x) = 1$ has exact minimal period $2^k$ under $F _ 0(x) = (x \oplus (x \ll 1)) + 1$. |
| `theorem3a_nonprefix_hybrid_nlfsr_debruijn` | For every finite list $M$ of non-prefix multi-way shift-AND taps, every odd $c$, and every $w \ge 1$, `hybridTapNLFSR M c` is De Bruijn complete. |
| `theorem3b_prefix_tap_exact_cycle_splitting` | For every $d \ge 1$ and odd $c$, the contiguous prefix tap $\{1, \dots, d\}$ is De Bruijn complete for $1 \le w \le d$ and splits into two disjoint $2^d$-cycles at $w = d + 1$. |

## Proof Architecture

1. **Slice Holonomy & Carry-Transducer Compiler (`transducer_cert_period_doubling`):** bit-sliced holonomy parity lifts exact periods by doubling; tracking bit-toggles with a finite `CarryTransducer` reduces all-width holonomy to a finite $\mathbb{F} _ 2^S$ lasso verified by `decide`.
2. **Return-Map & Carry-Barrier Engine (`theorem2a`–`theorem2c`):** 2-step return-map reduction, characteristic-2 Frobenius cancellation, any-bit-blind pairing involution, and carry-parity conservation prove the universal $2^{w-1}$ giant cycle on $\mathrm{bit} _ 1 = 0$, while bit-1 invariance blocks all carries on $\mathrm{bit} _ 1 = 1$ and yields exact logarithmic period $2^{\lceil \log _ 2(w-1) \rceil}$ for $F _ 0$.
3. **Non-Prefix Tap Classification (`theorem3a`, `theorem3b`):** per-tap any-bit-blind pairing proves De Bruijn completeness for arbitrary non-prefix multi-way AND taps, paired with exact 2-way cycle splitting at $w = d + 1$ for every prefix tap $P _ d$.

## Prior-Art Context

- **T-functions & NLFSRs:** Anashin (1994, 2002) and Klimov & Shamir (CHES 2002, FSE 2004) characterize single-cycle triangular maps via ANF degree bounds; Golomb (*Shift Register Sequences*) studies De Bruijn NLFSRs. Theorem 3a sits in that classical lineage (proved via any-bit-blind pairing without polynomials or Möbius inversion) and is paired with the exact cycle-splitting sharpness family Theorem 3b.
- **Verdict status:** Referee-2 `PASS` (swarm board #164); the referee-6 novelty audit was still pending when this package was cut, so the novelty summary ($\mathbb{F} _ 2$ carry-transducer eigencycle compiler for additive Carry-AND NLFSRs and universal exponential/logarithmic carry-barrier coexistence) is the packager's conservative reading.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib). See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts, [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest, and `scripts/explore_and_verify.py` for the exact-integer exploration and verification script (zero floating point).
