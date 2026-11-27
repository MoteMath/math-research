# Carry-Run Cyclotomic Transfer & Ripple-Depth Annihilators (`carry-run-cyclotomic-transfer`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): unrecorded silicon duality between carry-run output-parity cyclotomic period-(L+2) collapse and ripple-depth input-parity monomial period-(L+1) collapse, universal determinant-free (L+1)x(L+1) matrix annihilators, and the bivariate carry-absorption odd/even dichotomy, formalized in pure Lean 4 Init (zero Mathlib).*

## For Mathematicians

We introduce `CarryTransferEngine`, a pure-Init Lean 4 framework that lifts finite radix-$B$ carry transducers and finite algebraic operator certificates (`arithSum_eq_transferPow`, `intertwining_lift`, `scaled_periodic_lift`, `trinomial_gf_cauchy`) to universally quantified arithmetic identities over all widths $w \in \mathbb{N}$, bounds $L \ge 1$, even radices $B = 2m$, and integer weights $t \in \mathbb{Z}$. We prove two determinant-free $(L+1) \times (L+1)$ parametric matrix annihilators (`rippleOp_annihilator` and `runOp_annihilator`) and establish a sharp duality between hardware carry metrics and Thue–Morse parity weights:

1. **Carry-run output-parity cyclotomic collapse (`evenRadix_carryRun_outputParity_collapse`, `binary_carryRun_fullPopcount_collapse`):** Summing $(-1)^{\sigma _ {2m}(w, (x+y) \bmod (2m)^w)}$ over all $(x,y) \in [0, (2m)^w)^2$ with maximum carry-bit run length $\le L$ collapses via hyperplane intertwining with cyclic rotation on $\mathbb{Z}^{L+2}$ to exact period $L+2$, taking values $+m^w$ ($w \equiv 0$), $-m^w$ ($w \equiv L+1$), and $0$ otherwise $\pmod{L+2}$ (and in binary, including the MSB carry-out bit, taking exact period-$(L+2)$ values $1, -2, 0, \dots, 0, 1$).
2. **Ripple-depth input-parity monomial collapse (`evenRadix_rippleDepth_inputParity_collapse`, `binary_rippleDepth_plain_recurrence`):** Summing $(-1)^{\sigma _ {2m}(w, x) + \sigma _ {2m}(w, y)}$ over pairs with ripple-carry propagation depth $\le L$ vanishes identically whenever $(L+1) \nmid w$ and equals $((-1)^{L+1} 2^L m^{L+1})^{w/(L+1)}$ whenever $(L+1) \mid w$, while the unweighted binary count satisfies $R _ L(w+L+1) = 4 R _ L(w+L) - 2^L R _ L(w)$.
3. **Bivariate absorption law & zero-absorption dichotomy (`binary_carryRun_absorption_recurrence`, `binary_zeroAbsorption_dichotomy`):** Weighting each carry absorption ($c _ i = 1 \to c _ {i+1} = 0$) by $t \in \mathbb{Z}$ yields $A _ L(t, w+L+2) = (1-t) A _ L(t, w+L) + t A _ L(t, w)$ for all $t, L, w$. At $t = 0$, $A _ L(0, w) = 0$ for all $w \ge L$ when $L$ is odd (exact finite support) versus $A _ L(0, w) = (-1)^w$ for all $w \ge L$ when $L$ is even.

## For Non-Mathematicians

When a computer adds two $w$-bit numbers, carry bits ripple from right to left. Take every pair of $w$-bit numbers whose longest unbroken carry chain is at most $L$, add them, and score each pair $+1$ or $-1$ according to whether the sum has an even or odd number of $1$-bits. Out of $4^w$ possible pairs, you would expect the total to fluctuate wildly; instead, cancellations are so rigid that the entire sum collapses to just $-1$, $0$, or $+1$, repeating with exact period $L+2$ for every $L$ and every bit width $w$! Conversely, if you cap true hardware ripple-carry depth at $L$ and weight by the parity of the inputs instead of the output, the sum collapses to $0$ on every width not divisible by $L+1$. Swapping either pairing immediately breaks the collapse into exponential growth.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of `CarryTransferEngine`, proving universal $(L+1) \times (L+1)$ ripple/carry-run matrix annihilators, cyclotomic period-$(L+2)$ carry-run Thue–Morse collapses, monomial period-$(L+1)$ ripple-depth collapses, and the bivariate carry-absorption odd/even dichotomy.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `evenRadix_carryRun_outputParity_collapse` | For all even radices $B = 2m$ ($m \ge 1$), $L \ge 1$, and $w \in \mathbb{N}$, the carry-run $\le L$ output-parity sum collapses with exact period $L+2$ to $+m^w$, $-m^w$, or $0$. |
| `binary_carryRun_fullPopcount_collapse` | For all $L \ge 1$ and $w \in \mathbb{N}$, the full-sum binary Thue–Morse sum $(-1)^{\mathrm{popcount}(w+1, x+y)}$ over $\mathrm{carryRun}(x,y) \le L$ has exact period $L+2$ with values $1, -2, 0, \dots, 0, 1$. |
| `evenRadix_rippleDepth_inputParity_collapse` | For all $m \ge 1$, $L \ge 1$, and $w \in \mathbb{N}$, the ripple-depth $\le L$ input-parity sum vanishes when $(L+1) \nmid w$ and equals $((-1)^{L+1} 2^L m^{L+1})^{w/(L+1)}$ when $(L+1) \mid w$. |
| `binary_rippleDepth_plain_recurrence` | For all $L \ge 1$ and $w \in \mathbb{N}$, the unweighted binary ripple-depth count satisfies $R _ L(w+L+1) = 4 R _ L(w+L) - 2^L R _ L(w)$. |
| `binary_carryRun_absorption_recurrence` | For all $t \in \mathbb{Z}$, $L \ge 1$, and $w \in \mathbb{N}$, the absorption-weighted carry-run sum satisfies $A _ L(t, w+L+2) = (1-t) A _ L(t, w+L) + t A _ L(t, w)$. |
| `binary_zeroAbsorption_dichotomy` | At $t = 0$ (zero carry absorptions), for all $L \ge 1$ and $w \ge L$, $A _ L(0, w) = 0$ if $L$ is odd and $A _ L(0, w) = (-1)^w$ if $L$ is even. |
| `rippleOp_annihilator` | Universal 3-parameter $(L+1)$-dimensional ripple-carry matrix annihilator $M^{L+1} - (k+p+g) M^L + g p^L I = 0$ for all $L \ge 1$ and $k, p, g \in \mathbb{Z}$. |
| `runOp_annihilator` | Universal 4-parameter $(L+1)$-dimensional carry-run matrix annihilator $M^{L+2} - (a+r) M^{L+1} + (ar-bc) M^L + b c r^L I = 0$ for all $L \ge 1$ and $a, b, c, r \in \mathbb{Z}$. |

## Proof Architecture

1. **Universal Bit-Slice Transfer Bridge (`arithSum_eq_transferPow`):** Exact radix-$B$ digit splitting $[0, B^{w+1}) \simeq [0, B^w) \times [0, B)$ and discrete adjointness between `pullbackOp` and `transferOp` equate the $B^{2w}$-term double sum over $[0, B^w)^2$ to $\langle f _ T, M _ T^w e _ {q _ 0} \rangle$ for any `CarryTransducer B N`.

2. **Determinant-Free Parametric Annihilators (`rippleOp_annihilator`, `runOp_annihilator`):** Explicit coordinate-by-coordinate induction proves the universal $(L+1)$-dimensional operator annihilators for arbitrary integer weights without determinants or Mathlib linear algebra.

3. **Hyperplane Intertwining & Scaled Periodicity (`intertwining_lift`, `scaled_periodic_lift`):** Embedding $\mathbb{Z}^{L+1}$ into the zero-sum hyperplane of $\mathbb{Z}^{L+2}$ intertwines the carry-run output-parity operator with $m \cdot \mathrm{rotR} _ {L+2}$, collapsing $M^{L+2} = m^{L+2} I$; for ripple depth, the annihilator collapses to $M^{L+1} = (-1)^{L+1} 2^L m^{L+1} I$.

4. **Concrete `Nat` Addition Bridges & Sharpness:** Exact semantic bridges connect `evalPair` to actual `Nat` addition `x + y`, `digitSum`/`popcount`, `maxCarryRunLe`, `maxRippleDepthLe`, and `carryAbsorptions`, complemented by five kernel-checked sharpness counterexamples (S1–S5) showing that swapping parity/metric pairings, using odd radices, or perturbing $t = 1$ destroys the collapses.

## Prior-Art Context

- **Unweighted ripple-carry chains:** Burks–Goldstine–von Neumann (1946), Knuth (*TAOCP* Vol. 4A), and Pippenger (2002) analyze unweighted longest ripple-carry chains and the recurrence $R _ L(w+L+1) = 4 R _ L(w+L) - 2^L R _ L(w)$, recovered here as a specialization (`binary_rippleDepth_plain_recurrence`) of our universal 3-parameter operator annihilator.
- **Carry Markov chains & Thue–Morse sums:** Holte (1997) and Diaconis–Fulman (2009) study single-step carry Markov chains for $m$-operand addition (not bounded carry-chain length transfer matrices or signed Thue–Morse collapses), while Gelfond, Dumont–Thomas, and Spiegelhofer study unrestricted Thue–Morse sums.
- **Novel contribution:** The carry-run/output-parity cyclotomic period-$(L+2)$ collapse, the ripple-depth/input-parity monomial period-$(L+1)$ collapse, their swap-breaking sharpness, and the bivariate absorption odd/even $L$ dichotomy are new; audited as S-Tier flagship with zero overlap against existing packages.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build logs and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. `scripts/explore_and_verify.py` replays the finite certificates and sharpness counterexamples in exact integer arithmetic (zero floats).
