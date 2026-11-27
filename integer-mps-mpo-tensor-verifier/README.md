# Exact Integer MPS/MPO Tensor-Network Contraction & Gauge-Intertwiner Compiler (`integer-mps-mpo-tensor-verifier`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): two-stage denominator-free exact integer Ho-Kalman / gauge-intertwiner MPS/MPO tensor-network compiler in pure Lean 4 Init, discharging parametric Rudin-Shapiro q-carry collapses, irrational-spectrum carry 4th moments, carry-Walsh Fibonacci laws, exact orthogonalities, and all-odd-power trace vanishing across all widths w.*

## For Mathematicians

We construct **`SiliconTensorEngine`**, a two-stage exact integer Ho-Kalman / gauge-intertwiner proof compiler for binary Matrix Product States (MPS) and Matrix Product Operators (MPO) of arbitrary bond dimension $D$ over $\mathbb{Z}$. By LSB-first splitting and the Kronecker mixed-product law, exponentially large $2^w$-dimensional inner products, traces, Hilbert–Schmidt products, and expectation values reduce uniformly to finite $K \times K$ integer transfer systems $(u, T, v)$. Guaranteed denominator-free by Gauss's Lemma, our two-stage compiler (`sound_rightReductionCert`, `sound_orthogonalityCert`, `sound_recurrenceCert`) verifies right-invariant Krylov projections $TP = P M _ 1$ and left-invariant quotients $Q M _ 1 = M _ 2 Q$ purely in `Int`/`Bool` via kernel `decide` (zero floats, zero `native_decide`), alongside pointwise MPS/MPO gauge intertwiners proving operator identities for all $w, x, y \in \mathbb{N}$.

This engine discharges six infinite theorem families:
1. **Parametric Rudin–Shapiro $q$-Carry Collapse (`thm_rs_carry_parametric_closed`):** For all $q \in \mathbb{Z}$ and $w \in \mathbb{N}$, $(q+3) S _ q(w) = (q+2) 2^{w+1} + (-(q+1))^{w+1}$ (specializing to $2^w$ at $q=-1$, constant $1$ at $q=-2$, Jordan-block $(1-w)2^w$ at $q=-3$, and Jacobsthal at $q=0$).
2. **Carry-Parity 4th Moment & All-Odd-Trace Vanishing (`thm_carry_all_odd_traces_zero`):** $\mathrm{Tr}(C _ {w+2}^4) = 4 \mathrm{Tr}(C _ {w+1}^4) + 64 \mathrm{Tr}(C _ w^4)$ (irrational eigenvalues $2 \pm 2\sqrt{17}$ certified purely over $\mathbb{Z}$), and $\mathrm{Tr}(C _ w^{2m+1}) = 0$ for all $w \ge 1, m \in \mathbb{N}$.
3. **Carry–Walsh Fibonacci Law vs. Borrow Orthogonality (`thm_carry_hadamard_fibonacci`, `thm_carry_borrow_orthogonal`):** $\mathrm{Tr}(C _ w H _ w) = 2^w F _ {w+2}$, whereas $\mathrm{Tr}(C _ w B _ w) = 0$ and $\mathrm{Tr}(B _ w(-1) H _ w) = 0$ for all $w \ge 1$.
4. **Pointwise Carry/Borrow Complementarity & MPO Unitarity (`thm_carry_plus_borrow_tm`):** $((C _ w + B _ w) \cdot \mathrm{TM} _ w)(x) = 2$ for all $w \ge 1, x \in \mathbb{N}$, plus two-stage $4 \to 2 \to 1$ unitarity of Gray-code and Modular-Increment MPOs.

## For Non-Mathematicians

Quantum-inspired tensor networks (Matrix Product States and Operators) compress vectors of length $2^w$ and matrices of size $2^w \times 2^w$ into tiny fixed-size integer building blocks. We built an exact-integer tensor-network proof compiler in Lean 4 that compresses huge binary sums — like correlating the Rudin–Shapiro sequence with binary addition carries or taking the 4th spectral trace of the binary carry-parity matrix — down to minimal $2 \times 2$ integer certificates checked in milliseconds. Without using a single floating-point or irrational number, it proves exact infinite-width formulas for every bit width $w$: the carry-Walsh trace equals $2^w$ times a Fibonacci number, the carry and borrow operators are strictly orthogonal, and every odd power of the carry-parity matrix has trace zero!

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of **`SiliconTensorEngine`**, a two-stage exact integer Ho-Kalman / gauge-intertwiner MPS/MPO tensor-network proof compiler discharging infinite-width carry, borrow, Rudin–Shapiro, Thue–Morse, and Walsh–Hadamard identities.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `sound_rightReductionCert` | Stage-1 exact integer Krylov projection soundness: $TP = P M _ 1$ lifts finite matrix checks to exact transfer-system equality for all $w \in \mathbb{N}$. |
| `sound_orthogonalityCert` | Two-stage orthogonality soundness: certifies exact vanishing $\forall w \ge w _ 0$, including non-nilpotent invariant-subspace orthogonality. |
| `sound_recurrenceCert` | Minimal-order recurrence soundness: certifies exact integer linear recurrences (even with irrational spectra) purely over $\mathbb{Z}$ for all $w \in \mathbb{N}$. |
| `thm_rs_carry_parametric_closed` | For all $q \in \mathbb{Z}$ and $w \in \mathbb{N}$, $(q+3) \sum _ {x,y < 2^w} \mathrm{RS} _ w(x) \mathrm{RS} _ w(y) q^{\mathrm{carries}(w,x,y)} = (q+2) 2^{w+1} + (-(q+1))^{w+1}$. |
| `thm_carry_hadamard_fibonacci` | For all $w \in \mathbb{N}$, the Carry–Walsh Hilbert–Schmidt trace equals $\mathrm{Tr}(C _ w H _ w) = 2^w \cdot F _ {w+2}$. |
| `thm_carry_borrow_orthogonal` | For all $w \ge 1$, the binary carry-parity and borrow-parity operators are strictly Hilbert–Schmidt orthogonal: $\mathrm{Tr}(C _ w B _ w) = 0$. |
| `thm_carry_all_odd_traces_zero` | For all $w \ge 1$ and $m \in \mathbb{N}$, every odd spectral moment of the binary carry-parity matrix vanishes: $\mathrm{Tr}(C _ w^{2m+1}) = 0$. |
| `thm_carry_plus_borrow_tm` | Pointwise complementarity on Thue–Morse: for all $w \ge 1$ and $x \in \mathbb{N}$, $((C _ w + B _ w) \cdot \mathrm{TM} _ w)(x) = 2$. |

## Proof Architecture

1. **Arbitrary Bond-Dimension MPS/MPO Contraction Core:** Proves LSB-first Kronecker transfer-matrix reductions for MPS inner products, MPO traces, MPO–MPS contractions, MPO compositions, and Hilbert–Schmidt inner products.

2. **Two-Stage Exact Integer Ho-Kalman Compression (`sound_rightReductionCert`, `sound_orthogonalityCert`, `sound_recurrenceCert`):** Denominator-free right-Krylov + left-quotient certificates checked by kernel `decide` certify orthogonality, closed forms, and irrational-spectrum recurrences purely over $\mathbb{Z}$.

3. **Pointwise Gauge-Intertwiner Engine:** Verifies finite matrix intertwiners $W _ 1^{(b,b')} P = P W _ 2^{(b,b')}$ via `decide` to discharge pointwise identities (`thm_carry_plus_borrow_tm`) and $4 \to 2 \to 1$ MPO unitarity for Gray-code and Modular-Increment operators.

4. **Hostile Mutation Rejection:** Backed by 12 kernel-verified hostile certificate rejections confirming that perturbing any intertwiner entry, transient shift, or recurrence coefficient fails `check*Cert`.

## Prior-Art Context

- **Weighted finite automata & tensor networks:** Berstel–Reutenauer (1988) develop rational series / weighted finite automata and Schollwöck (2011) surveys MPS/MPO tensor networks in physics.
- **Novel contribution:** A denominator-free two-stage exact integer Ho-Kalman & gauge-intertwiner Lean 4 proof compiler at bond dimension $D \ge 2$, discharging genuinely new infinite-width binary identities: the parametric Rudin–Shapiro $q$-carry collapse, Carry–Walsh Fibonacci law, Carry $\perp$ Borrow orthogonality, all-odd-trace vanishing of $C _ w$, and pointwise Carry/Borrow complementarity on Thue–Morse.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build logs and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. `scripts/explore_and_verify.py` replays the finite certificates and sharpness counterexamples in exact integer arithmetic (zero floats).
