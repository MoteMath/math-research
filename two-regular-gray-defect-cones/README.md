# 2-Regular Linear-Representation Algebra & Gray-Binary Defect Cones (`two-regular-gray-defect-cones`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a pure-Init Lean 4 2-regular linear-representation algebra compiler (`const`, `scale`, `add`, `sub`, Kronecker `mul`, `even`/`odd`, `shift1`, `prefixSum`) paired with four finite exact-integer matrix certificate engines (`IdentityCert`, `IntertwineCert`, `ModCert`, `ConeCert`/`ConePosCert` + kernel-decidable `Bool` checkers), discharging five infinite theorems on the 1-parameter base-$q$ Gray-Binary bitwise defect $S _ q(q, n)$ including the sharp $2/5$ switching-weight bound, aperiodic Thue-Morse parity, period-8 mod-4 law, exact dyadic parabolic sandwich, and a $q$-independent second-difference law.*

## For Mathematicians

Every $2$-regular integer sequence $f : \mathbb{N} \to \mathbb{Z}$ is represented by a finite leading-zero-stable linear representation $R = (u, M _ 0, M _ 1, v)$ of dimension $d$ over $\mathbb{Z}$ with $M _ 0 v = v$, evaluated LSB-first on binary digits $b _ 0, \dots, b _ k \in \{0, 1\}$:

```math
f(n) = u^{\top} M_{b_0} M_{b_1} \cdots M_{b_k} v, \qquad \mathrm{state}(0) = v, \quad \mathrm{state}(2n + b) = M_b\,\mathrm{state}(n).
```

We formalize two composable layers in pure Lean 4 `Init` (zero Mathlib):

1. **2-Regular Algebra Compiler:** `LinRep.const`, `scale`, `add`, `sub`, Kronecker product `mul`, dyadic decimations `even`/`odd`, carry-block `shift1` ($f(n) \mapsto f(n + 1)$ in dimension $2d$), and `prefixSum` ($f(n) \mapsto \sum _ {k=0}^{n-1} f(k)$ in dimension $2d$), all proved sound for all $n \in \mathbb{N}$.
2. **Four Finite-Matrix Certificate Engines:** `IdentityCert` (scaled left-invariant nullspace), `IntertwineCert` (matrix commutation bisimulation), `ModCert` / `checkModCert` (modular invariant subspace), and `ConeCert` / `ConePosCert` / `checkConePosCert` (polyhedral invariant cone with integer scaling denominators $\alpha, \beta > 0$ and MSB-1 entry $P M _ 1 v \ge 0$ for $n \ge 1$).

Let $G(n) = n \oplus \lfloor n / 2 \rfloor$ be the binary reflected Gray code, $\mathrm{popcount}(n)$ its Hamming weight, $h(n) = 2^{\lfloor \log _ 2 n \rfloor}$ (`highBit`), and define the 1-parameter base-$q$ Gray-Binary defect and prefix sum:

```math
d_q(n) := \sum_{i \ge 0} (g_i - b_i)\,q^i, \qquad S_q(q, n) := \sum_{k=0}^{n-1} d_q(k),
```

specializing at $q = 1$ to the cumulative Gray switching-weight excess $W _ G(n) = \sum _ {k=0}^{n-1}(\mathrm{popcount}(G(k)) - \mathrm{popcount}(k))$ and at $q = 2$ to the cumulative Gray value excess $E _ G(n) = \sum _ {k=0}^{n-1}(G(k) - k)$, with dyadic parabolic envelope $Q _ {\mathrm{dyadic}}(n) = (n - h(n))(2 h(n) - n)$. The eight headline theorems in `Challenge.lean` / `Solution.lean` are:

1. `checkConePosCert_sound`: pure-data `Bool` polyhedral cone certificate soundness (`checkConePosCert R D = true` implies $\forall n \ge 1,\; \mathrm{evalRep}(R, n) \ge 0$).
2. `gray_defect_nonneg_all_q`: for all $q \ge 0$ and all $n \in \mathbb{N}$, $S _ q(q, n) \ge 0$ (via a 4-row parametric `ConeCert`), even though individual terms $d _ 1(2^m - 1) = 1 - m \to -\infty$.
3. `W_G_sharp_two_fifths_bound`: for all $n \ge 1$, $5\,W _ G(n) \le 2n - 2 + (n \bmod 2)$ (via a 6-row `ConePosCert` with $\alpha = 1, \beta = 2$).
4. `extremal_W_G_odd`: infinite extremal attainment family `extremalA k` ($3, 23, 183, 1463, \dots$) satisfying $5\,W _ G(a _ k) = 2 a _ k - 1$ for every $k \in \mathbb{N}$ (proving exact tightness of both the $2/5$ slope and the $-1$ offset).
5. `W_G_thue_morse_parity`: for all $n \in \mathbb{N}$, $2 \mid (W _ G(n) - (n \bmod 2)(1 - (\mathrm{popcount}(n) \bmod 2)))$, an aperiodic odd-filtered Thue-Morse parity law.
6. `E_G_mod4_law`: for all $n \in \mathbb{N}$, $4 \mid (E _ G(n) - (n \bmod 2)(\lfloor n / 2 \rfloor \bmod 4))$, strictly period-$8$.
7. `E_G_dyadic_parabolic_sandwich`: for all $n \in \mathbb{N}$, $Q _ {\mathrm{dyadic}}(n) \le 2\,E _ G(n) \le 2\,Q _ {\mathrm{dyadic}}(n)$ (via `LinRep.mul` + $9 \times 5$ `IntertwineCert` + two `ConePosCert`s).
8. `S_q_second_diff_identity`: for all $q \in \mathbb{Z}$ and all $n \in \mathbb{N}$, $S _ q(q, 2n) + S _ q(q, 2n + 2) - 2\,S _ q(q, 2n + 1) = -2\,(n \bmod 2)$, completely independent of $q$.

`Theorems.lean` additionally proves `extremal_W_G_even`, `extremal_E_G_lower`, `extremal_E_G_upper_mid`, all four certificate soundness theorems (`IdentityCert.sound`, `IntertwineCert.sound`, `ModCert.sound`, `ConeCert.sound`, `ConePosCert.sound`, `checkModCert_sound`), non-vacuity witnesses, hostile mutation rejections, and sharpness counterexamples.

## For Non-Mathematicians

Gray code is a way of counting in binary so that consecutive numbers differ in only one bit, widely used in hardware encoders and digital circuits. If you compare the number of `1`-bits in Gray code versus ordinary binary and keep a running total across $0, 1, \dots, n - 1$, individual numbers can make the running total dip sharply, yet the total **never** goes negative and **never** exceeds $\frac{2}{5} n$ (and hits that exact $2/5$ ceiling infinitely often). Instead of proving these bounds with real analysis or fractals, this package builds a small compiler for binary matrix machines and proves that a handful of tiny integer tables, checked mechanically by Lean's kernel, lock in the exact inequalities, remainders, and identities for every whole number $n$ up to infinity.

## Prior Art

- Linear representations of $k$-regular sequences were introduced by Allouche & Shallit (1992). Automatic decision tools such as Walnut (Mousavi 2016) handle bounded-value automatic predicates via DFAs, while classical cumulative binary bit-sum bounds use Trollope-Delange (1968, 1975) Takagi fractal analysis.
- What is formalized here beyond that baseline: a pure-Init Lean 4 2-regular algebra compiler (`mul`, `shift1`, `prefixSum`) coupled with exact integer-scaled polyhedral invariant-cone and modular-subspace certifiers (`ConePosCert`, `ModCert`), and the five infinite Gray-Binary defect laws (sharp $2/5$ ceiling with parity offset, aperiodic Thue-Morse parity, period-8 mod-4 law, dyadic parabolic sandwich, and $q$-independent second-difference law).
- Independently audited and `PASS`ed by `referee-1` (156/156 theorems on standard axioms, zero floats).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
python scripts/explore_and_verify.py
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. The package depends only on Lean 4 core (`Init`).
