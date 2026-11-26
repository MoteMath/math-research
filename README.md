# math-research

Machine-checked Lean 4 formalizations of exact determinant factorizations, binary-arithmetic dynamics, spectral graph counts, and combinatorial inequalities developed at MoteMath.

Each subdirectory is a self-contained Lake project with its own toolchain pin, `README.md` (with a **Synthetic Score**, **For Mathematicians** summary, and **For Non-Mathematicians** overview), `AUDIT.md`, and build instructions. Projects follow the [Palomar](https://palomar-registry.org/) submission layout (`Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`).

## Synthetic Score Matrix

Each project carries a heuristic self-rating out of `100` across five `1–10` dimensions (not a substitute for peer review):

```math
\mathrm{Score} = 3\cdot\mathrm{Nov} + 2\cdot\mathrm{Sur} + 2\cdot\mathrm{Gen} + 2\cdot\mathrm{Use} + 1\cdot\mathrm{Ver}.
```

- **Nov (30%):** Novelty — distance from published literature and OEIS.
- **Sur (20%):** Surprise & Depth — non-obviousness of the collapse or proof mechanism.
- **Gen (20%):** Generality — arbitrary rings/radices, all sizes/widths, exact `iff` laws.
- **Use (20%):** Usefulness — bridge value to bit-level arithmetic, graphs, or combinatorics.
- **Ver (10%):** Verification — `10` for pure `Init`/`Std` (zero Mathlib) + Palomar `nanoda`; `9` for Mathlib + Palomar `nanoda` (all zero `sorry`, standard axioms only).

| Project | Nov | Sur | Gen | Use | Ver | Score |
|---| :---: | :---: | :---: | :---: | :---: | :---: |
| [`universal-vertex-invroot/`](universal-vertex-invroot/) | 9 | 9 | 9 | 9 | 10 | **91** |
| [`moe-bias-placement-codes/`](moe-bias-placement-codes/) | 9 | 9 | 9 | 9 | 10 | **91** |
| [`mxfp6-ef21-rotations/`](mxfp6-ef21-rotations/) | 9 | 9 | 10 | 8 | 10 | **91** |
| [`bitnet-contraction-hierarchy/`](bitnet-contraction-hierarchy/) | 9 | 9 | 10 | 8 | 10 | **91** |
| [`spec-decoding-ot-bounds/`](spec-decoding-ot-bounds/) | 9 | 9 | 10 | 8 | 10 | **91** |
| [`ef21-ternary-contraction/`](ef21-ternary-contraction/) | 9 | 9 | 10 | 8 | 9 | **90** |
| [`sparse-e2m1-rotations/`](sparse-e2m1-rotations/) | 9 | 9 | 9 | 8 | 10 | **89** |
| [`muon-vertex-polar/`](muon-vertex-polar/) | 9 | 9 | 8 | 9 | 10 | **89** |
| [`ternary-lop3-circuits/`](ternary-lop3-circuits/) | 9 | 9 | 8 | 9 | 10 | **89** |
| [`subbyte-e2m1-lop3/`](subbyte-e2m1-lop3/) | 9 | 9 | 8 | 9 | 10 | **89** |
| [`soap-vertex-fourth-root/`](soap-vertex-fourth-root/) | 9 | 9 | 8 | 9 | 10 | **89** |
| [`sparse24-e2m1-lop3/`](sparse24-e2m1-lop3/) | 9 | 9 | 8 | 9 | 10 | **89** |
| [`octonion-rope-welch-frames/`](octonion-rope-welch-frames/) | 9 | 9 | 9 | 8 | 10 | **89** |
| [`binary-lyness-periods/`](binary-lyness-periods/) | 9 | 10 | 9 | 7 | 10 | **89** |
| [`clmul-lift-determinants/`](clmul-lift-determinants/) | 9 | 10 | 9 | 7 | 9 | **88** |
| [`zero-carry-spanning-trees/`](zero-carry-spanning-trees/) | 9 | 9 | 9 | 7 | 9 | **86** |
| [`arx-fibonacci-isospectrality/`](arx-fibonacci-isospectrality/) | 8 | 9 | 8 | 8 | 10 | **84** |
| [`skew-thue-morse-pfaffian/`](skew-thue-morse-pfaffian/) | 9 | 9 | 8 | 7 | 9 | **84** |
| [`bitrev-increment-cycles/`](bitrev-increment-cycles/) | 8 | 9 | 8 | 7 | 10 | **82** |
| [`carry-determinants/`](carry-determinants/) | 7 | 8 | 10 | 8 | 9 | **82** |
| [`weak-bruhat-commutators/`](weak-bruhat-commutators/) | 7 | 8 | 8 | 7 | 10 | **77** |
| [`carry-blocks-determinants/`](carry-blocks-determinants/) | 6 | 7 | 9 | 7 | 9 | **73** |
| [`grh-ultra-compact-lean/`](grh-ultra-compact-lean/) | 4 | 6 | 10 | 9 | 9 | **71** |
| [`combinatorial-inequalities/`](combinatorial-inequalities/) | 6 | 6 | 7 | 6 | 10 | **66** |
| [`sorting-operators/`](sorting-operators/) | 5 | 5 | 7 | 6 | 10 | **61** |

## Findings

### 1. [`universal-vertex-invroot/`](universal-vertex-invroot/) — **91 / 100**
- **Plain English:** Proves a single universal "completed-square" formula for computing any matrix inverse $p$-th root ($G^{-1/2}, G^{-1/3}, G^{-1/4}, G^{-1/8}, \dots$) in BF16/FP8 AI optimizers with zero cancellation and cubic convergence — and proves why 3-matmul degree-5 polar polynomials beat clever 4-matmul degree-9 polynomials in low precision (`> 1.65×` smaller rounding floor).
- **For Mathematicians:** Universal all-$p$ ($\forall p \ge 1, m \in \mathbb{Q}$) vertex identity $1 - (m - 1)/p + \frac{p+1}{2p^2}(m - 1)^2 = \frac{2p+1}{2p+2} + \frac{p+1}{2p^2}(m - \frac{2p+1}{p+1})^2 \ge \frac{3}{4}$ with exact monomial condition number $\kappa _ {\mathrm{mono}}(p) = 1 + 4/p + 2/p^2$ vs $\kappa _ {\mathrm{sum}} = 1$; universal all-$p$ cubic convergence $m P _ p(m)^p - 1 = (m - 1)^3 R _ p(m - 1)$ with exact leading constant $R _ p(0) = (p+1)(2p+1)/(6p^2)$; exact 4-matmul degree-9 shared-square identity and $> 1.65\times$ rounding-floor dominance $(1+u)^6 < (1+u)^{10}$ across BF16/FP8; plus pure-`Init` cleared-denominator `Int` 6-step BF16 confinement certificates for $p = 2$ (`[0.982, 1.018]`), $p = 3$ (`[0.974, 1.026]`), and $p = 8$ (`[0.932, 1.068]`).
- **Prior art & stack:** Unifies Guo & Higham (2006) coupled $p$-th roots, Shampoo/SOAP/Muon, and `muon-vertex-polar/` / `soap-vertex-fourth-root/` into a universal all-$p$ theory with exact degree-9 rounding-floor refutation. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 2. [`moe-bias-placement-codes/`](moe-bias-placement-codes/) — **91 / 100**
- **Plain English:** Proves six exact mathematical laws for Mixture-of-Experts (MoE) LLM clusters: why DeepSeek-V3's aux-loss-free load-balancing bias drifts linearly without mean-centering, the exact sharp dead-zone threshold where zero fixed points exist, why minimizing network fanout opposes intra-GPU hotspots, exact zero-hotspot affine-plane (`AG(2, 4)` and `AG(2, 8)`) GPU placement codes, the universal EPLB redundant-expert capacity limit, and exact margin thresholds preventing quantized routers from flipping expert assignments.
- **For Mathematicians:** Exact aux-loss-free mean-bias drift bound $|\frac{1}{E}\sum \delta _ i| \le \frac{E-2}{E}\gamma$ and exact mean-centered zero-drift invariance; sharp dead-zone fixed-point phase transition at $\tau _ {\min} = \max(r, E - r)/E$ ($r = (B K) \bmod E$: zero fixed points for $\tau < \tau _ {\min}$, attained at $\tau = \tau _ {\min}$); exact discrete-convexity duality between cross-GPU fanout and intra-GPU dispersion; explicit resolvable affine-plane BIBD placement codes $AG(2, 4)$ ($E = 16, G = 4$) and $AG(2, 8)$ ($E = 64, G = 8$) with zero pair-collision hotspots; universal EPLB redundant-expert pigeonhole lower bound; and exact uniform/floating-point quantized-router zero-flip margin thresholds.
- **Prior art & stack:** Builds on DeepSeek-V3 (2024) aux-loss-free load balancing and EPLB, Switch/GShard MoE routing, and classical resolvable affine-plane BIBDs; no prior publication found for the sharp dead-zone phase transition, fanout-dispersion duality, or unified Lean 4 router-placement certification. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 3. [`mxfp6-ef21-rotations/`](mxfp6-ef21-rotations/) — **91 / 100**
- **Plain English:** Proves the exact compression speed limits for 6-bit floating-point AI formats (`MXFP6-E3M2` vs `MXFP6-E2M3`) across every block size — pinpointing the exact block-size crossover (`B = 43` vs `B = 44` for MXFP6; `B = 178` vs `B = 179` for NVFP6) — alongside exact Hadamard quantization defect laws, exact 4-bit/6-bit-native Goethals–Seidel orthonormal matrices (`16 × 16` and zero-free `32 × 32`), and universal 4:8-sparse Hamilton quaternion rotations.
- **For Mathematicians:** Universal all-$B$ ($\forall B \ge 1$) EF21 contraction laws with tightness/attainment for OCP `MXFP6-E3M2`, `MXFP6-E2M3`, `NVFP6-E3M2`, and `NVFP6-E2M3`; exact crossover proving `E2M3 > E3M2` for $1 \le B \le 43$ (`B = 32`: $4608/4655 > 327680/331807$) and `E3M2 > E2M3` for $B \ge 44$ (and $2 \le B \le 178$ vs $B \ge 179$ for NVFP6); exact quantized Hadamard defects $9/8$ ($n = 8$) and $121/128$ ($n = 32$) plus sharp minimum dyadic coherence bounds; exact Goethals–Seidel `16 × 16` and zero-free `32 × 32` orthonormal matrices ($G^T G = 64 I$) with every entry exact in `E2M1 ∩ E3M2 ∩ E2M3`; and universal 4:8-sparse permutation-coupled Hamilton quaternion orthogonal stages in dimension $4m$.
- **Prior art & stack:** Extends OCP MXFP6 (Rouhani et al. 2023), EF21 (Richtárik et al. 2021), Goethals–Seidel (1970) arrays, and `ef21-ternary-contraction/` / `sparse-e2m1-rotations/`; no prior publication found for the universal MXFP6/NVFP6 EF21 crossover laws or E2M1-native Goethals–Seidel orthonormal matrices. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 4. [`bitnet-contraction-hierarchy/`](bitnet-contraction-hierarchy/) — **91 / 100**
- **Plain English:** Proves an exact three-tier mathematical hierarchy separating BitNet 1.58-bit scaling heuristics (`AbsMean` and `AbsMax` scale as $\Theta(1/d)$, `RMS` jumps an entire tier to $\Theta(1/\sqrt{d})$, and optimal ternary scales as $\Theta(1/\ln d)$), proves the exact critical dimension $d _ {\mathrm{crit}} = 8M^2 + 4$ (`76` for INT3, `396` for INT4) where multi-level quantizers phase-transition, and proves that greedy 2-stage ternary beats joint disjoint at $d = 3$ before reversing at $d \ge 4$.
- **For Mathematicians:** Universal over `Rat` ($\forall d \ge 1, \gamma \ge 0, x : \mathrm{Fin}\,d \to \mathbb{Q}$): nonnegative ternary contraction $\alpha \ge 0$ and exact tie-break invariance (`≥` vs `>`); exact `AbsMean` contraction $(2d - 1)/d^2$, `AbsMax` $4/(d + 3)$, and `AbsMax/2` $12/(d + 15)$ with attainment; universal `RMS` algebraic law $3d + 1 \le (d\alpha + 1)^2$ ($\Theta(1/\sqrt{d})$) with exact rational witnesses at $d = 8, 16$; universal multi-level shifted-square-root sandwich $(4M^2 + 1)^2 < 16M^2(M^2 + 1) < (4M^2 + 2)^2$ and exact feasibility threshold $d _ {\mathrm{crit}}(M) = 8M^2 + 4$ (`36`, `76`, `396`); and exact $d = 3$ vs $d = 4$ 2-stage ternary greedy-vs-disjoint crossover.
- **Prior art & stack:** Builds on BitNet b1.58 (Ma et al. 2024), EF21 (Richtárik et al. 2021), and `ef21-ternary-contraction/`; no prior publication found for the closed-form three-tier BitNet heuristic contraction hierarchy, $d _ {\mathrm{crit}} = 8M^2 + 4$ multi-level phase transition, or $d = 3 / 4$ 2-stage crossover. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 5. [`spec-decoding-ot-bounds/`](spec-decoding-ot-bounds/) — **91 / 100**
- **Plain English:** Proves the exact universal acceptance-rate advantage of correlated over i.i.d. multi-draft speculative decoding, refutes the optimality of Cyclic Madow sampling (even with oracle descending $p / q$ sorting!), proves tight worst-case acceptance losses when draft models are quantized (FP4/INT4), and proves unconditional bit-exact invertibility of modular `BitVec` reversible Transformers alongside exponential hyperbolic drift of floating-point reversible layers.
- **For Mathematicians:** Universal correlated-vs-i.i.d. multi-draft optimal transport multiplicative gap $K^K / (K^K - (K - 1)^K)$ and additive gap $((K - 1)/K)^K$ for all $K \ge 1, V$ with exact attainment; constructive $K = 2, V = 4$ counterexamples refuting both default-order ($1/2 < 3/4 < 1$) and oracle descending-$p / q$-sorted ($17/20 < 91/100 < 1$) Cyclic Madow optimality; universal tight quantized-draft acceptance loss bounds $(R - 1)/(R + 1)$ ($K = 1$) and $(K - 1)(R^2 - 1)/(1 + (K - 1)R^2)$ ($K \ge 2$); exact bidirectional invertibility of modular `BitVec b` reversible Transformers for all widths $b$ and depths $L$; and exact unimodularity $\det M(\gamma)^n = 1$ with exponential growth $(M(\gamma)^n) _ {0,0} + (M(\gamma)^n) _ {0,1} \ge (1 + \gamma)^n$ for floating-point reversible coupling.
- **Prior art & stack:** Builds on SpecTr (Sun et al. 2023), Multi-Draft Speculative Decoding / Cyclic Madow (Miao et al. 2024; Sun et al. 2024), and Reversible Transformers (Gomez et al. 2017; Mangalam et al. 2022); no prior publication found for the exact universal $K^K$-gap, oracle-sorted Madow refutation, or tight $K$-draft quantized-draft loss formula. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 6. [`ef21-ternary-contraction/`](ef21-ternary-contraction/) — **90 / 100**
- **Plain English:** Proves the exact mathematical speed limits for compressing AI gradients across GPU networks under Error Feedback (`EF21`): adding zero to 1-bit sign compression causes an exponential jump (`375×` stronger at $d = 1024$), leaving zero out of symmetric 2-bit collapses back to $O(1/d)$, and modern 4-bit formats (`MXFP4` and `NVFP4`) follow exact multi-regime phase transitions across every block size $B \ge 1$.
- **For Mathematicians:** Universal exact EF21 contraction law $\alpha _ {\mathrm{tern}}(d) = (\sum _ {i=0}^{d-1} (\sqrt{i+1} - \sqrt{i})^2)^{-1}$ over $\mathbb{R}^d$ (proved via Abel summation by parts, tightly attained at $w _ i = \sqrt{i+1} - \sqrt{i}$) with exact harmonic sandwich $4 / (4 + H _ {d-1}) \le \alpha _ {\mathrm{tern}}(d) \le 4 / (3 + H _ d)$; exact universal multi-regime OCP E2M1 contraction laws for MXFP4 ($\min(384/(B+399), 192/(B+195), 144/(B+143))$, 3 regimes, exact $48/53$ at $B = 16$ and $144/175$ at $B = 32$) and NVFP4 ($\min((24B+12)/(25B+11), 576/(B+575))$, 2 regimes, exact $132/137$ at $B = 16$ and $576/607$ at $B = 32$) for all $B \ge 1$; symmetric 2-bit zero-omission collapse $\alpha \le 9/(d+8)$; and exact $m$-bit mantissa stochastic rounding relative variance law $1/(4 \cdot 2^m (2^m + 1))$.
- **Prior art & stack:** Builds on Richtárik et al. (NeurIPS 2021) EF21, TernGrad (Wen et al. 2017), Horváth et al. (2019) Natural Compression, and OCP MXFP4 / Blackwell NVFP4; no prior publication found for the exact $\Theta(1/\ln d)$ ternary EF21 extremal law or the universal multi-regime MXFP4/NVFP4 phase diagrams. Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 7. [`sparse-e2m1-rotations/`](sparse-e2m1-rotations/) — **89 / 100**
- **Plain English:** Proves an exact 2-step **2:4-sparse** factorization of every Walsh–Hadamard matrix (matching modern GPU sparse Tensor Cores at 2× speed with zero error) and constructs exact 4-bit-native (E2M1) orthogonal rotations that beat dense Hadamard by up to `+5.4 dB` on heavy-tailed LLM outliers.
- **For Mathematicians:** Universal doubly-2:4-sparse $\{-1, 0, 1\}$ orthogonal factorization $(H _ {2^k} \otimes B _ 1)(I _ {2^k} \otimes B _ 2) = H _ {4 \cdot 2^k}$ for all $k \in \mathbb{N}$, universal single-2:4 coherence lower bound $2c \le (4m) M^2$ attained by $W _ {4 \cdot 2^k} = H _ {2^k} \otimes B _ 1$, universal skew-conference E2M1 orthogonality $(a I + C)^T (a I + C) = (a^2 + n - 1) I$, exact power-of-2 E2M1-native $Q _ {32} = H _ 4 \otimes (I _ 8 + 3 C _ 8)$ ($Q _ {32}^T Q _ {32} = 16^2 I _ {32}$), NVFP4 winner $Q _ {16} = 4 I _ {16} + C _ {16}$ ($c = 31$), and universal doubly-2:4-sparse E2M1 family $G _ {4 \cdot 2^k}(1, 2)$.
- **Prior art & stack:** Builds on Sylvester/Walsh–Hadamard, Paley skew-conference matrices, QuIP#/QuaRot/MR-GPTQ/DuQuant++, and 2:4 structured sparsity; no prior publication found for the doubly-2:4-sparse Hadamard factorization or E2M1-native skew-conference rotations. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 8. [`muon-vertex-polar/`](muon-vertex-polar/) — **89 / 100**
- **Plain English:** Rewriting the Muon AI optimizer's 5th-degree matrix-orthogonalization polynomial into a positive "shifted-square" vertex form eliminates low-precision cancellation at the exact same compute cost — making BF16 updates up to `139×` tighter and delivering the first provably safe FP8 E4M3 polar schedules.
- **For Mathematicians:** Proves the shifted-square identity $a x + b x^3 + c x^5 = x(\alpha + c(x^2 - \mu)^2)$ and exact quadratic Gram rounding-error annihilation $O(\beta u^2)$ vs monomial linear error $(b + 2c)\delta _ 1$, derives exact pointwise degree-5 envelopes for the 6-rounding-point `NoisyShiftedStep` model, and certifies continuous 5-step trajectory confinement of $[1/100, 1]$ via cleared-denominator homogeneous degree-5 Bernstein certificates in BF16 ($u = 1/256$: stationary `[0.942, 1.052]`, DP `[0.987, 1.013]`), pure FP8 E4M3 ($u = 1/16$: `[0.31, 1.65]`), and hybrid FP8 ($u = 1/32$: `[0.824, 1.163]`).
- **Prior art & stack:** Builds on Jordan (2024) Muon and Amsel et al. (2025, `2505.16932`) Polar Express; no prior publication found for the vertex-form quadratic error-annihilation theorem or kernel-certified BF16/FP8 E4M3 polar schedules. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 9. [`ternary-lop3-circuits/`](ternary-lop3-circuits/) — **89 / 100**
- **Plain English:** Proves exact minimum-gate bitwise GPU circuits that unpack tightly compressed 1.58-bit BitNet ternary weights using zero multiplications, divisions, or lookup tables — saving 16.7%–20% memory bandwidth while running faster on real GPUs — plus exact zero-FP ternary×INT4/FP4 dot-product circuits.
- **For Mathematicians:** Synthesizes and proves soundness + surjectivity of a **6-`LOP3` depth-2** 3-trit/5-bit unpacker (with an exact pigeonhole lower bound proving no input literal pass-through is possible, $18 > 16$, plus a 4-codeword escape cube still covering all $27$ triples) and a **14-`LOP3` depth-4** 5-trit/8-bit unpacker (with an exact weight-divisibility lower bound proving no output lane can depend on $\le 4$ inputs, since $[81, 94] \cap 16\mathbb{Z} = \emptyset$), alongside exact 9-`LOP3` ternary×INT4, 4+10-`LOP3` zero-offset ternary×FP4 (E2M1), and universal 3:2 CSA `popcnt` conservation over all $a, b, c \in \mathbb{N}$.
- **Prior art & stack:** Builds on BitNet b1.58 (Ma et al. 2024), T-MAC (Wei et al. 2024), GPU `LOP3` instructions, and Harley–Seal CSA trees; no prior publication found for these co-designed minimal-`LOP3` encodings, lower bounds, or zero-FP E2M1 dot circuits. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 10. [`subbyte-e2m1-lop3/`](subbyte-e2m1-lop3/) — **89 / 100**
- **Plain English:** Exploiting the fact that FP4 treats `-0.0` and `+0.0` identically lets GPUs unpack 2 ternary weights from 4 bits with **zero logic gates** and 3 ternary weights from 5 bits (`-58.33%` VRAM vs FP4) using only **4 `LOP3` gates** — alongside exact proofs explaining why 2.33-bit quinary unpacking requires multi-stage depth, how asymmetric 2-bit weights gain a 4th level with free polarity flip, and why 3:2 adders beat 4:2 compressors on `LOP3` GPUs.
- **For Mathematicians:** Exact 0-`LOP3` 2-trit/4-bit and 4-`LOP3` (`0x73`, `0xC7`, `0x3B`, `0x71`) 3-trit/5-bit $\to$ OCP E2M1 nibble unpackers covering all $9$ and $27$ tuples; general $\ge 3$-`LOP3` lower bound via Hamming weight $w(f _ i) \in [18, 23]$ vs $8 \mid w(g)$ for $\le 2$-variable functions; universal $\ge 5$-variable support barrier (`LOP3` depth $\ge 2$) for all surjective 3-quinary/7-bit decoders ($w \in [25k, 25k + 3] \implies 8 \nmid w$); bijective 2-bit asymmetric `{-2, -1, 0, +1}` $\leftrightarrow$ `{-1, 0, +1, +2}` signed-scale duality with universal 2-plane dot-product identity; and exact `LOP3` depth inversion proving 5-input 4:2 parity requires depth $\ge 2$ while 3:2 CSA (`0x96`, `0xE8`) executes in 2 `LOP3`s at depth $1$.
- **Prior art & stack:** Builds on OCP MXFP4/E2M1 (Rouhani et al. 2023), BitNet b1.58 (Ma et al. 2024), Weinberger (1981) 4:2 compressors, and NVIDIA PTX `lop3.b32`; no prior publication found for the direct E2M1 signed-zero 0/4-`LOP3` unpackers, 3-quinary/7-bit support barrier, or `LOP3` 4:2/3:2 depth inversion. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 11. [`soap-vertex-fourth-root/`](soap-vertex-fourth-root/) — **89 / 100**
- **Plain English:** Rewriting quadratic matrix inverse-fourth-root ($G^{-1/4}$) polynomials for Shampoo and SOAP optimizers into a strictly positive "completed-square" vertex form eliminates low-precision subtraction cancellation — delivering **$6.18\times$ to $15.1\times$** tighter BF16 accuracy than classical Guo–Higham — while proving that at extreme pure FP8 precision ($u = 1/16$), fourth-power noise amplification causes tuned linear schedules to overtake quadratic ones.
- **For Mathematicians:** Exact completed-square identity $a + b m + c m^2 = (a - b^2/(4c)) + c(m + b/(2c))^2$ and global positivity; exact Taylor-2 vertex form $9/10 + (5/32)(m - 9/5)^2 \ge 9/10$ with exact cubic coupled residual $m P(m)^4 - 1 = (m - 1)^3 R(m)$; exact pointwise adversarial envelopes for 7-rounding-point `NoisyVertexStep4` and 5-rounding-point `NoisyLinearStep4`; and pure-`Init` cleared-denominator `Int` interval certificates confining every 5-step trajectory in BF16 (`u = 1/256`: `[0.965, 1.039]` at $\varepsilon = 10^{-2}$, `[0.935, 1.049]` at $\varepsilon = 10^{-4}$), hybrid FP8 (`u = 1/32`: `[0.652, 1.329]`), and the pure FP8 E4M3 linear crossover (`u = 1/16`: `[0.257, 1.654]`).
- **Prior art & stack:** Extends Shampoo (Gupta et al. 2018), SOAP (Vyas et al. 2024), Guo & Higham (2006) coupled $p$-th root Newton, and `muon-vertex-polar/` ($G^{-1/2}$) to BF16/FP8-certified vertex-form $G^{-1/4}$ polynomials and the FP8 fourth-power linear crossover. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 12. [`sparse24-e2m1-lop3/`](sparse24-e2m1-lop3/) — **89 / 100**
- **Plain English:** GPU-synthesized minimal `LOP3` circuits that unpack 5 ternary weights from 1 byte directly into FP4 (`-60%` VRAM) in **10 gates**, compress 2:4-sparse metadata by `25%` (`1 LOP3`!) and `33.3%` (`12 LOP3`!), multiply two FP4 magnitudes with zero floating-point hardware in `25 LOP3` (`1.36×` faster than FP32 on RX 7900 XTX), and unpack 2 quinary weights from 5 bits in `4 LOP3` — all paired with exact lower bounds.
- **For Mathematicians:** Exact 10-`LOP3` direct-sign `5t8b → 5×E2M1` unpacker (`243/243`) + general Hamming-weight barrier $162 \le w(f _ i) \le 175$ vs $16 \mid w(g)$ ($\ge 5$ essential vars, depth $\ge 2$); tight 1-`LOP3` `3b → 4b` 2:4 mask (`0x17`) and 1-`LOP3` unordered `{idx0, idx1}` (`0x63`, $3\times$ fewer gates than tight 3-`LOP3` ordered); 12-`LOP3` `8b → 3×4b` 2:4 mask unpacker (`216/216`) + unique $(1, 1, 1)$ fiber-product direct-wire theorem ($6^3 = 2^3 \times 3^3$); 25-`LOP3` exact zero-FP `E2M1 × E2M1` magnitude multiplier (`64/64` in `[0, 144]`); and 4-`LOP3` depth-2 `2q5b → 2×E2M1` (`25/25`) + 4-wire impossibility theorem.
- **Prior art & stack:** Extends NVIDIA 2:4 structured sparsity (Mishra et al. 2021), OCP MXFP4 (Rouhani et al. 2023), BitNet b1.58, and `subbyte-e2m1-lop3/`; no prior publication found for these minimal `LOP3` 2:4-metadata, `5t8b → E2M1`, zero-FPU `E2M1 × E2M1`, or `2q5b → E2M1` circuits and lower bounds. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 13. [`octonion-rope-welch-frames/`](octonion-rope-welch-frames/) — **89 / 100**
- **Plain English:** Proves why 4D bit-shift RoPE rotations are mathematically impossible (always stuck at 24 trivial angles) while 8D **octonion** rotations break the barrier with exact `>> 16` bit-shift normalization, certifies five multiplication-free sparse ternary attention-key sketches that hit the physical Welch interference limit (`1.00000`), and proves the exact worst-case $\ell _ 1$ error formulas for top-$K$ and quantized Softmax.
- **For Mathematicians:** Universal mod-8 4-square descent proving zero primitive solutions to $a^2+b^2+c^2+d^2 = 2^r$ for $r \ge 3$ and exact $r _ 4(2^r) = 24$ Hurwitz classification for all $r \ge 1$; universal integer/rational orthogonality of 2D Pythagorean, 4D Hamilton quaternion, and 8D Cayley–Dickson octonion RoPE plus concrete `>> 16` Llama-2 witness ($\sum x _ i^2 = 2^{32}$); universal integer Welch Frobenius lower bound $m\,\Phi(S) \ge d s^2 (d - m)$ attained with exact ratio `1.00000` by 5 GPU-discovered sparse ternary frames (`(8,16) s∈{3,4,5}`, `(12,24) s∈{3,4}`); and exact sharp Softmax $\ell _ 1$ laws $2(N-K)/(K E + N - K)$ (Top-$K$ gap) and $2(R-1)/(R+1) = 2\tanh(\epsilon/2)$ ($\pm\epsilon$ quantized logits).
- **Prior art & stack:** Builds on Jacobi's four-square theorem, RoFormer (Su et al. 2021), Welch (1974), and sparse ternary JL projections (Achlioptas 2003; Kane–Nelson 2014); no prior publication found for the 4D-obstruction/8D-octonion bit-shift RoPE resolution, these 5 exact Welch-tight sparse ternary frames, or the algebraic rational Softmax $\ell _ 1$ proofs. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 14. [`binary-lyness-periods/`](binary-lyness-periods/) — **89 / 100**
- **Plain English:** Repeating $(x, y) \to (y,\; x \oplus (y + 2^r))$ on **any** two whole numbers — no matter how huge — always snaps back to where you started after **exactly $6$ steps** (and this works **only** when the constant is $0$ or a power of $2$), while its bitwise-OR twin $(y,\; x \oplus (y \mathbin{|} (y + 2^r)))$ always snaps back in **exactly $12$ steps**.
- **For Mathematicians:** General XOR-Feistel carry-renormalization laws on unbounded $\mathbb{N} \times \mathbb{N}$: $f(2k) = 2k + 1, f(2k + 1) = 2h(k)$ forces $F _ f^6 = \mathrm{id}$ off odd-odd states via exact $F _ f^3$-invariance of $a \oplus b$, and $f(2k + 1) = 2g(k) + 1$ forces $F _ f^{12} = \mathrm{id}$ globally via conjugacy of $F _ f^4$ to $\mathbb{F} _ 2$-Fibonacci; implies $F _ c^6 = \mathrm{id} \iff c = 0 \lor \exists r,\, c = 2^r$ and $H _ {2^r}^{12} = \mathrm{id}$ for all $r$.
- **Prior art & stack:** Echoes classical rational Lyness recurrences (Lyness 1942) and contrasts with addition *outside* XOR (MathOverflow *"A Bitwise Xor Problem"*); no prior publication or OEIS match found for these laws or dichotomy. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 15. [`clmul-lift-determinants/`](clmul-lift-determinants/) — **88 / 100**
- **Plain English:** Odd carry-less multiplication tables have determinant $0$ almost everywhere — except right next to powers of $2$ ($2^k - 1, 2^k, 2^k + 1$), where they snap to exact powers of $2$ via a hidden bit-reversed Hadamard matrix.
- **For Mathematicians:** Division-free polynomial Schur reduction of $(M _ n(t)) _ {i,j} = \mathrm{lift} _ {\mathbb{Z}}(P _ {2i+1} \cdot _ {\mathbb{F} _ 2[x]} P _ {2j+1})(t)$ to $(-2 t^{k+1}) H _ {k,m}^{\mathrm{rev}}$ over any commutative ring $R$, yielding exact single-monomial determinants at $n \in \{2^k - 1, 2^k, 2^k + 1\}$, identical gap vanishing on $2^k + 2 \le n \le 2^{k+1} - 2$, and the full `iff` non-vanishing locus over integral domains.
- **Prior art & stack:** Carry-less $\mathbb{F} _ 2[x]$ multiplication and Sylvester Hadamard matrices are classical; no prior literature or OEIS match found for this locus or determinant family. Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 16. [`zero-carry-spanning-trees/`](zero-carry-spanning-trees/) — **86 / 100**
- **Plain English:** Exact closed-form count of minimal wiring layouts (spanning trees) for networks linking binary or mixed-radix IDs that add with zero carries.
- **For Mathematicians:** Kronecker reversed-Pascal triangularization yields the exact alternating-harmonic spectrum of mixed-radix zero-carry transition matrices over $\mathbb{Q}$ and Kirchhoff cofactor counts over any commutative ring $R$, specializing to $\tau(G _ {2^k}) = \prod _ {m=2}^k (2^m - (-1)^m)^{\binom{k}{m}}$ for `i &&& j = 0`.
- **Prior art & stack:** Single-radix $k = 1$ is a threshold graph (Hammer & Kelmans 1996); for $k \ge 2$, $G _ b$ contains induced $P _ 4$ (non-cograph) and $3, 243, 71744535, \dots$ is absent from OEIS. Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 17. [`arx-fibonacci-isospectrality/`](arx-fibonacci-isospectrality/) — **84 / 100**
- **Plain English:** Mixing a secret $m$-bit XOR key $c$ into a modular Fibonacci counter $(x, y) \to (y,\; x + (y \oplus c)) \bmod 2^m$ cannot change a single cycle length — every single key produces the exact same loop sizes as unkeyed Fibonacci, though changing $x$ to $3x$ breaks it immediately on 2-bit numbers.
- **For Mathematicians:** Exact finite-level 2-adic perturbation law $((y + 2^r) \oplus c) \equiv (y \oplus c) + \sigma _ r \cdot 2^r \pmod{2^{r+2}}$ ($\sigma _ r \in \{1, 3\}$) and linearized Jacobian lifting prove that every non-fixed $(x, y)$ has exact minimal period $3 \cdot 2^{m - 1 - r _ 0}$, making $(x, y) \mapsto (x \oplus c, y \oplus c)$ an exact period-preserving involution (though not a conjugacy) between $G _ {c,m}$ and $G _ {0,m}$, with a sharp $m = 2$ failure witness for $3x + (y \oplus c)$.
- **Prior art & stack:** Builds on 2-adic differentiability of XOR (Anashin `0409422`, Anashin–Khrennikov 2009), T-functions (Klimov–Shamir 2002/2004), and unkeyed Pisano periods (Wall 1960); no prior publication found for key-invariant ARX Fibonacci cycle spectra. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 18. [`skew-thue-morse-pfaffian/`](skew-thue-morse-pfaffian/) — **84 / 100**
- **Plain English:** Mirror-antisymmetric Thue–Morse sign grids collapse to determinant **exactly $1$** at every even size across shifts $s \in \{0, 1, 2\}$ (jumping to $9$ at $s = 3$) and $0$ at every odd size.
- **For Mathematicians:** Half-swap involution Schur annihilation ($B^T A _ N^{-1} B = 0$) and a rank-1 null-vector bridge prove $\det(A _ {2m}^{(s)}) = 1$ for $s \in \{0, 1, 2\}$ and $\det(A _ {2m+1}^{(s)}) = 0$ for all $s, m$ over every commutative ring $R$ (including char $2$), where $(A _ n^{(s)}) _ {i,j} = \mathrm{sgn}(j - i)(-1)^{s _ 2(i + j + s)}$.
- **Prior art & stack:** Symmetric Thue–Morse Hankel determinants (APWW 1998; OEIS A186026) grow as nontrivial powers of $2$; no prior publication or OEIS match found for skew-symmetric unimodularity. Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 19. [`bitrev-increment-cycles/`](bitrev-increment-cycles/) — **82 / 100**
- **Plain English:** Repeatedly reversing $k$ bits and adding $1$ sweeps **all** $2^k$ states in one cycle iff $k$ is odd, but collapses to a tiny square-root-length loop ($2^{m+2} - 1$) for every even $k = 2(m+1)$.
- **For Mathematicians:** Complete odd/even Hamiltonian-cycle dichotomy for $f _ k(x) = (\mathrm{bitrev} _ k(x) + 1) \bmod 2^k$ proved via an exact $3/4/5$-step $k \to k + 2$ return-map renormalization law on the slice $(0, m, 0)$.
- **Prior art & stack:** Bit-reversal is standard in radix-2 FFT / Van der Corput constructions; no prior proof of this parity dichotomy or return-map law found in the literature or OEIS. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 20. [`carry-determinants/`](carry-determinants/) — **82 / 100**
- **Plain English:** Mixed-radix addition carry tables have nonzero determinant iff $n - 1$ uses only extremal digits (a Cantor-set pattern), and factor cleanly into products unifying Kummer $p$-adic and Thue–Morse determinants.
- **For Mathematicians:** Cantor extremal-digit `iff` non-vanishing characterization and division-free multivariate mixed-radix Hankel/carry factorizations over arbitrary commutative rings $R$, with corollaries for `(i + j) ^^^ i ^^^ j`, $v _ p\binom{i+j}{i}$, weighted linear carries, and $\det((-1)^{s _ 2(i+j)}) _ {2^k} = 2^{2^k - 1}$.
- **Prior art & stack:** Base-$2$ specializations overlap with Bacher & Chapman (2004), Bacher (2007), APWW (1998), and Sobolewski & Ulas (2026, `2607.09376`); mixed-radix Cantor characterization and multivariate exponential formulas extend them. Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 21. [`weak-bruhat-commutators/`](weak-bruhat-commutators/) — **77 / 100**
- **Plain English:** Running stack-sort or pop-stack-sort **before** $k$ bubble-sort passes always leaves cards at least as sorted as running them **after**, for every deck and every $k$.
- **For Mathematicians:** Introduces the Bubble-Refined Order ($\preceq _ B$: value-inversion inclusion plus descent-bottom inclusion), proves $\preceq _ B$-monotonicity of $B$, and establishes all-$k$ commutators $B^k(S(xs)) \preceq _ B S(B^k(xs))$ and $B^k(P(xs)) \preceq _ B P(B^k(xs))$ with inversion and descent corollaries.
- **Prior art & stack:** Builds on Knuth (TAOCP Vol. 3, §5.2.2), West (1990), Ungar (1982), Chung–Claesson–Dukes–Graham (2010), Albert et al. (`1008.5299`), and Defant (`2104.02675`, `2104.03215`). Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 22. [`carry-blocks-determinants/`](carry-blocks-determinants/) — **73 / 100**
- **Plain English:** Tables counting separate carry streaks in mixed-radix addition always have determinant $\pm 1$, alongside a plateau rule where determinants ignore the top-left corner and an exact XOR bit-length formula.
- **For Mathematicians:** Division-free determinant formulas over arbitrary commutative rings $R$ for exponential and linear mixed-radix carry-blocks, binary Gray-code carry transitions, 0-based and 1-based plateau Hankel matrices, mixed-radix digit lengths, and shifted ultrametric matrices $(\mathrm{bitlen}(i \oplus j) + t) _ {2^k}$.
- **Prior art & stack:** Carry-blocks build on `carry-determinants/`; `bitlen(i ^^^ j)` sits in the classical tree-distance / ultrametric / $(\mathbb{Z}/2\mathbb{Z})^k$-circulant lineage (Graham & Pollak 1971; Martínez–Michon–San Martín 1994; Nabben & Varga 1994). Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 23. [`grh-ultra-compact-lean/`](grh-ultra-compact-lean/) — **71 / 100**
- **Plain English:** Compresses the already-short `grh-compact` Lean 4 formalization of the Riemann Hypothesis and Dirichlet GRH from `796` files (`76,166` lines of code, `112,854` total lines) down to **`490` files and `53,691` lines of pure code (`54,986` total lines)** without altering a single byte of the theorem statements.
- **For Mathematicians:** Source-compacted derivative of `lsernau/grh-lean` (`grh-compact`, commit `72fead10`) proving Mathlib's `RiemannHypothesis` and critical-strip zero localization $\mathrm{Re}(s) = 1/2$ for all Dirichlet $L$-functions $L(s, \chi)$ ($N \ge 1$), achieving `-38.44%` modules, `-29.51%` pure LoC, and `-51.28%` total lines with `src/Statements.lean`, `Challenge.lean`, `src/Main.lean`, and `comparator.json` preserved byte-for-byte unchanged.
- **Prior art & stack:** Strictly derived from `lsernau/grh-lean` (`grh-compact/`, Apache-2.0, Copyright 2026 Anthropic, PBC; mathematical proof by Levent Alpöge, formalized with Claude; see <https://alpo.ge/remark.pdf>). Lean `v4.35.0` / Mathlib `56a005855ea` (`propext`, `Classical.choice`, `Quot.sound`).

### 24. [`combinatorial-inequalities/`](combinatorial-inequalities/) — **66 / 100**
- **Plain English:** Four universal "speed limits" on stack-sorting, permutation displacement, and integer difference sets proved for every size without exception.
- **For Mathematicians:** Four universal bounds for all $n, N \in \mathbb{N}$: $3\,\mathrm{inv}(S^2(p)) \le \mathrm{pat} _ {231}(p)$ on $\mathrm{Av}(321)$, $\mathrm{des}(S(p)) \le \mathrm{peaks}(p)$, $2\,\mathrm{inv}(p) \le \mathrm{disp2}(p) + \mathrm{des}(p)(\mathrm{des}(p) + 1)$ on $\mathrm{Av}(231)$, and $3|A - A| \le 2|2A - A| + 1$.
- **Prior art & stack:** Adjacent to West (1990), Zeilberger (1992), Defant (`1809.03123`), Diaconis & Graham (1977), and Freiman / Ruzsa / Bukh sumset-dilate bounds. Lean `v4.34.1` / pure `Std` (`propext`, `Classical.choice`, `Quot.sound`).

### 25. [`sorting-operators/`](sorting-operators/) — **61 / 100**
- **Plain English:** One pass of stack-sort always beats or ties one pass of bubble-sort on every list, producing the exact same output whenever there is no 3-step decreasing chain.
- **For Mathematicians:** Constructive cross-operator comparison of West stack-sort $S$ and single-pass bubble sort $B$: $\mathrm{inv}(S) \le \mathrm{inv}(B)$, $\mathrm{des}(S) \le \mathrm{des}(B)$, $S = B$ on $\mathrm{Av}(321)$ with strictness witness `[2, 1, 3, 0]`, and $\mathrm{inv}(B) \le \mathrm{pat} _ {321} + \mathrm{pat} _ {231}$.
- **Prior art & stack:** Adjacent to West (1990), Chung–Claesson–Dukes–Graham (2010), Albert et al. (`1008.5299`), and Defant (`1809.03123`, `2104.02675`). Lean `v4.34.1` / pure `Init` (`propext`, `Quot.sound` only — no `Classical.choice`).

## Navigating the collection

- Use [CONTENTS.md](CONTENTS.md) for a theorem-by-theorem map across all 25 projects.
- Inside each project folder:
  - Read `README.md` for its **Synthetic Score**, **For Mathematicians** summary, **For Non-Mathematicians** plain-English overview, and prior-art citations.
  - Read `Challenge.lean` (and its small definitions module) to inspect the exact statements being proved without reading any proof code.
  - Read `Solution.lean` and `AUDIT.md` for the verification record, verbatim `#print axioms` output, and reproduction commands.

## How the results were produced

These results were explored computationally using binary arithmetic, formalized universally in Lean 4 without `sorry` or custom axioms, checked with `lake build` and `#print axioms`, and paired with Palomar `Challenge.lean` / `Solution.lean` comparator configurations.

These projects are shared as verified research artifacts. Each project's `README.md` documents the closest known prior art we are aware of. We defer to the mathematics community on matters of credit, precedence, and concurrent work—if any statement duplicates or is subsumed by an earlier result in the literature, please open an issue so we can add the citation or prune it.

## CI

Pull requests and pushes to `main` run [`.github/workflows/lean-projects.yml`](.github/workflows/lean-projects.yml) on each changed project directory. Each project passes when `lake build` succeeds on its pinned toolchain with no `sorry` outside `Challenge.lean`, and when `leanprover/comparator` with `lean4export`, the independent `nanoda` kernel, and `landrun` accepts every `comparator.json` configuration ([`.github/scripts/comparator-check.sh`](.github/scripts/comparator-check.sh)).

## License

Apache-2.0. See [LICENSE](LICENSE).
