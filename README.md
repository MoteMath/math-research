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
| [`sparse-e2m1-rotations/`](sparse-e2m1-rotations/) | 9 | 9 | 9 | 8 | 10 | **89** |
| [`muon-vertex-polar/`](muon-vertex-polar/) | 9 | 9 | 8 | 9 | 10 | **89** |
| [`ternary-lop3-circuits/`](ternary-lop3-circuits/) | 9 | 9 | 8 | 9 | 10 | **89** |
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

### 1. [`sparse-e2m1-rotations/`](sparse-e2m1-rotations/) — **89 / 100**
- **Plain English:** Proves an exact 2-step **2:4-sparse** factorization of every Walsh–Hadamard matrix (matching modern GPU sparse Tensor Cores at 2× speed with zero error) and constructs exact 4-bit-native (E2M1) orthogonal rotations that beat dense Hadamard by up to `+5.4 dB` on heavy-tailed LLM outliers.
- **For Mathematicians:** Universal doubly-2:4-sparse $\{-1, 0, 1\}$ orthogonal factorization $(H _ {2^k} \otimes B _ 1)(I _ {2^k} \otimes B _ 2) = H _ {4 \cdot 2^k}$ for all $k \in \mathbb{N}$, universal single-2:4 coherence lower bound $2c \le (4m) M^2$ attained by $W _ {4 \cdot 2^k} = H _ {2^k} \otimes B _ 1$, universal skew-conference E2M1 orthogonality $(a I + C)^T (a I + C) = (a^2 + n - 1) I$, exact power-of-2 E2M1-native $Q _ {32} = H _ 4 \otimes (I _ 8 + 3 C _ 8)$ ($Q _ {32}^T Q _ {32} = 16^2 I _ {32}$), NVFP4 winner $Q _ {16} = 4 I _ {16} + C _ {16}$ ($c = 31$), and universal doubly-2:4-sparse E2M1 family $G _ {4 \cdot 2^k}(1, 2)$.
- **Prior art & stack:** Builds on Sylvester/Walsh–Hadamard, Paley skew-conference matrices, QuIP#/QuaRot/MR-GPTQ/DuQuant++, and 2:4 structured sparsity; no prior publication found for the doubly-2:4-sparse Hadamard factorization or E2M1-native skew-conference rotations. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 2. [`muon-vertex-polar/`](muon-vertex-polar/) — **89 / 100**
- **Plain English:** Rewriting the Muon AI optimizer's 5th-degree matrix-orthogonalization polynomial into a positive "shifted-square" vertex form eliminates low-precision cancellation at the exact same compute cost — making BF16 updates up to `139×` tighter and delivering the first provably safe FP8 E4M3 polar schedules.
- **For Mathematicians:** Proves the shifted-square identity $a x + b x^3 + c x^5 = x(\alpha + c(x^2 - \mu)^2)$ and exact quadratic Gram rounding-error annihilation $O(\beta u^2)$ vs monomial linear error $(b + 2c)\delta _ 1$, derives exact pointwise degree-5 envelopes for the 6-rounding-point `NoisyShiftedStep` model, and certifies continuous 5-step trajectory confinement of $[1/100, 1]$ via cleared-denominator homogeneous degree-5 Bernstein certificates in BF16 ($u = 1/256$: stationary `[0.942, 1.052]`, DP `[0.987, 1.013]`), pure FP8 E4M3 ($u = 1/16$: `[0.31, 1.65]`), and hybrid FP8 ($u = 1/32$: `[0.824, 1.163]`).
- **Prior art & stack:** Builds on Jordan (2024) Muon and Amsel et al. (2025, `2505.16932`) Polar Express; no prior publication found for the vertex-form quadratic error-annihilation theorem or kernel-certified BF16/FP8 E4M3 polar schedules. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 3. [`ternary-lop3-circuits/`](ternary-lop3-circuits/) — **89 / 100**
- **Plain English:** Proves exact minimum-gate bitwise GPU circuits that unpack tightly compressed 1.58-bit BitNet ternary weights using zero multiplications, divisions, or lookup tables — saving 16.7%–20% memory bandwidth while running faster on real GPUs — plus exact zero-FP ternary×INT4/FP4 dot-product circuits.
- **For Mathematicians:** Synthesizes and proves soundness + surjectivity of a **6-`LOP3` depth-2** 3-trit/5-bit unpacker (with an exact pigeonhole lower bound proving no input literal pass-through is possible, $18 > 16$, plus a 4-codeword escape cube still covering all $27$ triples) and a **14-`LOP3` depth-4** 5-trit/8-bit unpacker (with an exact weight-divisibility lower bound proving no output lane can depend on $\le 4$ inputs, since $[81, 94] \cap 16\mathbb{Z} = \emptyset$), alongside exact 9-`LOP3` ternary×INT4, 4+10-`LOP3` zero-offset ternary×FP4 (E2M1), and universal 3:2 CSA `popcnt` conservation over all $a, b, c \in \mathbb{N}$.
- **Prior art & stack:** Builds on BitNet b1.58 (Ma et al. 2024), T-MAC (Wei et al. 2024), GPU `LOP3` instructions, and Harley–Seal CSA trees; no prior publication found for these co-designed minimal-`LOP3` encodings, lower bounds, or zero-FP E2M1 dot circuits. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 4. [`binary-lyness-periods/`](binary-lyness-periods/) — **89 / 100**
- **Plain English:** Repeating $(x, y) \to (y,\; x \oplus (y + 2^r))$ on **any** two whole numbers — no matter how huge — always snaps back to where you started after **exactly $6$ steps** (and this works **only** when the constant is $0$ or a power of $2$), while its bitwise-OR twin $(y,\; x \oplus (y \mathbin{|} (y + 2^r)))$ always snaps back in **exactly $12$ steps**.
- **For Mathematicians:** General XOR-Feistel carry-renormalization laws on unbounded $\mathbb{N} \times \mathbb{N}$: $f(2k) = 2k + 1, f(2k + 1) = 2h(k)$ forces $F _ f^6 = \mathrm{id}$ off odd-odd states via exact $F _ f^3$-invariance of $a \oplus b$, and $f(2k + 1) = 2g(k) + 1$ forces $F _ f^{12} = \mathrm{id}$ globally via conjugacy of $F _ f^4$ to $\mathbb{F} _ 2$-Fibonacci; implies $F _ c^6 = \mathrm{id} \iff c = 0 \lor \exists r,\, c = 2^r$ and $H _ {2^r}^{12} = \mathrm{id}$ for all $r$.
- **Prior art & stack:** Echoes classical rational Lyness recurrences (Lyness 1942) and contrasts with addition *outside* XOR (MathOverflow *"A Bitwise Xor Problem"*); no prior publication or OEIS match found for these laws or dichotomy. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 5. [`clmul-lift-determinants/`](clmul-lift-determinants/) — **88 / 100**
- **Plain English:** Odd carry-less multiplication tables have determinant $0$ almost everywhere — except right next to powers of $2$ ($2^k - 1, 2^k, 2^k + 1$), where they snap to exact powers of $2$ via a hidden bit-reversed Hadamard matrix.
- **For Mathematicians:** Division-free polynomial Schur reduction of $(M _ n(t)) _ {i,j} = \mathrm{lift} _ {\mathbb{Z}}(P _ {2i+1} \cdot _ {\mathbb{F} _ 2[x]} P _ {2j+1})(t)$ to $(-2 t^{k+1}) H _ {k,m}^{\mathrm{rev}}$ over any commutative ring $R$, yielding exact single-monomial determinants at $n \in \{2^k - 1, 2^k, 2^k + 1\}$, identical gap vanishing on $2^k + 2 \le n \le 2^{k+1} - 2$, and the full `iff` non-vanishing locus over integral domains.
- **Prior art & stack:** Carry-less $\mathbb{F} _ 2[x]$ multiplication and Sylvester Hadamard matrices are classical; no prior literature or OEIS match found for this locus or determinant family. Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 6. [`zero-carry-spanning-trees/`](zero-carry-spanning-trees/) — **86 / 100**
- **Plain English:** Exact closed-form count of minimal wiring layouts (spanning trees) for networks linking binary or mixed-radix IDs that add with zero carries.
- **For Mathematicians:** Kronecker reversed-Pascal triangularization yields the exact alternating-harmonic spectrum of mixed-radix zero-carry transition matrices over $\mathbb{Q}$ and Kirchhoff cofactor counts over any commutative ring $R$, specializing to $\tau(G _ {2^k}) = \prod _ {m=2}^k (2^m - (-1)^m)^{\binom{k}{m}}$ for `i &&& j = 0`.
- **Prior art & stack:** Single-radix $k = 1$ is a threshold graph (Hammer & Kelmans 1996); for $k \ge 2$, $G _ b$ contains induced $P _ 4$ (non-cograph) and $3, 243, 71744535, \dots$ is absent from OEIS. Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 7. [`arx-fibonacci-isospectrality/`](arx-fibonacci-isospectrality/) — **84 / 100**
- **Plain English:** Mixing a secret $m$-bit XOR key $c$ into a modular Fibonacci counter $(x, y) \to (y,\; x + (y \oplus c)) \bmod 2^m$ cannot change a single cycle length — every single key produces the exact same loop sizes as unkeyed Fibonacci, though changing $x$ to $3x$ breaks it immediately on 2-bit numbers.
- **For Mathematicians:** Exact finite-level 2-adic perturbation law $((y + 2^r) \oplus c) \equiv (y \oplus c) + \sigma _ r \cdot 2^r \pmod{2^{r+2}}$ ($\sigma _ r \in \{1, 3\}$) and linearized Jacobian lifting prove that every non-fixed $(x, y)$ has exact minimal period $3 \cdot 2^{m - 1 - r _ 0}$, making $(x, y) \mapsto (x \oplus c, y \oplus c)$ an exact period-preserving involution (though not a conjugacy) between $G _ {c,m}$ and $G _ {0,m}$, with a sharp $m = 2$ failure witness for $3x + (y \oplus c)$.
- **Prior art & stack:** Builds on 2-adic differentiability of XOR (Anashin `0409422`, Anashin–Khrennikov 2009), T-functions (Klimov–Shamir 2002/2004), and unkeyed Pisano periods (Wall 1960); no prior publication found for key-invariant ARX Fibonacci cycle spectra. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 8. [`skew-thue-morse-pfaffian/`](skew-thue-morse-pfaffian/) — **84 / 100**
- **Plain English:** Mirror-antisymmetric Thue–Morse sign grids collapse to determinant **exactly $1$** at every even size across shifts $s \in \{0, 1, 2\}$ (jumping to $9$ at $s = 3$) and $0$ at every odd size.
- **For Mathematicians:** Half-swap involution Schur annihilation ($B^T A _ N^{-1} B = 0$) and a rank-1 null-vector bridge prove $\det(A _ {2m}^{(s)}) = 1$ for $s \in \{0, 1, 2\}$ and $\det(A _ {2m+1}^{(s)}) = 0$ for all $s, m$ over every commutative ring $R$ (including char $2$), where $(A _ n^{(s)}) _ {i,j} = \mathrm{sgn}(j - i)(-1)^{s _ 2(i + j + s)}$.
- **Prior art & stack:** Symmetric Thue–Morse Hankel determinants (APWW 1998; OEIS A186026) grow as nontrivial powers of $2$; no prior publication or OEIS match found for skew-symmetric unimodularity. Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 9. [`bitrev-increment-cycles/`](bitrev-increment-cycles/) — **82 / 100**
- **Plain English:** Repeatedly reversing $k$ bits and adding $1$ sweeps **all** $2^k$ states in one cycle iff $k$ is odd, but collapses to a tiny square-root-length loop ($2^{m+2} - 1$) for every even $k = 2(m+1)$.
- **For Mathematicians:** Complete odd/even Hamiltonian-cycle dichotomy for $f _ k(x) = (\mathrm{bitrev} _ k(x) + 1) \bmod 2^k$ proved via an exact $3/4/5$-step $k \to k + 2$ return-map renormalization law on the slice $(0, m, 0)$.
- **Prior art & stack:** Bit-reversal is standard in radix-2 FFT / Van der Corput constructions; no prior proof of this parity dichotomy or return-map law found in the literature or OEIS. Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 10. [`carry-determinants/`](carry-determinants/) — **82 / 100**
- **Plain English:** Mixed-radix addition carry tables have nonzero determinant iff $n - 1$ uses only extremal digits (a Cantor-set pattern), and factor cleanly into products unifying Kummer $p$-adic and Thue–Morse determinants.
- **For Mathematicians:** Cantor extremal-digit `iff` non-vanishing characterization and division-free multivariate mixed-radix Hankel/carry factorizations over arbitrary commutative rings $R$, with corollaries for `(i + j) ^^^ i ^^^ j`, $v _ p\binom{i+j}{i}$, weighted linear carries, and $\det((-1)^{s _ 2(i+j)}) _ {2^k} = 2^{2^k - 1}$.
- **Prior art & stack:** Base-$2$ specializations overlap with Bacher & Chapman (2004), Bacher (2007), APWW (1998), and Sobolewski & Ulas (2026, `2607.09376`); mixed-radix Cantor characterization and multivariate exponential formulas extend them. Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 11. [`weak-bruhat-commutators/`](weak-bruhat-commutators/) — **77 / 100**
- **Plain English:** Running stack-sort or pop-stack-sort **before** $k$ bubble-sort passes always leaves cards at least as sorted as running them **after**, for every deck and every $k$.
- **For Mathematicians:** Introduces the Bubble-Refined Order ($\preceq _ B$: value-inversion inclusion plus descent-bottom inclusion), proves $\preceq _ B$-monotonicity of $B$, and establishes all-$k$ commutators $B^k(S(xs)) \preceq _ B S(B^k(xs))$ and $B^k(P(xs)) \preceq _ B P(B^k(xs))$ with inversion and descent corollaries.
- **Prior art & stack:** Builds on Knuth (TAOCP Vol. 3, §5.2.2), West (1990), Ungar (1982), Chung–Claesson–Dukes–Graham (2010), Albert et al. (`1008.5299`), and Defant (`2104.02675`, `2104.03215`). Lean `v4.34.1` / pure `Init` (`propext`, `Classical.choice`, `Quot.sound`).

### 12. [`carry-blocks-determinants/`](carry-blocks-determinants/) — **73 / 100**
- **Plain English:** Tables counting separate carry streaks in mixed-radix addition always have determinant $\pm 1$, alongside a plateau rule where determinants ignore the top-left corner and an exact XOR bit-length formula.
- **For Mathematicians:** Division-free determinant formulas over arbitrary commutative rings $R$ for exponential and linear mixed-radix carry-blocks, binary Gray-code carry transitions, 0-based and 1-based plateau Hankel matrices, mixed-radix digit lengths, and shifted ultrametric matrices $(\mathrm{bitlen}(i \oplus j) + t) _ {2^k}$.
- **Prior art & stack:** Carry-blocks build on `carry-determinants/`; `bitlen(i ^^^ j)` sits in the classical tree-distance / ultrametric / $(\mathbb{Z}/2\mathbb{Z})^k$-circulant lineage (Graham & Pollak 1971; Martínez–Michon–San Martín 1994; Nabben & Varga 1994). Lean `v4.34.1` / Mathlib (`propext`, `Classical.choice`, `Quot.sound`).

### 13. [`grh-ultra-compact-lean/`](grh-ultra-compact-lean/) — **71 / 100**
- **Plain English:** Compresses the already-short `grh-compact` Lean 4 formalization of the Riemann Hypothesis and Dirichlet GRH from `796` files (`76,166` lines of code, `112,854` total lines) down to **`490` files and `53,691` lines of pure code (`54,986` total lines)** without altering a single byte of the theorem statements.
- **For Mathematicians:** Source-compacted derivative of `lsernau/grh-lean` (`grh-compact`, commit `72fead10`) proving Mathlib's `RiemannHypothesis` and critical-strip zero localization $\mathrm{Re}(s) = 1/2$ for all Dirichlet $L$-functions $L(s, \chi)$ ($N \ge 1$), achieving `-38.44%` modules, `-29.51%` pure LoC, and `-51.28%` total lines with `src/Statements.lean`, `Challenge.lean`, `src/Main.lean`, and `comparator.json` preserved byte-for-byte unchanged.
- **Prior art & stack:** Strictly derived from `lsernau/grh-lean` (`grh-compact/`, Apache-2.0, Copyright 2026 Anthropic, PBC; mathematical proof by Levent Alpöge, formalized with Claude; see <https://alpo.ge/remark.pdf>). Lean `v4.35.0` / Mathlib `56a005855ea` (`propext`, `Classical.choice`, `Quot.sound`).

### 14. [`combinatorial-inequalities/`](combinatorial-inequalities/) — **66 / 100**
- **Plain English:** Four universal "speed limits" on stack-sorting, permutation displacement, and integer difference sets proved for every size without exception.
- **For Mathematicians:** Four universal bounds for all $n, N \in \mathbb{N}$: $3\,\mathrm{inv}(S^2(p)) \le \mathrm{pat} _ {231}(p)$ on $\mathrm{Av}(321)$, $\mathrm{des}(S(p)) \le \mathrm{peaks}(p)$, $2\,\mathrm{inv}(p) \le \mathrm{disp2}(p) + \mathrm{des}(p)(\mathrm{des}(p) + 1)$ on $\mathrm{Av}(231)$, and $3|A - A| \le 2|2A - A| + 1$.
- **Prior art & stack:** Adjacent to West (1990), Zeilberger (1992), Defant (`1809.03123`), Diaconis & Graham (1977), and Freiman / Ruzsa / Bukh sumset-dilate bounds. Lean `v4.34.1` / pure `Std` (`propext`, `Classical.choice`, `Quot.sound`).

### 15. [`sorting-operators/`](sorting-operators/) — **61 / 100**
- **Plain English:** One pass of stack-sort always beats or ties one pass of bubble-sort on every list, producing the exact same output whenever there is no 3-step decreasing chain.
- **For Mathematicians:** Constructive cross-operator comparison of West stack-sort $S$ and single-pass bubble sort $B$: $\mathrm{inv}(S) \le \mathrm{inv}(B)$, $\mathrm{des}(S) \le \mathrm{des}(B)$, $S = B$ on $\mathrm{Av}(321)$ with strictness witness `[2, 1, 3, 0]`, and $\mathrm{inv}(B) \le \mathrm{pat} _ {321} + \mathrm{pat} _ {231}$.
- **Prior art & stack:** Adjacent to West (1990), Chung–Claesson–Dukes–Graham (2010), Albert et al. (`1008.5299`), and Defant (`1809.03123`, `2104.02675`). Lean `v4.34.1` / pure `Init` (`propext`, `Quot.sound` only — no `Classical.choice`).

## Navigating the collection

- Use [CONTENTS.md](CONTENTS.md) for a theorem-by-theorem map across all 15 projects.
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
