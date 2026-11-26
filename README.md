# math-research

Machine-checked Lean 4 formalizations of exact determinant factorizations and combinatorial inequalities developed at MoteMath.

Each subdirectory is a self-contained Lake project with its own toolchain pin, `README.md`, `AUDIT.md`, and build instructions; build from inside the subdirectory. Projects follow the [Palomar](https://palomar-registry.org/) submission layout (`Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml` at each project root).

| Project | Summary of Results | Closest Prior Art | Lean / Mathlib | Axioms |
|---|---|---|---|---|
| [`carry-determinants/`](carry-determinants/) | Cantor extremal-digit non-vanishing characterization (base $B \ge 2$ and mixed radix) and closed-form multivariate determinant factorizations for mixed-radix multiplicative Hankel and carry matrices over arbitrary commutative rings, with corollaries for `det((i + j) ^^^ i ^^^ j)`, the $p$-adic Kummer matrix $v _ p\binom{i+j}{i}$, weighted linear carry matrices, and the power-of-two Thue-Morse Hankel determinant $2^{2^k - 1}$ | Bacher & Chapman (2004, `math/0212144`) and Bacher (`0708.1430`) cover the base-$2$ specializations $X = 0, i$; Sobolewski & Ulas (2026, `2607.09376`) prove an algebraically equivalent base-$2$ additive formula covering $p = 2$ Kummer; APWW (1998) and OEIS A186026 study Thue-Morse Hankel determinants mod $2$ | `leanprover/lean4:v4.34.1` / Mathlib `v4.34.1` | `propext`, `Classical.choice`, `Quot.sound` |
| [`carry-blocks-determinants/`](carry-blocks-determinants/) | Closed-form determinant families over arbitrary commutative rings: exponential and linear mixed-radix carry-blocks matrices, binary Gray-code carry-transition matrices, 0-based and 1-based plateau Hankel matrices (with mixed-radix digit-length corollaries), and ultrametric XOR bit-length matrices | Builds on mixed-radix carry reductions; `bitlen(i ^^^ j)` is a $(\mathbb{Z}/2\mathbb{Z})^k$-circulant (Walsh-Hadamard) matrix and half the leaf-distance matrix of a complete binary tree (cf. Graham & Pollak 1971; Martínez–Michon–San Martín 1994; Nabben & Varga 1994) | `leanprover/lean4:v4.34.1` / Mathlib `v4.34.1` | `propext`, `Classical.choice`, `Quot.sound` |
| [`combinatorial-inequalities/`](combinatorial-inequalities/) | Four universally quantified permutation and additive-set inequalities proved for all $n, N \in \mathbb{N}$: the sharp factor-3 two-stack bound $3\,\mathrm{inv}(S^2(p)) \le \mathrm{pat} _ {231}(p)$ on $\mathrm{Av}(321)$, $\mathrm{des}(S(p)) \le \mathrm{peaks}(p)$, a quadratic descent-excess Spearman bound on $\mathrm{Av}(231)$, and $3|A - A| \le 2|2A - A| + 1$ | West (1990), Zeilberger (1992), and Defant (`1809.03123`) for stack-sorting; Diaconis & Graham (1977) for Spearman displacement vs. inversions; Freiman / Ruzsa / Bukh sumset-dilate bounds | `leanprover/lean4:v4.34.1` / `Std` only (no Mathlib) | `propext`, `Classical.choice`, `Quot.sound` |
| [`sorting-operators/`](sorting-operators/) | Cross-operator inequalities and identities relating West's stack-sorting operator $S$ and single-pass bubble sort $B$: $\mathrm{inv}(S) \le \mathrm{inv}(B)$, $\mathrm{des}(S) \le \mathrm{des}(B)$, coincidence $S = B$ on $\mathrm{Av}(321)$ with an explicit strictness witness, and $\mathrm{inv}(B) \le \mathrm{pat} _ {321} + \mathrm{pat} _ {231}$ | West (1990), Chung–Claesson–Dukes–Graham (2010), Albert–Atkinson–Bouvel–Claesson–Dukes (2011, `1008.5299`), and Defant (`1809.03123`, `2104.02675`) | `leanprover/lean4:v4.34.1` / `Init` only (no Mathlib) | `propext`, `Quot.sound` (no `Classical.choice`) |
| [`zero-carry-spanning-trees/`](zero-carry-spanning-trees/) | Alternating-harmonic spectrum of mixed-radix zero-carry transition matrices via Kronecker-Pascal triangularization, and exact Kirchhoff spanning-tree formulas over arbitrary commutative rings, specializing to the binary bitwise-disjoint (`i &&& j = 0`) graph count $\tau(G _ {2^k}) = \prod _ {m=2}^k (2^m - (-1)^m)^{\binom{k}{m}}$ | Single-radix $k = 1$ case is a threshold graph (Hammer & Kelmans 1996); for $k \ge 2$, $G _ b$ contains induced $P _ 4$ (non-cograph) and the binary sequence $3, 243, 71744535, \dots$ does not appear in OEIS | `leanprover/lean4:v4.34.1` / Mathlib `v4.34.1` | `propext`, `Classical.choice`, `Quot.sound` |
| [`bitrev-increment-cycles/`](bitrev-increment-cycles/) | Exact parity dichotomy for $f _ k(x) = (\mathrm{bitrev} _ k(x) + 1) \bmod 2^k$: single full-period Hamiltonian cycle of length $2^k$ iff $k$ is odd, exact minimal orbit period $2^{m+2} - 1$ of $0$ for even $k = 2(m + 1)$, and the $3/4/5$-step $k \to k + 2$ return-map renormalization law | Bit-reversal involution is standard in radix-2 FFT / Van der Corput constructions; no prior proof of this odd/even Hamiltonian dichotomy or $k \to k + 2$ return-map law found in the literature or OEIS | `leanprover/lean4:v4.34.1` / `Init` only (no Mathlib) | `propext`, `Classical.choice`, `Quot.sound` |

## Navigating the collection

- Use [CONTENTS.md](CONTENTS.md) for a theorem-by-theorem map across all projects.
- Inside each project folder:
  - Read `Challenge.lean` (and its small definitions module) to inspect the exact statements being proved without reading any proof code.
  - Read `README.md` for detailed prior-art citations and scope notes.
  - Read `Solution.lean` and `AUDIT.md` for the verification record, verbatim `#print axioms` output, and reproduction commands.

## How the results were produced

These results were explored computationally using binary arithmetic, formalized universally in Lean 4 without `sorry` or custom axioms, checked with `lake build` and `#print axioms`, and paired with Palomar `Challenge.lean` / `Solution.lean` comparator configurations.

These projects are shared as verified research artifacts. Each project's `README.md` documents the closest known prior art we are aware of. We defer to the mathematics community on matters of credit, precedence, and concurrent work—if any statement duplicates or is subsumed by an earlier result in the literature, please open an issue so we can add the citation or prune it.

## CI

Pull requests and pushes to `main` run [`.github/workflows/lean-projects.yml`](.github/workflows/lean-projects.yml) on each changed project directory. Each project passes when `lake build` succeeds on its pinned toolchain with no `sorry` outside `Challenge.lean`, and when `leanprover/comparator` with `lean4export`, the independent `nanoda` kernel, and `landrun` accepts every `comparator.json` configuration ([`.github/scripts/comparator-check.sh`](.github/scripts/comparator-check.sh)).

## License

Apache-2.0. See [LICENSE](LICENSE).
