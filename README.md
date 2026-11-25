# math-research

Machine-checked Lean 4 formalizations of mathematical results discovered through binary math at MoteMath.

Each subdirectory is a self-contained Lake project with its own toolchain pin, `README.md`, `AUDIT.md`, and build instructions; build from inside the subdirectory. Projects follow the [Palomar](https://palomar-registry.org/) submission layout (`Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml` at each project root).

| Project | Summary of Results | Lean / Mathlib | Axioms |
|---|---|---|---|
| [`carry-determinants/`](carry-determinants/) | Cantor non-vanishing characterization and exact closed-form multivariate determinant factorizations for mixed-radix Hankel and carry matrices over any commutative ring, with corollaries for the binary carry-word matrix `det((i + j) ^^^ i ^^^ j)`, the $p$-adic Kummer binomial valuation matrix, weighted linear carry matrices, and the power-of-two Thue-Morse Hankel matrix | `leanprover/lean4:v4.34.1` / Mathlib `v4.34.1` | `propext`, `Classical.choice`, `Quot.sound` |
| [`combinatorial-inequalities/`](combinatorial-inequalities/) | 23 universally quantified combinatorial theorem clusters proved for all $n, N \in \mathbb{N}$: West stack vs. pop-stack inversion dominance, sharp factor-3 two-stack bound on $\mathrm{Av}(321)$, stack descents vs. input peaks, reflection-asymmetry and difference-folding bounds for integer subsets, quantitative graph diameter and irregularity bounds, plus two formal counterexample disproofs | `leanprover/lean4:v4.34.1` / `Std` only (no Mathlib) | `propext`, `Classical.choice`, `Quot.sound` |
| [`bit-circuit-synthesis/`](bit-circuit-synthesis/) | Zero-Mathlib, zero-built-in-arithmetic formalization built directly on canonical binary words (`BBin` / `BPos`) and 1-bit multiplexer gates: `1,799` universal bit-circuit theorems plus universal proofs of carry-less $\mathbb{F} _ 2[x]$ degree additivity, integral-domain closure, carried vs. carry-less degree-jump contrast, Artin-Schreier linearity and fiber pairing, iterated Frobenius trace telescoping, and additive Hilbert's Theorem 90 | `leanprover/lean4:v4.34.1` / `Init` only (no Mathlib) | `propext` only (no `Classical.choice`, no `Quot.sound`) |

## Navigating the collection

- Use [CONTENTS.md](CONTENTS.md) for a theorem-by-theorem map across all projects.
- Inside each project folder:
  - Read `Challenge.lean` (and its small definitions module) to inspect the exact statements being proved without reading any proof code.
  - Read `Solution.lean` and `AUDIT.md` for the verification record, verbatim `#print axioms` output, and reproduction commands.

## How the results were produced

These results were discovered through binary math and formalized universally in Lean 4 without `sorry` or custom axioms, checked with `lake build` and `#print axioms`, and paired with Palomar `Challenge.lean` / `Solution.lean` comparator configurations.

These projects are shared as research artifacts. We defer to the mathematics community on matters of credit, precedence, and concurrent work. If any statement duplicates an earlier result in the literature, please open an issue so we can add the citation.

## CI

Pull requests and pushes to `main` run [`.github/workflows/lean-projects.yml`](.github/workflows/lean-projects.yml) on each changed project directory. Each project passes when `lake build` succeeds on its pinned toolchain with no `sorry` outside `Challenge.lean`, and when `leanprover/comparator` with `lean4export`, the independent `nanoda` kernel, and `landrun` accepts every `comparator.json` configuration ([`.github/scripts/comparator-check.sh`](.github/scripts/comparator-check.sh)).

## License

Apache-2.0. See [LICENSE](LICENSE).
