# Ultra-Compact Generalized Riemann Hypothesis for Dirichlet L-functions in Lean 4 (`grh-ultra-compact-lean`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **4 / 10** | **6 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **71 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): derivative source-compaction artifact of `lsernau/grh-lean` (`grh-compact`, Apache-2.0, Levent Alpöge & Claude), not a newly discovered mathematical proof (`Nov = 4`). Achieves a verified `-38.44%` reduction in `.lean` modules (`796 -> 490`), `-29.51%` in pure code lines (`76,166 -> 53,691`), and `-51.28%` in total lines (`112,854 -> 54,986`) while preserving `src/Statements.lean`, `Challenge.lean`, `src/Main.lean`, and `comparator.json` byte-for-byte unchanged under Lean `v4.35.0` / Mathlib (`Ver = 9`).*

## For Mathematicians

This project is an aggressively source-compacted Lean `v4.35.0` / Mathlib formalization of the **Riemann Hypothesis** for $\zeta(s)$ and the **Generalized Riemann Hypothesis** for all Dirichlet $L$-functions $L(s, \chi)$ ($N \ge 1$, all $\chi \pmod N$). Every statement in [`src/Statements.lean`](src/Statements.lean) and [`Challenge.lean`](Challenge.lean) — along with the top-level proof exports in [`src/Main.lean`](src/Main.lean), the toolchain pin (`lean-toolchain`), the Mathlib pin (`lake-manifest.json`), and `comparator.json` — is preserved **byte-for-byte unchanged** from upstream `lsernau/grh-lean` (`grh-compact` at `72fead102f663d5c7a407964a13dc0cf9d977207`).

The mathematical architecture is Levent Alpöge's proof (see <https://alpo.ge/remark.pdf>), formalized in `src/Lib` (`383` modules: class field theory, adelic groups, harmonic analysis, Weil representations, $p$-adic Hodge theory, Shimura varieties, and Galois representations; imports nothing from `src/New`) and `src/New` (`103` modules: setup and main argument in `src/New/Main.lean`, establishing `star_inequality`, `eventually_primeError_le_rpow`, and `New.grh`). Our compaction folds single-importer leaf modules, removes dead declarations and redundant scaffolding, and tightens proof terms across 24 disjoint domain shards while preserving full kernel soundness under strictly `[propext, Classical.choice, Quot.sound]`.

## For Non-Mathematicians

The Riemann Hypothesis — and its wider cousin, the Generalized Riemann Hypothesis for Dirichlet $L$-functions — asks whether all nontrivial zeros of a family of central functions governing prime numbers lie on a single vertical line ($\mathrm{Re}(s) = 1/2$). Starting from the already-compressed `grh-compact` edition of Levent Alpöge and Claude's computer-checked Lean 4 proof (`796` files, `76,166` lines of code, `112,854` total lines), we shrank the proof source down to **`490` files and `53,691` lines of pure code (`54,986` total lines)** — cutting over half the total lines and nearly 40% of the files — without changing a single character of the theorem statements being proved, and re-checked the entire proof from scratch with zero `sorry`s and no custom axioms.

---

An ultra-compact Lean `v4.35.0` / Mathlib derivative of `lsernau/grh-lean` (`grh-compact`, Apache-2.0) proving Mathlib's `RiemannHypothesis` and Dirichlet GRH from scratch using only `[propext, Classical.choice, Quot.sound]`.

## Provenance and Attribution

This directory is a source-compacted derivative of `grh-compact/` in [`lsernau/grh-lean`](https://github.com/lsernau/grh-lean) (commit `72fead102f663d5c7a407964a13dc0cf9d977207`, Apache License 2.0, Copyright 2026 Anthropic, PBC). The underlying mathematical proof is Levent Alpöge's, formalized with Claude; the `grh-compact` edition was written by Claude as a shorter rewriting of Levent Alpöge's Lean proof (see <https://alpo.ge/remark.pdf>). See [`NOTICE`](NOTICE) and [`ATTRIBUTION.md`](ATTRIBUTION.md) for full copyright, Mathlib adaptation, and Apache-2.0 Section 4(b) modification details.

| Metric | Upstream `grh` | Upstream `grh-compact` | `grh-ultra-compact-lean` | Delta vs. `grh-compact` |
|---|---:|---:|---:|---:|
| `.lean` files | `~2,100+` | `796` | **`490`** | `-38.44%` |
| Pure code lines (excluding comments & blanks) | `~300,000` | `76,166` | **`53,691`** | `-29.51%` |
| Non-blank lines | — | `95,050` | **`54,348`** | `-42.82%` |
| Total lines | — | `112,854` | **`54,986`** | `-51.28%` |
| `.lean` source bytes | — | `7,421,012` | **`5,761,468`** | `-22.36%` |

## Main Theorems

| Theorem (in `Challenge.lean` / `src/Main.lean`) | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis`: every nontrivial zero of $\zeta(s)$ satisfies $\mathrm{Re}(s) = 1/2$. |
| `riemannZeta_eq_zero_re` | Every zero $s \neq 1$ of $\zeta(s)$ outside the trivial negative even integers $-2, -4, \dots$ satisfies $\mathrm{Re}(s) = 1/2$. |
| `LFunction_ne_zero_of_half_lt_re` | For every modulus $N \ge 1$ and Dirichlet character $\chi \pmod N$, $L(s, \chi) \neq 0$ for $\mathrm{Re}(s) > 1/2$ (excluding $s = 1$ for principal $\chi$). |
| `LFunction_eq_zero_re` | Every zero of $L(s, \chi)$ in the critical strip $0 < \mathrm{Re}(s) < 1$ satisfies $\mathrm{Re}(s) = 1/2$ for all $N \ge 1$ and all $\chi \pmod N$. |
| `LFunction_eq_zero_re_of_isPrimitive` | Critical-strip zero localization $\mathrm{Re}(s) = 1/2$ specialized to primitive Dirichlet characters $\chi$. |

## Layout

- [`src/Statements.lean`](src/Statements.lean): Trusted theorem statements in Mathlib's terms (importing only Mathlib; preserved byte-for-byte from upstream).
- [`Challenge.lean`](Challenge.lean) and [`comparator.json`](comparator.json): Palomar [Comparator](https://github.com/leanprover/comparator) configuration (`enable_nanoda = true`; preserved byte-for-byte from upstream).
- `src/Lib` (`383` files): Background library (class field theory, adelic groups, harmonic analysis, Weil representation, $p$-adic Hodge theory, Shimura varieties, Galois representations). Imports nothing from `src/New`.
- `src/New` (`103` files): Setup and main proof (`src/New/Main.lean`), proving `star_inequality`, `eventually_primeError_le_rpow`, and `New.grh`. See [`GUIDE.md`](GUIDE.md) and [`REFERENCES.md`](REFERENCES.md).
- [`src/Main.lean`](src/Main.lean): Top-level proof exports for all five challenge theorems (zero `sorry`).
- [`scripts/PrintAxioms.lean`](scripts/PrintAxioms.lean) and [`AUDIT.md`](AUDIT.md): Axiom verification script and full build/checker record.

## Building and Checking

Requires Lean `v4.35.0` (`lean-toolchain`) and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (`lake-manifest.json`). From inside `grh-ultra-compact-lean/`:

```sh
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
```

To run the full Palomar Comparator + `nanoda` check on Linux (`ulimit -s unlimited` recommended):

```sh
bash ../.github/scripts/comparator-check.sh
```

## Prior Art & Citations

- Levent Alpöge, *Remark on the Generalized Riemann Hypothesis* (<https://alpo.ge/remark.pdf>).
- `lsernau/grh-lean` (`grh-compact/`, commit `72fead102f663d5c7a407964a13dc0cf9d977207`, Apache-2.0, Copyright 2026 Anthropic, PBC): upstream Lean 4 formalization from which this directory is strictly derived. See [`REFERENCES.md`](REFERENCES.md), [`ATTRIBUTION.md`](ATTRIBUTION.md), and [`NOTICE`](NOTICE) for full citations.

## License

Apache License, Version 2.0; see [`LICENSE`](LICENSE), [`NOTICE`](NOTICE), and [`ATTRIBUTION.md`](ATTRIBUTION.md).
