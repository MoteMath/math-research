# Audit record

This file records the checks run on the exact sources in `grh-ultra-compact-lean/`.

Toolchain: Lean `leanprover/lean4:v4.35.0`; Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (pinned in `lake-manifest.json`).

## Source compaction summary (vs. upstream `grh-compact` at `72fead10`)

| Metric | Upstream `grh-compact` | `grh-ultra-compact-lean` | Delta | Change |
|---|---:|---:|---:|---:|
| `.lean` files | `796` | `490` | `-306` | `-38.44%` |
| Pure code lines (excluding comments & blanks) | `76,166` | `53,691` | `-22,475` | `-29.51%` |
| Non-blank lines | `95,050` | `54,348` | `-40,702` | `-42.82%` |
| Total lines | `112,854` | `54,986` | `-57,868` | `-51.28%` |
| `.lean` source bytes | `7,421,012` | `5,761,468` | `-1,659,544` | `-22.36%` |

All frozen specification and configuration files (`src/Statements.lean`, `Challenge.lean`, `src/Main.lean`, `comparator.json`, `lean-toolchain`, `lake-manifest.json`, `lakefile.toml`) match upstream SHA-256 checksums bit-for-bit.

## How to reproduce

```sh
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
bash ../.github/scripts/comparator-check.sh
```

## Recorded results

- `lake build` (100% zero-project-cache clean build from scratch after `lake exe cache get`): **passed** with exit code `0` across all `9,537` build jobs (`488` library modules across `Lib`, `New`, `Statements`, `Main`); zero `sorry` outside `Challenge.lean`.
- Custom axioms (`axiom ...`) outside comments: **0**.
- Independent Rust kernel check (`con-ron --compare --verified` comparing the `lean4export v3.1.0` dump of `Main` against `Challenge.lean`): **passed** (`accepted 52169 declarations, 5 axioms justified by the solution; 204185 declarations accepted` — all 5 headline theorems justified).
- `leanprover/comparator` with `lean4export` (`v4.35.0`), `nanoda`, and `landrun` (`comparator.json`, `enable_nanoda = true`): sandboxed `lake build Main` (`9,535/9,535` jobs) and `lean4export` **passed**; the `nanoda` kernel replay had not completed when this audit was written. The only CI run recorded for this project (2026-11-26) was cancelled, so no external-kernel replay of this project is on record; the workflow `.github/workflows/lean-projects.yml` can be run for it with `workflow_dispatch`.

### `#print axioms` output (`scripts/PrintAxioms.lean`), verbatim

```text
'riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
'riemannZeta_eq_zero_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_ne_zero_of_half_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_eq_zero_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_eq_zero_re_of_isPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound]
```
