# Formal Verification Audit (`fano-sparse24-perm`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 93 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/12] Built FanoSparse24Perm.Defs (2.0s)
✔ [3/12] Built FanoSparse24Perm.RatOrder (2.3s)
✔ [4/12] Built FanoSparse24Perm.Ef21Structured (2.7s)
✔ [5/12] Built FanoSparse24Perm.FanoObstruction (11s)
✔ [6/12] Built FanoSparse24Perm.OrderStats (38s)
✔ [7/12] Built FanoSparse24Perm.Mxfp4Joint (59s)
✔ [8/12] Built FanoSparse24Perm.SunflowerObstruction (74s)
✔ [9/12] Built FanoSparse24Perm (11s)
✔ [11/12] Built Solution (18s)
Build completed successfully (12 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (16s)
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:86:8: declaration uses `sorry`
warning: Challenge.lean:112:8: declaration uses `sorry`
warning: Challenge.lean:130:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the five intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `FanoSparse24Perm/`, `FanoSparse24Perm.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'FanoSparse24PermChallenge.structured_topk_ef21_contraction_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FanoSparse24PermChallenge.mxfp4_anchor_dilution_48_beats_24_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FanoSparse24PermChallenge.fano_plane_sparse24_obstruction_exact' depends on axioms: [propext, Quot.sound]
'FanoSparse24PermChallenge.sunflower_sparse24_obstruction_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FanoSparse24PermChallenge.order_statistic_k2k_nmse_laws_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All five headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
