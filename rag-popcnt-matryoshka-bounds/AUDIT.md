# Formal Verification Audit (`rag-popcnt-matryoshka-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Clean build time:** `11.90 s` (all 13 jobs from `lake clean`)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*10 + 2*9 + 2*10 + 10 = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake clean && lake build
✔ [2/13] Built RagPopcntMatryoshka.Defs (2.3s)
✔ [3/13] Built RagPopcntMatryoshka.RatOrder (1.0s)
✔ [4/13] Built RagPopcntMatryoshka.PopcntIdentities (2.9s)
✔ [5/13] Built RagPopcntMatryoshka.OversampleSnr (2.9s)
✔ [6/13] Built RagPopcntMatryoshka.HypercubeNorm (2.9s)
✔ [7/13] Built RagPopcntMatryoshka.Int4RescoreGap (2.9s)
✔ [8/13] Built RagPopcntMatryoshka.RooflineSpeedup (2.9s)
✔ [9/13] Built RagPopcntMatryoshka.MatryoshkaCrossover (2.0s)
✔ [10/13] Built RagPopcntMatryoshka (1.2s)
✔ [12/13] Built Solution (1.4s)
Build completed successfully (13 jobs).
CLEAN_BUILD_SECONDS=11.90

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:77:8: declaration uses `sorry`
warning: Challenge.lean:98:8: declaration uses `sorry`
warning: Challenge.lean:115:8: declaration uses `sorry`
warning: Challenge.lean:137:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `RagPopcntMatryoshka/`, `RagPopcntMatryoshka.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'RagPopcntMatryoshkaChallenge.popcnt_binary_and_twoplane_exact_dot_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RagPopcntMatryoshkaChallenge.two_stage_oversample_snr_squared_hierarchy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RagPopcntMatryoshkaChallenge.matryoshka_vs_full_dim_binary_spectral_crossover_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RagPopcntMatryoshkaChallenge.hypercube_sign_wht_automatic_spectral_normalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RagPopcntMatryoshkaChallenge.stage2_int4_rescore_gap_preservation_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RagPopcntMatryoshkaChallenge.rag_memory_and_bandwidth_speedup_roofline_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
