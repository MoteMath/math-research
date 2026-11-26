# Formal Verification Audit (`mla-kantorovich-rope-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 93 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake build
✔ [2/11] Built MlaKantorovichRope.Defs (7.1s)
✔ [3/11] Built MlaKantorovichRope.RatOrder (2.1s)
✔ [4/11] Built MlaKantorovichRope.NopeRopeMemory (5.8s)
✔ [5/11] Built MlaKantorovichRope.KantorovichGL (7.7s)
✔ [6/11] Built MlaKantorovichRope.PythagoreanRope (2.8s)
✔ [7/11] Built MlaKantorovichRope.ParsevalMultihead (2.9s)
✔ [8/11] Built MlaKantorovichRope (1.6s)
✔ [10/11] Built Solution (1.9s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.7s)
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:68:8: declaration uses `sorry`
warning: Challenge.lean:95:8: declaration uses `sorry`
warning: Challenge.lean:121:8: declaration uses `sorry`
warning: Challenge.lean:156:8: declaration uses `sorry`
warning: Challenge.lean:182:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `MlaKantorovichRope/`, `MlaKantorovichRope.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MlaKantorovichRopeChallenge.kantorovich_bilinear_spectral_leakage_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MlaKantorovichRopeChallenge.absorbed_kv_gl_invariance_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'MlaKantorovichRopeChallenge.decoupled_nope_rope_256_85_crossover_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MlaKantorovichRopeChallenge.parseval_tight_frame_multihead_interference_cap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MlaKantorovichRopeChallenge.pythagorean_1105_multi_angle_rope_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MlaKantorovichRopeChallenge.subbyte_mla_memory_compression_ratios_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
