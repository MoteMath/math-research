# Formal Verification Audit (`muonclip-adamw-sr-bounds`)

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
✔ [2/10] Built MuonclipAdamwSr.Defs (1.2s)
✔ [3/10] Built MuonclipAdamwSr.RatOrder (1.3s)
✔ [4/10] Built MuonclipAdamwSr.AdamWFreeze (12s)
✔ [5/10] Built MuonclipAdamwSr.MuonClip (16s)
✔ [6/10] Built MuonclipAdamwSr.SrEmaJensen (17s)
✔ [7/10] Built MuonclipAdamwSr (1.1s)
✔ [9/10] Built Solution (1.5s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.5s)
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:71:8: declaration uses `sorry`
warning: Challenge.lean:108:8: declaration uses `sorry`
warning: Challenge.lean:132:8: declaration uses `sorry`
warning: Challenge.lean:153:8: declaration uses `sorry`
warning: Challenge.lean:187:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `MuonclipAdamwSr/`, `MuonclipAdamwSr.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MuonclipAdamwSrChallenge.muonclip_pitchfork_symmetry_breaking_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MuonclipAdamwSrChallenge.muonclip_rtn_overshoot_vs_rtz_safety' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MuonclipAdamwSrChallenge.adamw_weight_decay_freeze_radii_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MuonclipAdamwSrChallenge.sr_ema_two_state_markov_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'MuonclipAdamwSrChallenge.preconditioner_jensen_bias_exact_sqrt_vs_v' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MuonclipAdamwSrChallenge.asymmetric_muonclip_ratio_limit_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
