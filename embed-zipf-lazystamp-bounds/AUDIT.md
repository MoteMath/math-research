# Formal Verification Audit (`embed-zipf-lazystamp-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26  
**Clean build time:** `11.06 s` (`< 40 s` budget)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **10 / 10** | **95 / 100** |

*Weighted composite: `3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 3*9 + 2*10 + 2*9 + 2*10 + 10 = 95 / 100`. See [`README.md`](README.md) for the full For Mathematicians, For Non-Mathematicians, and Prior-Art Context sections.*

## Build & Challenge Checks

```text
$ lake clean && lake build
✔ [2/13] Built EmbedZipfLazyStamp.Defs (1.2s)
✔ [3/13] Built EmbedZipfLazyStamp.RatOrder (1.6s)
✔ [4/13] Built EmbedZipfLazyStamp.TiedGrad (2.2s)
✔ [5/13] Built EmbedZipfLazyStamp.RneFlush (2.3s)
✔ [6/13] Built EmbedZipfLazyStamp.BandwidthSpeedup (2.2s)
✔ [7/13] Built EmbedZipfLazyStamp.ZipfPareto (2.2s)
✔ [8/13] Built EmbedZipfLazyStamp.Bf16Freeze (1.6s)
✔ [9/13] Built EmbedZipfLazyStamp.LazyAdamW (2.1s)
✔ [10/13] Built EmbedZipfLazyStamp (941ms)
✔ [12/13] Built Solution (1.1s)
Build completed successfully (13 jobs).
CLEAN_BUILD_SECONDS=11.0614603

$ lake build Challenge
⚠ [3/4] Built Challenge (1.1s)
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:57:8: declaration uses `sorry`
warning: Challenge.lean:92:8: declaration uses `sorry`
warning: Challenge.lean:117:8: declaration uses `sorry`
warning: Challenge.lean:135:8: declaration uses `sorry`
warning: Challenge.lean:158:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `EmbedZipfLazyStamp/`, `EmbedZipfLazyStamp.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'EmbedZipfLazyStampChallenge.tied_embedding_dense_pushdown_zero_sum_and_asymmetry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'EmbedZipfLazyStampChallenge.rare_token_rne_weight_flush_and_fp8_subnormal_underflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'EmbedZipfLazyStampChallenge.bf16_sparse_adamw_v_decay_freeze_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'EmbedZipfLazyStampChallenge.lazy_stamp_adamw_exact_equivalence_to_dense_updates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'EmbedZipfLazyStampChallenge.lazy_stamp_bandwidth_and_work_speedup_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'EmbedZipfLazyStampChallenge.zipf_mixed_precision_embedding_allocation_pareto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.

## Package Validation (`validate_pkgs.py`)

```text
$ python c:\Users\devin\Desktop\math\ai-math-continuous-20261126\validate_pkgs.py embed-zipf-lazystamp-bounds
PASS embed-zipf-lazystamp-bounds
```
