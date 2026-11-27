# Formal Verification Audit (`arx-rank1-surgery-quotient-locks`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built ArxRank1SurgeryQuotientLocks.Defs (1.8s)
✔ [3/7] Built ArxRank1SurgeryQuotientLocks.Theorems (41s)
✔ [4/7] Built ArxRank1SurgeryQuotientLocks (1.9s)
✔ [6/7] Built Solution (2.6s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.4s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:70:8: declaration uses `sorry`
warning: Challenge.lean:80:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Exit codes: `lake build` = 0, `lake build Challenge` = 0. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ArxRank1SurgeryQuotientLocksChallenge.rank1Surgery_spliced_minPeriod' depends on axioms: [propext, Quot.sound]
'ArxRank1SurgeryQuotientLocksChallenge.rank1Surgery_global_order' depends on axioms: [propext, Quot.sound]
'ArxRank1SurgeryQuotientLocksChallenge.arx_fermat_mersenne_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ArxRank1SurgeryQuotientLocksChallenge.arx_fermat_mersenne_even' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ArxRank1SurgeryQuotientLocksChallenge.arx_fermat_number_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ArxRank1SurgeryQuotientLocksChallenge.arx_rank1_surgery_theorem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ArxRank1SurgeryQuotientLocksChallenge.arx_rank1_surgery_nontrivial_xor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ArxRank1SurgeryQuotientLocksChallenge.speck_period3_quotient_lock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
