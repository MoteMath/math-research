# Formal Verification Audit (`dyadic-ldlt-schur-posdef-engine`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.7s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:64:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `DyadicLdltSchurPosdefEngine/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'DyadicLdltSchurPosdefEngineChallenge.ldlt_strictlyPosDef_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicLdltSchurPosdefEngineChallenge.ldlt_quadForm_lower_bound' depends on axioms: [propext, Quot.sound]
'DyadicLdltSchurPosdefEngineChallenge.schurSystem_nested_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DyadicLdltSchurPosdefEngineChallenge.vdcHamming_strictlyPosDef_all_n_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicLdltSchurPosdefEngineChallenge.vdcHamming_critical_4_3_all_n' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicLdltSchurPosdefEngineChallenge.vdcHamming_sharp_15_4_fails_16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicLdltSchurPosdefEngineChallenge.grayWeighted_strictlyPosDef_all_n' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicLdltSchurPosdefEngineChallenge.expVdc_critical_7_6_all_n' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
