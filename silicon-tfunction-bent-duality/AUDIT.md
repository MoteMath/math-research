# Formal Verification Audit (`silicon-tfunction-bent-duality`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built SiliconTfunctionBentDuality.Defs (2.9s)
✔ [3/7] Built SiliconTfunctionBentDuality.Theorems (45s)
✔ [4/7] Built SiliconTfunctionBentDuality (1.9s)
✔ [6/7] Built Solution (1.8s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.2s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:13:8: declaration uses `sorry`
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `SiliconTfunctionBentDuality/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SiliconTfunctionBentDualityChallenge.walsh_walsh' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconTfunctionBentDualityChallenge.mm_isBent' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconTfunctionBentDualityChallenge.zeroSum_tQuad_isBent' depends on axioms: [propext, Classical.choice, Quot.sound]
'SiliconTfunctionBentDualityChallenge.mul3_infinite_bent_and_nonMM' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SiliconTfunctionBentDualityChallenge.mul7_infinite_bent_and_nonMM' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SiliconTfunctionBentDualityChallenge.counterexample_non_bijective_mul2' depends on axioms: [propext, Quot.sound]
'SiliconTfunctionBentDualityChallenge.counterexample_non_causal_shift' depends on axioms: [propext]
'SiliconTfunctionBentDualityChallenge.nonvacuity_carletT_nonzero_pi0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
