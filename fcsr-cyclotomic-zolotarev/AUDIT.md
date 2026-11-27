# Formal Verification Audit (`fcsr-cyclotomic-zolotarev`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built FcsrCyclotomicZolotarev.Defs (4.2s)
✔ [3/7] Built FcsrCyclotomicZolotarev.Theorems (45s)
✔ [4/7] Built FcsrCyclotomicZolotarev (2.6s)
✔ [6/7] Built Solution (2.3s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.7s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
warning: Challenge.lean:73:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Exit codes: `lake build` = 0, `lake build Challenge` = 0. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'FcsrCyclotomicZolotarevChallenge.word_representation_exact' depends on axioms: [propext, Quot.sound]
'FcsrCyclotomicZolotarevChallenge.step_bijection_on_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'FcsrCyclotomicZolotarevChallenge.carry_bounds_on_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'FcsrCyclotomicZolotarevChallenge.universal_carry_bit_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FcsrCyclotomicZolotarevChallenge.halfPeriod_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'FcsrCyclotomicZolotarevChallenge.dSection_cyclotomic_engine' depends on axioms: [propext, Classical.choice, Quot.sound]
'FcsrCyclotomicZolotarevChallenge.even_period_of_mod8_3_or_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'FcsrCyclotomicZolotarevChallenge.family_pow2_add_3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
