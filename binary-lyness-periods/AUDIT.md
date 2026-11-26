# Formal Verification Audit (`binary-lyness-periods`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Build & Challenge Checks

```text
$ lake build
✔ [3/7] Built BinaryLynessPeriods.Theorems (8.6s)
✔ [4/7] Built BinaryLynessPeriods (1.4s)
✔ [6/7] Built Solution (1.4s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the five intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BinaryLynessPeriods/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BinaryLynessChallenge.feistelStep_iter_six_of_even_parity' depends on axioms: [propext, Quot.sound]
'BinaryLynessChallenge.feistelStep_iter_twelve_of_odd_parity' depends on axioms: [propext, Quot.sound]
'BinaryLynessChallenge.lynessStep_pow_two_period_six' depends on axioms: [propext, Quot.sound]
'BinaryLynessChallenge.lynessStep_period_six_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryLynessChallenge.orLynessStep_pow_two_period_twelve' depends on axioms: [propext, Quot.sound]
```

Four of the five headline theorems are completely constructive (`[propext, Quot.sound]` only), and all five depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
