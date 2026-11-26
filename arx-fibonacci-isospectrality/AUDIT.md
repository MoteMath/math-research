# Formal Verification Audit (`arx-fibonacci-isospectrality`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Build & Challenge Checks

```text
$ lake build
✔ [3/7] Built ArxFibonacciIsospectrality.Theorems (9.7s)
✔ [4/7] Built ArxFibonacciIsospectrality (1.4s)
✔ [6/7] Built Solution (1.3s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.4s)
warning: Challenge.lean:10:8: declaration uses `sorry`
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the five intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `ArxFibonacciIsospectrality/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ArxFibonacciChallenge.xor_add_pow_two_mod' depends on axioms: [propext, Quot.sound]
'ArxFibonacciChallenge.arxFibStep_fixed_point_iff' depends on axioms: [propext, Quot.sound]
'ArxFibonacciChallenge.arxFibStep_exact_minPeriod' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArxFibonacciChallenge.arxFibStep_isospectral_bijection' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArxFibonacciChallenge.arxFibStep3_breaks_isospectrality' depends on axioms: [propext, Quot.sound]
```

Three of the five headline theorems are completely constructive (`[propext, Quot.sound]` only), and all five depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
