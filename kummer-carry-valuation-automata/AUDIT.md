# Formal Verification Audit (`kummer-carry-valuation-automata`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built KummerCarryValuationAutomata.Defs (2.2s)
✔ [3/7] Built KummerCarryValuationAutomata.Theorems (29s)
✔ [4/7] Built KummerCarryValuationAutomata (3.5s)
✔ [6/7] Built Solution (2.4s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.5s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:38:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Exit codes: `lake build` = 0, `lake build Challenge` = 0. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'KummerCarryValuationAutomataChallenge.v2_binom_add_popcount' depends on axioms: [propext, Quot.sound]
'KummerCarryValuationAutomataChallenge.v2_trinom_add_popcount' depends on axioms: [propext, Quot.sound]
'KummerCarryValuationAutomataChallenge.shifted_xor_kummer_exact' depends on axioms: [propext, Quot.sound]
'KummerCarryValuationAutomataChallenge.shifted_or_kummer_exact' depends on axioms: [propext, Quot.sound]
'KummerCarryValuationAutomataChallenge.gray_binom_even' depends on axioms: [propext, Quot.sound]
'KummerCarryValuationAutomataChallenge.gray_strictly_below_shifted_xor' depends on axioms: [propext, Quot.sound]
'KummerCarryValuationAutomataChallenge.binom_11n_sharp_slope' depends on axioms: [propext, Classical.choice, Quot.sound]
'KummerCarryValuationAutomataChallenge.binom_55n_sharp_infinite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
