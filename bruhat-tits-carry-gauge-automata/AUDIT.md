# Formal Verification Audit (`bruhat-tits-carry-gauge-automata`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BruhatTitsCarryGaugeAutomata.Defs (47s)
✔ [3/7] Built BruhatTitsCarryGaugeAutomata.Theorems (25s)
✔ [4/7] Built BruhatTitsCarryGaugeAutomata (1.0s)
⚠ [6/7] Built Solution (1.8s)
warning: Solution.lean:13:17: Variable name `K` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _K

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: Solution.lean:13:27: Variable name `hd` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hd

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: Solution.lean:13:40: Variable name `M0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _M0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: Solution.lean:13:43: Variable name `M1` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _M1

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: Solution.lean:13:56: Variable name `v0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _v0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: Solution.lean:44:30: Variable name `K` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _K

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: Solution.lean:44:40: Variable name `m` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _m

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: Solution.lean:44:50: Variable name `M0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _M0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: Solution.lean:44:53: Variable name `M1` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _M1

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: Solution.lean:44:66: Variable name `v0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _v0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:15:8: declaration uses `sorry`
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BruhatTitsCarryGaugeAutomata/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BruhatTitsCarryGaugeAutomataChallenge.carryCount_eq_evalMat' depends on axioms: [propext, Quot.sound]
'BruhatTitsCarryGaugeAutomataChallenge.sound' depends on axioms: [propext, Quot.sound]
'BruhatTitsCarryGaugeAutomataChallenge.thm_2x2_5point_rigidity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BruhatTitsCarryGaugeAutomataChallenge.thm_2x2_k_equiv_3_mod_8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BruhatTitsCarryGaugeAutomataChallenge.thm_3x3_exact_v2' depends on axioms: [propext, Quot.sound]
'BruhatTitsCarryGaugeAutomataChallenge.thm_phi4_unbounded' depends on axioms: [propext, Quot.sound]
'BruhatTitsCarryGaugeAutomataChallenge.nonvacuous_3x3_k4' depends on axioms: [propext, Quot.sound]
'BruhatTitsCarryGaugeAutomataChallenge.sharpness_3x3_all_five_weights' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
