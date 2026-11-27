# Formal Verification Audit (`dyadic-skew-congruence-pfaffian`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built DyadicSkewCongruencePfaffian.Defs (24s)
✔ [3/7] Built DyadicSkewCongruencePfaffian.Theorems (70s)
✔ [4/7] Built DyadicSkewCongruencePfaffian (1.5s)
✔ [6/7] Built Solution (1.7s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.7s)
warning: Challenge.lean:7:8: declaration uses `sorry`
warning: Challenge.lean:12:8: declaration uses `sorry`
warning: Challenge.lean:22:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:40:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `DyadicSkewCongruencePfaffian/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'DyadicSkewCongruencePfaffianChallenge.pfaffian_blockUpperId' depends on axioms: [propext, Classical.choice, Quot.sound]
'DyadicSkewCongruencePfaffianChallenge.pfaffian_blockSchur_bot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicSkewCongruencePfaffianChallenge.pfaffian_skewConference_compl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicSkewCongruencePfaffianChallenge.pfaffian_carry_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound]
'DyadicSkewCongruencePfaffianChallenge.pfaffian_grayWalsh_pow2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DyadicSkewCongruencePfaffianChallenge.pfaffian_skewWalsh' depends on axioms: [propext, Classical.choice, Quot.sound]
'DyadicSkewCongruencePfaffianChallenge.sharpness_raw_carry_no_complement' depends on axioms: [propext, Quot.sound]
'DyadicSkewCongruencePfaffianChallenge.sharpness_shifted_skewWalsh' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
