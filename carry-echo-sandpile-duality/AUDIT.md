# Formal Verification Audit (`carry-echo-sandpile-duality`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:64:8: declaration uses `sorry`
warning: Challenge.lean:71:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CarryEchoSandpileDuality/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CarryEchoSandpileDualityChallenge.carryEcho_skew_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryEchoSandpileDualityChallenge.carryEcho_total_avalanche_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryEchoSandpileDualityChallenge.carryEcho_recurrent_iff_dualSkew' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryEchoSandpileDualityChallenge.carryEcho_recurrent_count_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryEchoSandpileDualityChallenge.carryEcho_explicitIdentity_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryEchoSandpileDualityChallenge.carryEcho_identity_laws_ge2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryEchoSandpileDualityChallenge.directedCarry_all_stable_recurrent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryEchoSandpileDualityChallenge.directedCarry_kummer_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
