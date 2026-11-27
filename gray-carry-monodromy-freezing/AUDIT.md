# Formal Verification Audit (`gray-carry-monodromy-freezing`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [3/7] Built GrayCarryMonodromyFreezing.Theorems (33s)
✔ [4/7] Built GrayCarryMonodromyFreezing (2.9s)
✔ [6/7] Built Solution (3.2s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:21:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:52:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
warning: Challenge.lean:81:8: declaration uses `sorry`
warning: Challenge.lean:100:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the 7 intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `GrayCarryMonodromyFreezing/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'GrayCarryMonodromyFreezingChallenge.bdftr_exact_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrayCarryMonodromyFreezingChallenge.grayRight_nat_stabilization' depends on axioms: [propext, Quot.sound]
'GrayCarryMonodromyFreezingChallenge.grayRight_sub_complete_annihilation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryMonodromyFreezingChallenge.cpmf_full_partition_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryMonodromyFreezingChallenge.lgray1_mod32_9_exact_five_cycles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryMonodromyFreezingChallenge.lgray1_mod64_19_exact_seven_cycles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayCarryMonodromyFreezingChallenge.lgray_ge2_odd_single_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (no `sorryAx`, no `Lean.ofReduceBool`).
