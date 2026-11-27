# Formal Verification Audit (`gray-basis-feistel-carry-orbits`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built GrayBasisFeistelCarryOrbits.Defs (3.2s)
✔ [3/7] Built GrayBasisFeistelCarryOrbits.Theorems (44s)
✔ [4/7] Built GrayBasisFeistelCarryOrbits (1.8s)
✔ [6/7] Built Solution (2.2s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Exit codes: `lake build` = 0, `lake build Challenge` = 0. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'GrayBasisFeistelCarryOrbitsChallenge.phi_singleCycle_iff_even' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayBasisFeistelCarryOrbitsChallenge.grayInvMap_singleCycle_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayBasisFeistelCarryOrbitsChallenge.grayBitPermInvolution_plusOne_universal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayBasisFeistelCarryOrbitsChallenge.grayBitrev_plusOne_order4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayBasisFeistelCarryOrbitsChallenge.grayBitPermInvolution_msbKick_singleCycle_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayBasisFeistelCarryOrbitsChallenge.grayBitrev_msbKick_singleCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayBasisFeistelCarryOrbitsChallenge.feistelCarry_singleCycle_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GrayBasisFeistelCarryOrbitsChallenge.feistelCarry_bijection_jacobsthal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
