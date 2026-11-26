# Formal Verification Audit (`muon-vertex-polar`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Build & Challenge Checks

```text
$ lake build
✔ [2/8] Built MuonVertexPolar.Defs (1.4s)
✔ [3/8] Built MuonVertexPolar.Algebra (33s)
✔ [4/8] Built MuonVertexPolar.Certificates (3.5s)
✔ [5/8] Built MuonVertexPolar (1.1s)
✔ [7/8] Built Solution (1.2s)
Build completed successfully (8 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:70:8: declaration uses `sorry`
warning: Challenge.lean:80:8: declaration uses `sorry`
warning: Challenge.lean:90:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the seven intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `MuonVertexPolar/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MuonVertexPolarChallenge.shifted_square_equiv_monomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'MuonVertexPolarChallenge.shifted_square_quadratic_error_at_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MuonVertexPolarChallenge.noisyShiftedStep_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'MuonVertexPolarChallenge.bf16_stationary_shifted_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'MuonVertexPolarChallenge.bf16_dp5_shifted_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'MuonVertexPolarChallenge.fp8_pure_dp5_shifted_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'MuonVertexPolarChallenge.fp8_hybrid_dp5_shifted_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All seven headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero `Lean.ofReduceBool` / `native_decide`, matching `comparator.json` with `enable_nanoda: true`.
