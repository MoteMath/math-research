# Formal Verification Audit (`soap-vertex-fourth-root`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **8 / 10** | **9 / 10** | **10 / 10** | **89 / 100** |

## For Mathematicians

All seven headline theorems in `SoapVertexFourthRootChallenge` (`Challenge.lean` / `Solution.lean`) are proved from Lean 4 `Init` alone with zero Mathlib dependencies and zero `native_decide`. The continuous 5-step confinement proofs (`bf16_fourth_root_dp5_certified`, `bf16_fourth_root_eps1e4_certified`, `fp8_hybrid_fourth_root_dp5_certified`, `fp8_pure_fourth_root_linear_dp5_certified`) compose the exact pointwise envelopes (`noisyVertexStep4_envelope`, `noisyLinearStep4_envelope`) with a sound unnormalized `Int`-pair (`QPair`) uniform-partition interval checker (`checkVertexStep` at `K = 128`, `checkLinearStep` at `K = 256`), avoiding `Rat.normalize` / `Nat.gcd` overhead in kernel reduction.

## For Non-Mathematicians

Every claim in this package is verified directly by the Lean 4 proof kernel—not by floating-point tests or unverified scripts. The compiler checks that across all 5 steps and every possible worst-case rounding error at every arithmetic operation, the output stays strictly inside the stated intervals.

## Prior-Art Context

Builds on Guo & Higham (2006) coupled matrix $p$-th root iterations, Shampoo (Gupta et al. 2018) / SOAP (Vyas et al. 2024) Kronecker preconditioning, and the pure-`Init` Palomar Comparator template established in `muon-vertex-polar`.

## Build & Challenge Checks

```text
$ lake build
✔ [2/8] Built SoapVertexFourthRoot.Defs (1.5s)
✔ [3/8] Built SoapVertexFourthRoot.Algebra (6.3s)
✔ [4/8] Built SoapVertexFourthRoot.Certificates (20s)
✔ [5/8] Built SoapVertexFourthRoot (1.2s)
✔ [7/8] Built Solution (1.2s)
Build completed successfully (8 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
warning: Challenge.lean:71:8: declaration uses `sorry`
warning: Challenge.lean:81:8: declaration uses `sorry`
warning: Challenge.lean:91:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the seven intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry` / `admit` / `axiom` / `native_decide` anywhere in `SoapVertexFourthRoot/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SoapVertexFourthRootChallenge.vertex_fourth_root_equiv_monomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SoapVertexFourthRootChallenge.taylor2_fourth_root_vertex_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SoapVertexFourthRootChallenge.noisyFourthRootStep_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'SoapVertexFourthRootChallenge.bf16_fourth_root_dp5_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SoapVertexFourthRootChallenge.bf16_fourth_root_eps1e4_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SoapVertexFourthRootChallenge.fp8_hybrid_fourth_root_dp5_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SoapVertexFourthRootChallenge.fp8_pure_fourth_root_linear_dp5_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All seven headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero `Lean.ofReduceBool` / `native_decide`, matching `comparator.json` (`enable_nanoda: true`).
