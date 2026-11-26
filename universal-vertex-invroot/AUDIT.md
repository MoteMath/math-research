# Formal Verification Audit (`universal-vertex-invroot`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

## For Mathematicians

All six headline theorems in `UniversalVertexInvrootChallenge` (`Challenge.lean` / `Solution.lean`) are proved from Lean 4 `Init` alone with zero Mathlib dependencies and zero `native_decide`. The universal all-$p$ algebraic theorems (`universal_invroot_vertex_identity_and_positivity`, `universal_invroot_cubic_convergence`) hold for every `p : Nat` with `1 ≤ p` and every `m : Rat`, proved via cleared-denominator rational identities and an explicit recursive remainder induction `polyPowRem`. The continuous 6-step BF16 stationary confinement proofs (`bf16_inv_sqrt_vertex_certified`, `bf16_inv_cbrt_vertex_certified`, `bf16_inv_eighth_vertex_certified`) compose exact pointwise adversarial envelopes (`noisyVertexStep2_envelope`, `noisyVertexStep3_envelope`, `noisyVertexStep8_envelope`) with a sound unnormalized `Int`-pair (`QPair`) uniform-partition interval checker (`checkVertexStepP`) and sound outward $2^{-40}$ dyadic rounding (`qFloor40` / `qCeil40`), avoiding `Rat.normalize` / `Nat.gcd` overhead in kernel reduction.

## For Non-Mathematicians

Every mathematical claim in this package is verified directly by the Lean 4 proof kernel—not by floating-point tests or unverified scripts. The compiler checks the universal all-$p$ vertex formula, its cubic convergence rate, the degree-5 vs. degree-9 hardware rounding-floor dominance, and that the exact BF16 schedules for $p \in \{2, 3, 8\}$ stay strictly inside their certified bands against every worst-case rounding adversary across all 6 steps.

## Prior-Art Context

Builds on Guo & Higham (2006) coupled matrix $p$-th root iterations, Shampoo (Gupta et al. 2018) / SOAP (Vyas et al. 2024) / Muon (Jordan et al. 2024) low-precision matrix root preconditioning, and the pure-`Init` Palomar Comparator template established in `muon-vertex-polar` and `soap-vertex-fourth-root`.

## Build & Challenge Checks

```text
$ lake build
✔ [2/8] Built UniversalVertexInvroot.Defs (1.3s)
✔ [3/8] Built UniversalVertexInvroot.Algebra (8.5s)
✔ [4/8] Built UniversalVertexInvroot.Certificates (9.0s)
✔ [5/8] Built UniversalVertexInvroot (1.0s)
✔ [7/8] Built Solution (1.2s)
Build completed successfully (8 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:75:8: declaration uses `sorry`
warning: Challenge.lean:84:8: declaration uses `sorry`
warning: Challenge.lean:93:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry` / `admit` / `axiom` / `native_decide` / `lemma` anywhere in `UniversalVertexInvroot/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'UniversalVertexInvrootChallenge.universal_invroot_vertex_identity_and_positivity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'UniversalVertexInvrootChallenge.universal_invroot_cubic_convergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'UniversalVertexInvrootChallenge.deg9_shared_square_and_rounding_floor_dominance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'UniversalVertexInvrootChallenge.bf16_inv_sqrt_vertex_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'UniversalVertexInvrootChallenge.bf16_inv_cbrt_vertex_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'UniversalVertexInvrootChallenge.bf16_inv_eighth_vertex_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero `Lean.ofReduceBool` / `native_decide`, matching `comparator.json` (`enable_nanoda: true`).
