# Formal Verification Audit (`xor-vdc-fp4-dither`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Build & Challenge Checks

```text
$ lake build
✔ [8/11] Built XorVdcFp4Dither (1.8s)
✔ [10/11] Built Solution (2.4s)
Build completed successfully (11 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.0s)
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
warning: Challenge.lean:84:8: declaration uses `sorry`
warning: Challenge.lean:97:8: declaration uses `sorry`
warning: Challenge.lean:118:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `XorVdcFp4Dither/`, `XorVdcFp4Dither.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'XorVdcFp4DitherChallenge.xor_vdc_sr_unbiased_and_covariance_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'XorVdcFp4DitherChallenge.xor_vdc_walsh_spectrum_and_trace_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'XorVdcFp4DitherChallenge.e2m1_harmonic_mean_worst_case_sr_variance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'XorVdcFp4DitherChallenge.antithetic_pair_sr_variance_halving' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'XorVdcFp4DitherChallenge.double_quant_gemm_bias_obstruction_and_hammersley' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'XorVdcFp4DitherChallenge.split_32bit_word_xor_vdc_zero_bias_double_gemm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.
