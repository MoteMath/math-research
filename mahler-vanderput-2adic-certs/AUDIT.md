# Formal Verification Audit (`mahler-vanderput-2adic-certs`)

**Toolchain:** `leanprover/lean4:v4.35.0` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built MahlerVanderput2adicCerts.Defs (11s)
✔ [3/7] Built MahlerVanderput2adicCerts.Theorems (8.2s)
✔ [4/7] Built MahlerVanderput2adicCerts (1.7s)
✔ [6/7] Built Solution (2.9s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:13:8: declaration uses `sorry`
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:47:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `MahlerVanderput2adicCerts/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'MahlerVanderput2adicCertsChallenge.vdp_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound]
'MahlerVanderput2adicCertsChallenge.z2_density_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'MahlerVanderput2adicCertsChallenge.q_gray_alternating_duality_even' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MahlerVanderput2adicCertsChallenge.theta2_bitwise_inverse_Z2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MahlerVanderput2adicCertsChallenge.triadic_holder_2_3_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'MahlerVanderput2adicCertsChallenge.shear_carry_1lipschitz_sharp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MahlerVanderput2adicCertsChallenge.exp2c_neg_one_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'MahlerVanderput2adicCertsChallenge.nonvacuity_all_compilers' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
