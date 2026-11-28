# Verification & Audit Receipt (`carryless-f2-smith-determinants`)

- **Toolchain:** `leanprover/lean4:v4.34.1` + Mathlib `v4.34.1`
- **Palomar Comparator Manifest:** [`comparator.json`](comparator.json) (`enable_nanoda: true`, 10 pinned theorems, 9 pinned definitions)
- **Permitted Axioms:** `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`, zero custom axioms)

## Build Receipt

```text
> lake build
✔ [3093/3097] Built CarrylessSmithDet.Theorems (18s)
✔ [3094/3097] Built CarrylessSmithDet (15s)
✔ [3096/3097] Built Solution (15s)
Build completed successfully (3097 jobs).

> lake build Challenge
⚠ [1954/1955] Built Challenge (11s)
warning: Challenge.lean:6:8: declaration uses `sorry`
warning: Challenge.lean:11:8: declaration uses `sorry`
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:23:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:61:8: declaration uses `sorry`
warning: Challenge.lean:69:8: declaration uses `sorry`
Build completed successfully (1955 jobs).
```

## `#print axioms` Receipt (`lake env lean PrintAxioms.lean`)

```text
'CarrylessSmithDet.natToPoly_clmul' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarrylessSmithDet.polyToNat_natToPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarrylessSmithDet.natToPoly_polyToNat' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarrylessSmithDet.det_clgcdMat_of_divisorSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarrylessSmithDet.det_clgcdMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarrylessSmithDet.sum_clTotient_divisors' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarrylessSmithDet.det_clgcd_pow2_deg' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarrylessSmithDet.det_clgcd_id_collapse_nine' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarrylessSmithDet.det_clgcd_coprime_collapse_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarrylessSmithDet.det_clgcd_popcount_collapse_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Provenance

Discovered by zero-floating-point bare-metal RDNA3 (`gfx1100`) 32-prime CRT modular determinant mining in `alien-silicon-hunt-20261128` Track A (`f2_pow2_deg_gcd_1`, `NO_EXACT_OEIS_MATCH`), validated bit-identically on CPU, generalized to arbitrary arithmetic functions `f : ℕ → R` over any commutative ring $R$, and proved unconditionally in Lean 4's kernel together with the sharp `n = 9`, `n = 4`, and `n = 2` singularity collapses.
