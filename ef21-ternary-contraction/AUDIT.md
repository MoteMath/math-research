# Formal Verification Audit (`ef21-ternary-contraction`)

**Toolchain:** `leanprover/lean4:v4.34.1` with Mathlib `v4.34.1`  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **8 / 10** | **9 / 10** | **90 / 100** |

## Build & Challenge Checks

```text
$ lake build
✔ [1523/1530] Built EF21Ternary.Defs (13s)
✔ [1524/1530] Built EF21Ternary.TwoBitAndSR (20s)
✔ [1526/1530] Built EF21Ternary.FP4 (31s)
✔ [1526/1530] Built EF21Ternary.Ternary (21s)
✔ [1527/1530] Built EF21Ternary (12s)
✔ [1529/1530] Built Solution (12s)
Build completed successfully (1530 jobs).

$ lake build Challenge
⚠ [1517/1518] Built Challenge (12s)
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
warning: Challenge.lean:80:8: declaration uses `sorry`
Build completed successfully (1518 jobs).
```

Zero errors, zero warnings outside the five intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `EF21Ternary/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'EF21TernaryChallenge.ternary_ef21_contraction_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'EF21TernaryChallenge.alphaTern_harmonic_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound]
'EF21TernaryChallenge.mxfp4_nvfp4_ef21_contraction_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'EF21TernaryChallenge.symmetric_2bit_no_zero_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'EF21TernaryChallenge.mantissa_sr_variance_law' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All five headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Quot.sound`, and `Classical.choice`), matching `comparator.json` with `enable_nanoda: true`.

## Verified MXFP4 / NVFP4 Universal Phase Regimes

- **MXFP4 (`alphaMXFP4 B = min (384 / (B + 399)) (min (192 / (B + 195)) (144 / (B + 143)))`):**
  - `1 ≤ B ≤ 8`: $\alpha _ {\mathrm{MXFP4}}(B) = 384 / (B + 399)$ (exact attainment at $(5, 1/4)$; $24/25$ at $B = 1$).
  - `9 ≤ B ≤ 12`: $\alpha _ {\mathrm{MXFP4}}(B) = 192 / (B + 195)$ (exact attainment at $(7/2, 1/4)$; $16/17$ at $B = 9$).
  - `B ≥ 13`: $\alpha _ {\mathrm{MXFP4}}(B) = 144 / (B + 143)$ (tight supremum at $(3^+, 1/4)$; $48/53$ at $B = 16$, $144/175$ at $B = 32$).
- **NVFP4 (`alphaNVFP4 B = min ((24 * B + 12) / (25 * B + 11)) (576 / (B + 575))`):**
  - `1 ≤ B ≤ 23`: $\alpha _ {\mathrm{NVFP4}}(B) = (24 B + 12) / (25 B + 11)$ (exact attainment at $(6, 5)$; $1$ at $B = 1$, $132/137$ at $B = 16$).
  - `B ≥ 24`: $\alpha _ {\mathrm{NVFP4}}(B) = 576 / (B + 575)$ (exact attainment at $(6, 1/4)$; $576/607$ at $B = 32$).
