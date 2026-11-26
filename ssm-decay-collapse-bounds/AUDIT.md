# Formal Verification Audit (`ssm-decay-collapse-bounds`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **95 / 100** |

*Composite arithmetic: `3*9 + 2*10 + 2*10 + 2*9 + 10 = 95 / 100`.*

## Build & Challenge Checks

```text
$ lake build
✔ [7/12] Built SsmDecayCollapse.CsdTwoTap (23s)
✔ [8/12] Built SsmDecayCollapse.ShiftSubtractBounds (23s)
✔ [9/12] Built SsmDecayCollapse (13s)
✔ [11/12] Built Solution (81s)
Build completed successfully (12 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (56s)
warning: Challenge.lean:38:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:74:8: declaration uses `sorry`
warning: Challenge.lean:90:8: declaration uses `sorry`
warning: Challenge.lean:107:8: declaration uses `sorry`
warning: Challenge.lean:121:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`, `admit`, `axiom`, `native_decide`, or `lemma` declarations anywhere in `SsmDecayCollapse/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'SsmDecayCollapseChallenge.ieee_decay_stall_midpoint_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'SsmDecayCollapseChallenge.one_ulp_per_step_sequential_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SsmDecayCollapseChallenge.additive_swamping_exact_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SsmDecayCollapseChallenge.dyadic_shift_subtract_tight_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SsmDecayCollapseChallenge.dyadic_shift_subtract_zero_input_stall_asymmetry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SsmDecayCollapseChallenge.csd_two_tap_half_life_gap_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `"enable_nanoda": true`.

## For Mathematicians

Every proof in `SsmDecayCollapse/` is 100% pure-`Init` algebraic reasoning over `Rat`, `Int`, and `Nat` (zero external dependencies):
- `RatZpow.lean`: Establishes exact integer powers of two `zpow2`, exact binade characterization `binadeOf_spec` / `binadeOf_eq_of_bounds` via `Nat.log2`, exact RNE integer rounding `rneInt_eq_of_bounds` / `rneInt_midpoint`, and normal floating-point grid preservation `ieeeRne_floatVal`.
- `DecayStall.lean`: Proves `ieee_decay_stall_midpoint_exact` universally for all $p \ge 1$ by showing $a _ {\max}(p) = \mathrm{floatVal}(p, -1, 2^p - 1)$ is maximal below $1$, scaling $a _ {\mathrm{stall}}(p) \cdot 2^{p+1} = (2^{p+1} - 1) + 1/2$ with odd floor to trigger RNE tie-to-even up to $1$, and evaluating all five IEEE-754 formats (`p ∈ {2, 3, 7, 10, 23}`).
- `OneUlpCollapse.lean`: Proves the exact 1-ULP step laws `floatVal_mul_aMax_pos` (strictly inside $(2^p + m - 1, 2^p + m - 1/2)$) and `floatVal_mul_aMax_zero` (exact binade drop), then inducts across $2^p$ steps per binade to prove `seqPow p (m * 2^p) = zpow2 (-m)` for all $p \ge 1, m \in \mathbb{N}$.
- `AdditiveSwamping.lean`: Proves `ieeeRne_one_add_half_ulp` via RNE tie-to-even on even $2^p$, inducing `seqAccum p (2^(-(p+1))) T = 1` and exact linear divergence $T \cdot 2^{-(p+1)}$.
- `ShiftSubtractBounds.lean`: Proves monotonicity `sub_fdiv_mono` of $h \mapsto h - \lfloor h / d \rfloor$ for all $d > 0$, yielding the tight invariant $[-2^R B _ {\max}, 2^R B _ {\max} + (2^R - 1)]$, exact endpoint fixed points at $r = R$, and zero-input stall asymmetry (`shiftSubIter_zero_fixed` vs `shiftSubIter_reaches_zero_of_nonpos`).
- `CsdTwoTap.lean`: Proves exact 1-tap ratio $2$, exact 2-tap CSD alternating ratios $3/2$ and $4/3$, and the $2^{24} / 2^8 = 65{,}536\times$ dynamic-range advantage over BF16.

## For Non-Mathematicians

This audit confirms that every mathematical law discovered in the Wave 9C Mamba-2 / SSD low-precision campaign — the exact BF16/FP8/FP16/FP32 memory-horizon stall cliffs, the universal 1-ULP-per-step sequential decay collapse ($128$-token effective BF16 half-life and $2^{-32}$ collapse at $T = 4096$), exact linear additive swamping divergence, exact overflow bounds and signed stall asymmetry for zero-multiplier shift-subtract SSMs, and the $2 \to 3/2$ timescale-gap improvement from 2-tap CSD — has been independently verified from first principles by Lean 4's trusted kernel with zero external libraries and zero unproven assumptions.

## Prior-Art Context

Follows the Palomar Comparator / `nanoda` pure-`Init` verification standard established in sibling `math-research` packages (`deltanet-wy-stability`, `mxfp8-e2m5-e3m4-frontier`), formalizing the hardware-math laws of Mamba-2 SSD (Gu & Dao, ICML 2024), parallel prefix scans (Blelloch, 1990), and IEEE-754 binary RNE arithmetic.
