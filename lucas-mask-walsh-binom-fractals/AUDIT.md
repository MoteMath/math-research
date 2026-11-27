# Formal Verification Audit (`lucas-mask-walsh-binom-fractals`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built LucasMaskWalshBinomFractals.Defs (5.3s)
✔ [3/7] Built LucasMaskWalshBinomFractals.Theorems (33s)
✔ [4/7] Built LucasMaskWalshBinomFractals (1.9s)
✔ [6/7] Built Solution (1.7s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.5s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:22:8: declaration uses `sorry`
warning: Challenge.lean:28:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `LucasMaskWalshBinomFractals/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'LucasMaskWalshBinomFractalsChallenge.delta_two_state_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'LucasMaskWalshBinomFractalsChallenge.bitUnit_sq_lift' depends on axioms: [propext, Quot.sound]
'LucasMaskWalshBinomFractalsChallenge.bitSmooth_pow_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'LucasMaskWalshBinomFractalsChallenge.walsh_bitSmooth_spike' depends on axioms: [propext, Classical.choice, Quot.sound]
'LucasMaskWalshBinomFractalsChallenge.walsh_lucas_binom_odd_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LucasMaskWalshBinomFractalsChallenge.walsh_lucas_binom_even_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LucasMaskWalshBinomFractalsChallenge.walsh_lucas_mixed_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LucasMaskWalshBinomFractalsChallenge.sharpness_squaring_jump_needs_spike_mask' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
