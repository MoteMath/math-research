# Formal Verification Audit (`two-adic-biscaled-det-valuation`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Replayed Challenge
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:50:8: declaration uses `sorry`
warning: Challenge.lean:58:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
warning: Challenge.lean:74:8: declaration uses `sorry`
warning: Challenge.lean:79:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `TwoAdicBiscaledDetValuation/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'TwoAdicBiscaledDetValuationChallenge.v2_det_biscaled_elimination_engine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoAdicBiscaledDetValuationChallenge.v2_det_perturbation_stability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoAdicBiscaledDetValuationChallenge.mob2_pop_and' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicBiscaledDetValuationChallenge.theorem_1A_supercritical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoAdicBiscaledDetValuationChallenge.theorem_1B_critical_I' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicBiscaledDetValuationChallenge.theorem_1C_critical_II' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicBiscaledDetValuationChallenge.theorem_n1_jump' depends on axioms: [propext, Quot.sound]
'TwoAdicBiscaledDetValuationChallenge.sharpness_S3_infinite_breakdown_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
