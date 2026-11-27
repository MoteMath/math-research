# Formal Verification Audit (`cayley-hamilton-perron-annihilator`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built CayleyHamiltonPerronAnnihilator.Defs (3.0s)
✔ [3/7] Built CayleyHamiltonPerronAnnihilator.Theorems (21s)
✔ [4/7] Built CayleyHamiltonPerronAnnihilator (1.4s)
✔ [6/7] Built Solution (1.5s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.6s)
warning: Challenge.lean:7:8: declaration uses `sorry`
warning: Challenge.lean:13:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:35:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:45:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CayleyHamiltonPerronAnnihilator/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CayleyHamiltonPerronAnnihilatorChallenge.matAnn_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CayleyHamiltonPerronAnnihilatorChallenge.scaledVal_exact_valuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CayleyHamiltonPerronAnnihilatorChallenge.carrySumK_eq_obs' depends on axioms: [propext, Quot.sound]
'CayleyHamiltonPerronAnnihilatorChallenge.thm_Z5_and_K7_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'CayleyHamiltonPerronAnnihilatorChallenge.thm_C3_odd_part_mod4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CayleyHamiltonPerronAnnihilatorChallenge.thm_C5_pos_for_all_ge_8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CayleyHamiltonPerronAnnihilatorChallenge.sharpness_K23_fails' depends on axioms: [propext]
'CayleyHamiltonPerronAnnihilatorChallenge.sharpness_K7_Z5_shift' depends on axioms: [propext]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
