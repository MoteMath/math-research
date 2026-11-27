# Formal Verification Audit (`binary-partition-window-automata`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BinaryPartitionWindowAutomata.Defs (2.8s)
✔ [3/7] Built BinaryPartitionWindowAutomata.Theorems (50s)
✔ [4/7] Built BinaryPartitionWindowAutomata (1.7s)
✔ [6/7] Built Solution (1.8s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.7s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:13:8: declaration uses `sorry`
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:20:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:33:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BinaryPartitionWindowAutomata/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BinaryPartitionWindowAutomataChallenge.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryPartitionWindowAutomataChallenge.b5_forbids_three_mod4_via_dfa' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BinaryPartitionWindowAutomataChallenge.b4_coupled_8n_5_mod4' depends on axioms: [propext, Classical.choice, Quot.sound]
'BinaryPartitionWindowAutomataChallenge.mutation_rejects_bad_q0' depends on axioms: [propext]
'BinaryPartitionWindowAutomataChallenge.br_universal_mod4_carry_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BinaryPartitionWindowAutomataChallenge.sharpness_r3_even_v2' does not depend on any axioms
'BinaryPartitionWindowAutomataChallenge.sharpness_b5_fails_mod8' does not depend on any axioms
'BinaryPartitionWindowAutomataChallenge.sharpness_gap023_offset17_fails' does not depend on any axioms
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
