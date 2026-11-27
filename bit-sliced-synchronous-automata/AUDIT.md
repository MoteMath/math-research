# Formal Verification Audit (`bit-sliced-synchronous-automata`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BitSlicedSynchronousAutomata.Defs (26s)
✔ [3/7] Built BitSlicedSynchronousAutomata.Theorems (53s)
✔ [4/7] Built BitSlicedSynchronousAutomata (1.2s)
✔ [6/7] Built Solution (1.3s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.3s)
warning: Challenge.lean:18:8: declaration uses `sorry`
warning: Challenge.lean:25:8: declaration uses `sorry`
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `BitSlicedSynchronousAutomata/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'BitSlicedSynchronousAutomataChallenge.checkCert_sound' depends on axioms: [propext, Quot.sound]
'BitSlicedSynchronousAutomataChallenge.bvProp_cert_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitSlicedSynchronousAutomataChallenge.thm_signed_quarter_sum_net_overflow_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedSynchronousAutomataChallenge.thm_unsigned_quarter_sum_no_overflow_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedSynchronousAutomataChallenge.thm_signed_eq_unsigned_quarter_sum_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedSynchronousAutomataChallenge.thm_signed_quarter_sum_mod_reconstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedSynchronousAutomataChallenge.thm_nested_avg_vs_quarter_sum_sandwich' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BitSlicedSynchronousAutomataChallenge.thm_gray_triple_zeckendorf_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
