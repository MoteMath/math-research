# Formal Verification Audit (`cross-thread-silicon-meta-bridge`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built CrossThreadSiliconMetaBridge.Defs (3.1s)
✔ [3/7] Built CrossThreadSiliconMetaBridge.Theorems (15s)
✔ [4/7] Built CrossThreadSiliconMetaBridge (1.5s)
✔ [6/7] Built Solution (1.5s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.5s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:13:8: declaration uses `sorry`
warning: Challenge.lean:19:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:31:8: declaration uses `sorry`
warning: Challenge.lean:37:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `CrossThreadSiliconMetaBridge/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'CrossThreadSiliconMetaBridgeChallenge.sumPow2_eq_sumRange' depends on axioms: [propext, Quot.sound]
'CrossThreadSiliconMetaBridgeChallenge.xorConv_quadForm_eq_wht' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CrossThreadSiliconMetaBridgeChallenge.prefixTree_walsh_bandlimited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CrossThreadSiliconMetaBridgeChallenge.transferRec2_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CrossThreadSiliconMetaBridgeChallenge.rawCarry_c1_indefinite_all_w' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CrossThreadSiliconMetaBridgeChallenge.thueMorse_inc_mod4_all_w' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CrossThreadSiliconMetaBridgeChallenge.demoAdicTree_sharp_at_freq4' does not depend on any axioms
'CrossThreadSiliconMetaBridgeChallenge.mutation_reject_modSubspace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
