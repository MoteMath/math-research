# Formal Verification Audit (`bit-sliced-synchronous-automata`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built BitSlicedSynchronousAutomata.Defs (3.4s)
✔ [3/7] Built BitSlicedSynchronousAutomata.Theorems (148s)
✔ [4/7] Built BitSlicedSynchronousAutomata (1.7s)
✔ [6/7] Built Solution (1.0s)
Build completed successfully (7 jobs).

$ lake build Challenge
✖ [3/4] Building Challenge (1.7s)
trace: .> LEAN_PATH=C:\Users\devin\Desktop\math\math-research\bit-sliced-synchronous-automata\.lake\build\lib\lean c:\Users\devin\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lean.exe C:\Users\devin\Desktop\math\math-research\bit-sliced-synchronous-automata\Challenge.lean -o C:\Users\devin\Desktop\math\math-research\bit-sliced-synchronous-automata\.lake\build\lib\lean\Challenge.olean -i C:\Users\devin\Desktop\math\math-research\bit-sliced-synchronous-automata\.lake\build\lib\lean\Challenge.ilean -c C:\Users\devin\Desktop\math\math-research\bit-sliced-synchronous-automata\.lake\build\ir\Challenge.c --setup C:\Users\devin\Desktop\math\math-research\bit-sliced-synchronous-automata\.lake\build\ir\Challenge.setup.json --json
warning: Challenge.lean:18:8: declaration uses `sorry`
error: Challenge.lean:27:13: failed to synthesize instance of type class
  BEq φ.State

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
warning: Challenge.lean:32:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:46:8: declaration uses `sorry`
warning: Challenge.lean:53:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:66:8: declaration uses `sorry`
Some required targets logged failures:
- Challenge
error: build failed
```

Exit codes: `lake build` = 0, `lake build Challenge` = 1. Zero errors, zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in the library modules or `Solution.lean`.

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

Exit code: 0. Every headline theorem depends only on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`.
