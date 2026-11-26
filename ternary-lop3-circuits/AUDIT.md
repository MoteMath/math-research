# Formal Verification Audit (`ternary-lop3-circuits`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Build & Challenge Checks

```text
$ lake build
✔ [3/7] Built TernaryLop3Circuits.Theorems (7.7s)
✔ [4/7] Built TernaryLop3Circuits (1.2s)
✔ [6/7] Built Solution (1.3s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.3s)
warning: Challenge.lean:27:8: declaration uses `sorry`
warning: Challenge.lean:43:8: declaration uses `sorry`
warning: Challenge.lean:63:8: declaration uses `sorry`
warning: Challenge.lean:82:8: declaration uses `sorry`
warning: Challenge.lean:105:8: declaration uses `sorry`
warning: Challenge.lean:116:8: declaration uses `sorry`
warning: Challenge.lean:126:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the seven intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `TernaryLop3Circuits/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'TernaryLop3Challenge.unpack_3t5b_sound_and_surjective' depends on axioms: [propext, Quot.sound]
'TernaryLop3Challenge.unpack_3t5b_six_gate_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TernaryLop3Challenge.unpack_5t8b_sound_and_surjective' depends on axioms: [propext, Quot.sound]
'TernaryLop3Challenge.unpack_5t8b_four_var_impossibility' depends on axioms: [propext, Classical.choice, Quot.sound]
'TernaryLop3Challenge.ternary_int4_exact5_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TernaryLop3Challenge.ternary_fp4_exact5_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TernaryLop3Challenge.csa32_popcnt_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both circuit soundness/surjectivity theorems (`unpack_3t5b_sound_and_surjective` and `unpack_5t8b_sound_and_surjective`) are completely constructive (`[propext, Quot.sound]` only), and all seven headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true` (zero `Lean.ofReduceBool`).
