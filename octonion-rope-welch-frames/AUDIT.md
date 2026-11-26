# Formal Verification Audit (`octonion-rope-welch-frames`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-26

## Build & Challenge Checks

```text
$ lake build
✔ [2/10] Built OctonionRopeWelch.Defs (1.6s)
✔ [3/10] Built OctonionRopeWelch.RoPE (10s)
✔ [4/10] Built OctonionRopeWelch.Rigidity (12s)
✔ [5/10] Built OctonionRopeWelch.Welch (12s)
✔ [6/10] Built OctonionRopeWelch.Softmax (12s)
✔ [7/10] Built OctonionRopeWelch (1.0s)
✔ [9/10] Built Solution (1.2s)
Build completed successfully (10 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.2s)
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:55:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
warning: Challenge.lean:79:8: declaration uses `sorry`
warning: Challenge.lean:90:8: declaration uses `sorry`
warning: Challenge.lean:108:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the six intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide`/`lemma` anywhere in `OctonionRopeWelch/`, `OctonionRopeWelch.lean`, or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'OctonionRopeWelchChallenge.quaternion_pow2_rigidity_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OctonionRopeWelchChallenge.pythagorean_and_octonion_rope_exact_orthogonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OctonionRopeWelchChallenge.welch_frame_energy_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'OctonionRopeWelchChallenge.welch_tight_sparse_ternary_frames_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OctonionRopeWelchChallenge.softmax_topk_gap_l1_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'OctonionRopeWelchChallenge.softmax_quantized_logit_l1_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All six headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `Lean.ofReduceBool` and zero `sorryAx` — matching `comparator.json` with `enable_nanoda: true`.
