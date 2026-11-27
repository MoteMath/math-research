# Formal Verification Audit (`dyadic-jsr-polytope-monoid-checker`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built DyadicJsrPolytopeMonoidChecker.Defs (4.8s)
✔ [3/7] Built DyadicJsrPolytopeMonoidChecker.Theorems (7.8s)
✔ [4/7] Built DyadicJsrPolytopeMonoidChecker (1.7s)
✔ [6/7] Built Solution (2.6s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.2s)
warning: Challenge.lean:8:8: declaration uses `sorry`
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:51:8: declaration uses `sorry`
warning: Challenge.lean:59:8: declaration uses `sorry`
warning: Challenge.lean:67:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `DyadicJsrPolytopeMonoidChecker/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'DyadicJsrPolytopeMonoidCheckerChallenge.switched_polytope_sound' depends on axioms: [propext, Quot.sound]
'DyadicJsrPolytopeMonoidCheckerChallenge.convex_hull_infinite_alphabet_sound' depends on axioms: [propext, Quot.sound]
'DyadicJsrPolytopeMonoidCheckerChallenge.periodic_eigen_sound' depends on axioms: [propext, Quot.sound]
'DyadicJsrPolytopeMonoidCheckerChallenge.thm1_convex_hull_contraction' depends on axioms: [propext, Quot.sound]
'DyadicJsrPolytopeMonoidCheckerChallenge.thm1_sharpness_unbounded' depends on axioms: [propext, Quot.sound]
'DyadicJsrPolytopeMonoidCheckerChallenge.thm3_signed_cone_subradius' depends on axioms: [propext, Quot.sound]
'DyadicJsrPolytopeMonoidCheckerChallenge.thm4_unconstrained_lower' depends on axioms: [propext, Quot.sound]
'DyadicJsrPolytopeMonoidCheckerChallenge.mut8_bad_naf_dfa_rejected' depends on axioms: [propext, Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
