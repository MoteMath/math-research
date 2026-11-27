# Formal Verification Audit (`reversible-gate-lattice-flux`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.5s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:26:8: declaration uses `sorry`
warning: Challenge.lean:41:8: declaration uses `sorry`
warning: Challenge.lean:56:8: declaration uses `sorry`
warning: Challenge.lean:62:8: declaration uses `sorry`
warning: Challenge.lean:68:8: declaration uses `sorry`
warning: Challenge.lean:75:8: declaration uses `sorry`
warning: Challenge.lean:85:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `ReversibleGateLatticeFlux/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'ReversibleGateLatticeFluxChallenge.fluxCert_verify_sound' depends on axioms: [propext, Quot.sound]
'ReversibleGateLatticeFluxChallenge.fluxCert_open_segment_continuity' depends on axioms: [propext, Quot.sound]
'ReversibleGateLatticeFluxChallenge.fluxCert_ring_conserved_iter' depends on axioms: [propext, Quot.sound]
'ReversibleGateLatticeFluxChallenge.fredkin_cnot_iff_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReversibleGateLatticeFluxChallenge.fredkin_toffoli_conserved_all_widths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ReversibleGateLatticeFluxChallenge.fredkin_toffoli_reversible_all_widths' depends on axioms: [propext, Quot.sound]
'ReversibleGateLatticeFluxChallenge.double_fredkin_three_laws_all_widths' depends on axioms: [propext, Quot.sound]
'ReversibleGateLatticeFluxChallenge.subcnot_chiral_domain_wall_conserved_all_widths' depends on axioms: [propext,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
