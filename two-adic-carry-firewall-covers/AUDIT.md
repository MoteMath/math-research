# Formal Verification Audit (`two-adic-carry-firewall-covers`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
✔ [2/7] Built TwoAdicCarryFirewallCovers.Defs (4.4s)
✔ [3/7] Built TwoAdicCarryFirewallCovers.Theorems (30s)
✔ [4/7] Built TwoAdicCarryFirewallCovers (1.8s)
✔ [6/7] Built Solution (2.2s)
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (2.1s)
warning: Challenge.lean:16:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:29:8: declaration uses `sorry`
warning: Challenge.lean:34:8: declaration uses `sorry`
warning: Challenge.lean:39:8: declaration uses `sorry`
warning: Challenge.lean:44:8: declaration uses `sorry`
warning: Challenge.lean:49:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors, zero warnings outside the eight intentional `sorry` placeholders in `Challenge.lean`, and zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `TwoAdicCarryFirewallCovers/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'TwoAdicCarryFirewallCoversChallenge.coverTree_sound' depends on axioms: [propext, Quot.sound]
'TwoAdicCarryFirewallCoversChallenge.T4_global_convergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicCarryFirewallCoversChallenge.T5_global_convergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicCarryFirewallCoversChallenge.X21_global_convergence_to_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoAdicCarryFirewallCoversChallenge.X33_global_convergence_to_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoAdicCarryFirewallCoversChallenge.grayQuad2_val_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicCarryFirewallCoversChallenge.grayQuad2_neq_shift15' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoAdicCarryFirewallCoversChallenge.T8_nontrivial_6cycle_never_drops' depends on axioms: [propext, Quot.sound]
```

All eight headline theorems depend exclusively on Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), matching `comparator.json` with `enable_nanoda: true`. No `sorryAx`, no `Lean.ofReduceBool`.
