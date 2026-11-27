# Formal Verification Audit (`two-way-bit-transducer-inverses`)

**Toolchain:** `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib)  
**Audit date:** 2026-11-27

## Build & Challenge Checks

```text
$ lake build
Build completed successfully (7 jobs).

$ lake build Challenge
⚠ [3/4] Built Challenge (1.9s)
warning: Challenge.lean:17:8: declaration uses `sorry`
warning: Challenge.lean:24:8: declaration uses `sorry`
warning: Challenge.lean:30:8: declaration uses `sorry`
warning: Challenge.lean:36:8: declaration uses `sorry`
warning: Challenge.lean:42:8: declaration uses `sorry`
warning: Challenge.lean:48:8: declaration uses `sorry`
warning: Challenge.lean:54:8: declaration uses `sorry`
warning: Challenge.lean:60:8: declaration uses `sorry`
Build completed successfully (4 jobs).
```

Zero errors and zero warnings outside the intentional `sorry` placeholders in `Challenge.lean`; zero `sorry`/`axiom`/`admit`/`native_decide` anywhere in `TwoWayBitTransducerInverses/` or `Solution.lean`.

## Verbatim `#print axioms` Output

```text
$ lake env lean scripts/PrintAxioms.lean
'TwoWayBitTransducerInversesChallenge.checkCert_sound_bv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoWayBitTransducerInversesChallenge.skipFlip2_period3_bv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoWayBitTransducerInversesChallenge.skipFlip2_shifted_period6_bv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoWayBitTransducerInversesChallenge.skipFlip2_fwd_period_pow2' depends on axioms: [propext, Quot.sound]
'TwoWayBitTransducerInversesChallenge.runTriggerTwoWay_left_inv' depends on axioms: [propext, Quot.sound]
'TwoWayBitTransducerInversesChallenge.runTrigger_period6_all_m_bv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoWayBitTransducerInversesChallenge.runSkipFlip_period6_all_m_bv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TwoWayBitTransducerInversesChallenge.coupled_parityDelay_exact_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every headline theorem depends only on axioms from `{propext, Classical.choice, Quot.sound}`, matching `comparator.json` with `enable_nanoda: true`.
