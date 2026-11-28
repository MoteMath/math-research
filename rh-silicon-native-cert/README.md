Finite bit-width checks say nothing about all bit-widths $w \in \mathbb{N}$.

# Pure-Silicon Binary Certification Bundle (`SiliconNativeCert`)

A self-contained, pure-`Init` Lean `4.34.1` (`"packages": []`) Palomar certification bundle proving **8 atomic discrete theorems** with **25/25 definitions pinned** in [`comparator.json`](./comparator.json) (`enable_nanoda = true`, zero `sorry`, zero custom axioms, zero continuum or external library imports).

## Scope and Epistemic Status

- **What this bundle proves unconditionally:** Exact discrete soundness, congruence positivity, universal bit-stream transducer equivalence across all unbounded bit-widths $w \in \mathbb{N}$, carry-move parity flips, factor-list invariance, and formal obstruction theorems (`finite_window_blindness`, `bounded_envelope_obstruction`) showing why finite-width bit-circuit searches alone cannot imply asymptotic all-$w$ bounds.
- **What this bundle does NOT claim:** It does not prove any open conjecture about prime distributions or unbounded bit-width integer envelopes.

## Pinned Atomic Theorems (`Challenge.lean` / `Solution.lean`)

1. `SiliconNativeCert.quadForm_pos_of_strictDiagDom` — Scaled strict diagonal dominance of a symmetric integer matrix $G$ implies $v^T G v > 0$ for every nonzero integer vector $v$.
2. `SiliconNativeCert.psync4_sound` — Any 16-bit product-state invariant bitmask passing `checkPsyncInv4` certifies exact bit-stream equality of two 4-state binary carry transducers for every input list of every length $w \in \mathbb{N}$.
3. `SiliconNativeCert.universal_carry_decomp` — Universal all-bit-width binary addition identity $x + y = (x \oplus y) + 2(x \land y)$ proved directly via `psync4_sound`.
4. `SiliconNativeCert.universal_step_envelope_implies_target` — Any uniform step envelope bounded by $C \cdot \mathrm{sqrtBit}(w) + B$ implies the discrete square-root scale target `SqrtScaleTarget f`.
5. `SiliconNativeCert.finite_window_blindness` — For any function $f : \mathbb{N} \to \mathbb{N}$ and any finite window $W _ 0$, there exists $g$ agreeing with $f$ on all $w \le W _ 0$ that violates `SqrtScaleTarget g`.
6. `SiliconNativeCert.bounded_envelope_obstruction` — No globally bounded envelope $E(w) \le B$ can upper-bound an unbounded function $f$.
7. `SiliconNativeCert.carryMove_flips_parity` — Every discrete carry-move flips factor-list parity.
8. `SiliconNativeCert.oneStepSplit_preserves_valid` — Every valid one-step integer split preserves `validFactorList N`.

## Verification Commands

```bash
lake build
lake build Challenge
lake env lean PrintAxioms.lean
```

All eight theorems depend strictly on Lean's standard axioms (`[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`). Companion non-vacuity witnesses (`Sanity.lean`) confirm every predicate is inhabited.
