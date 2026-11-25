# Bit-Circuit Synthesis

Zero-Mathlib, zero-built-in-arithmetic Lean 4 formalization constructed directly from canonical binary words (`BBin` / `BPos`) and 1-bit multiplexer gates (`BBit`, `bmux`). Every theorem uses at most `propext` (no `Classical.choice`, no `Quot.sound`, no `Nat`/`Int`/`Bool` arithmetic primitives).

## Main results

The trusted statement file [`Challenge.lean`](Challenge.lean) highlights 8 universal carry-less $\mathbb{F} _ 2[x]$ and Artin-Schreier theorems proved directly on binary words:

- **Carry-less degree additivity (`bpos_clmul_deg_additive`):** For all `p q : BPos`, $\deg(p \otimes q) = \deg(p) + \deg(q)$.
- **Integral domain property (`bf2x_integral_domain`):** `bclmul x y = BBin.zero` iff `x = BBin.zero ∨ y = BBin.zero`.
- **Carried vs. carry-less degree-jump witness (`bcarried_vs_carryless_deg_jump_witness`):** Exact comparison between carry-less $3 \otimes 3 = 5$ (degree $2 = 1 + 1$) and carried $3 \cdot 3 = 9$ (degree $3 \ne 2$).
- **Artin-Schreier additivity and 2-to-1 fiber pairing (`bartin_schreier_add_hom`, `bartin_schreier_shift_one_inv`):** $\wp(x \oplus y) = \wp(x) \oplus \wp(y)$ and $\wp(x \oplus 1) = \wp(x)$ for $\wp(x) = x^2 \oplus x$.
- **Frobenius homomorphism (`bfrob2_xor_hom`):** $(x \oplus y)^2 = x^2 \oplus y^2$ in characteristic $2$.
- **Iterated Frobenius trace telescoping (`bfrob_trace_artin_schreier_telescope`):** $\mathrm{Tr} _ m(x^2 \oplus x) = x^{2^m} \oplus x$ for every tower height $m$.
- **Additive Hilbert's Theorem 90 (`bhilbert90_additive_trace_zero_mod`):** Modulo any $P _ m$ fixing $x^{2^m}$, $\mathrm{Tr} _ m(x^2 \oplus x) \equiv 0 \pmod{P _ m}$.

The library also contains the complete `1,799`-theorem universal bit-circuit synthesis suite in [`BitCircuitSynthesis/AutoEpoch6Complete1799Verify.lean`](BitCircuitSynthesis/AutoEpoch6Complete1799Verify.lean).

## Scope note

Any finite-width positivity or fixed-range integer checks inside supporting modules certify strictly their stated finite identities and say nothing about the zeros of $\zeta(s)$ or $L(s, \chi)$ over $\mathbb{Q}$.

## Building and checking

From inside `bit-circuit-synthesis/` (no Mathlib cache needed):

```sh
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

To run the full Palomar Comparator check on Linux:

```sh
bash ../.github/scripts/comparator-check.sh
```
