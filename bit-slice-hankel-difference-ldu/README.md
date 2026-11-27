# Bit Slice Hankel Difference LDU - Laplace difference identities and exact mod-8 and 2-adic laws for Hankel determinants of bitwise automatic sequences (`bit-slice-hankel-difference-ldu`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of Laplace-type Hankel determinant operators over exact integers, applied to bitwise automatic sequences. Proves an affine-shift identity, the closed system of three Hankel families with odd-parameter master invariants (mod-8 period 8 and nonsingularity for every n), vanishing at odd sizes and signed-square values at even sizes for the ruler family, the exact 2-adic valuation 2 floor(n/2) of the signed ruler Hankel determinant, and a popcount-power Hankel factorization.*

## For Mathematicians

We construct a reusable, pure-silicon, integer-native **Bit-Slice Hankel Congruence & Difference LDU Factorization Engine** in standalone Lean 4.36.0 (`Proof.lean`, pure `Init`, zero Mathlib, zero floats, zero division, zero `sorry`, zero `native_decide`). Instead of analytic continued fractions, Padé approximants, or floating-point spectral decompositions, the engine operates strictly by **LSB even-odd index permutations** (`eoPerm`) and **unit-triangular integer congruences** $L H L^{\top}$ (`det_unit_lower_cong`), yielding four universal integer determinant operators (**Operators A, B, C, D**) valid for arbitrary sequences over $\mathbb{Z}$ and all matrix sizes $n \ge 0$. Applying these four operators to the 3-parameter binary-valuation automatic sequence family closes a **6-equation 3-state exact integer bit-slice automaton** for $(A _ n, B _ n, C _ n) = (\det H _ n(a), \det H _ n(\Delta a), \det H _ n(\Delta^2 a))$ and discharges f

## For Non-Mathematicians

A complete, sorry-free, pure-Init (zero Mathlib) Lean 4 formalization of Laplace-type Hankel determinant operators over exact integers, applied to bitwise automatic sequences. Proves an affine-shift identity, the closed system of three Hankel families with odd-parameter master invariants (mod-8 period 8 and nonsingularity for every n), vanishing at odd sizes and signed-square values at even sizes for the ruler family, the exact 2-adic valuation 2 floor(n/2) of the signed ruler Hankel determinant, and a popcount-power Hankel factorization.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BitSliceHankelDifferenceLdu/Theorems.lean`, definitions in `BitSliceHankelDifferenceLdu/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `hankel_affine_shift` | Theorem 1 (Affine-shift Laplace identity): det Hankel(alpha a + beta) of size m + 1 equals alpha^(m+1) det Hankel(a) + beta alpha^m det Hankel(second difference of a) of size m. |
| `ecSeq_odd_master_invariant` | Theorem 2 (Odd-parameter master invariant): for odd c, alpha, beta, the three Hankel determinant families satisfy explicit parity, mod-4 and mod-8 invariants for every n. |
| `ecSeq_odd_mod8_periodic` | Theorem 3 (Period-8 law): for odd parameters the Hankel determinant of ecSeq is periodic modulo 8 in n with period 8. |
| `ecSeq_odd_nonsingular` | Theorem 4 (Nonsingularity): for odd parameters every Hankel determinant of ecSeq is nonzero. |
| `ruler_family_odd_zero` | Theorem 5 (Ruler odd vanishing): the Hankel determinant of the ruler family ecSeq 0 alpha beta vanishes at every odd size 2m + 1. |
| `ruler_family_even_signed_square` | Theorem 6 (Ruler even signed square): at every even size 2(m + 1) the ruler-family Hankel determinant is altSign(m + 1) times a perfect square. |
| `signed_ruler_v2_exact` | Theorem 7 (Exact 2-adic valuation): for n not congruent to 2 modulo 4, the Hankel determinant of the signed ruler sequence is nonzero with 2-adic valuation exactly 2 floor(n/2). |
| `popPow_hankel_factorization` | Theorem 8 (Popcount-power factorization): the Hankel determinant of r^popcount factors into two Hankel determinants of half size. |

## Prior-Art Context

- Builds on classical binary arithmetic and finite-state / algebraic verification methods; formalizes a pure-Init Lean 4 infinite proof engine with zero Mathlib dependencies.
- Hostile-verified PASS by `referee-3`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).