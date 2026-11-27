# `adic-16`: Involutive Circulant Carry-Transfer & 2-Window Bit-Splitting Polyhedral Cone Engine for Mod-$m$ and Bitwise Popcount Classes (`circulant-carry-bit-splitting-cones`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): This work introduces and machine-checks **two reusable finite-to-infinite pure-silicon proof mechanisms** for binary popcount-residue classes $C _ {m, r} = \{ n \in \mathbb{N} : s _ 2(n) \equiv r \pmod m \}$, unifying exact group-ring carry algebra and polyhedral Farkas cone certification in standalone Lean 4.36.0 (zero Mathlib, zero `sorry`, zero `native_decide`, zero floating*

## For Mathematicians

This work introduces and machine-checks **two reusable finite-to-infinite pure-silicon proof mechanisms** for binary popcount-residue classes $C _ {m, r} = \{ n \in \mathbb{N} : s _ 2(n) \equiv r \pmod m \}$, unifying exact group-ring carry algebra and polyhedral Farkas cone certification in standalone Lean 4.36.0 (zero Mathlib, zero `sorry`, zero `native_decide`, zero floating-point values).

## For Non-Mathematicians

This work introduces and machine-checks **two reusable finite-to-infinite pure-silicon proof mechanisms** for binary popcount-residue classes $C _ {m, r} = \{ n \in \mathbb{N} : s _ 2(n) \equiv r \pmod m \}$, unifying exact group-ring carry algebra and polyhedral Farkas cone certification in standalone Lean 4.36.0 (zero Mathlib, zero `sorry`, zero `native_decide`, zero floating

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `CirculantCarryBitSplittingCones/Theorems.lean`, definitions in `CirculantCarryBitSplittingCones/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `hermitian_row0_telescope_symm` | **REUSABLE MECHANISM I (General Involutive Row-0 Telescoping & Palindromy Theorem):** If `H` is `rev`-Hermitian over `Z[Z/mZ]`, `v 0 = e_0`, and row 0 of `H` satisfies `H 0 j = delta_{0,j} e_0 + rev(v j)`, then: 1. `(H^(k+1) v)_0 = (H^k v)_0 + quadForm(v, H^k)` for all `k : Nat`, 2. `rev((H^k v)_0) = (H^k v)_0` for all `k : Nat`. |
| `mersenne_mod3_recurrence` | **THEOREM 1b (Exact 3-Term Recurrence & Exponential Positivity for Mod-3 Mersenne):** For ALL `k : Nat`: 1. `D_3(k + 3) = 4 * D_3(k + 2) + 4 * D_3(k + 1) - D_3(k)`, 2. `D_3(k) ≥ 4^k > 0`, hence class `0 (mod 3)` strictly dominates BOTH `1` and `2 (mod 3)` on every dyadic block `[0, 2^(3k))`. |
| `mersenne_mod6_dominance_breaks_at_2_pow_72` | **THEOREM 1c (Kernel-Checked Sharp Phase Transition at m = 6, N = 2^72):** Although `c_0(2^(6k)) > c_r(2^(6k))` for all `1 ≤ k ≤ 11` (up to `2^66 ≈ 7.38 × 10^19`), at `k = 12` (`N = 2^72 = 4,722,366,482,869,645,213,696`), Mod-6 Mersenne 0-dominance SHARPLY BREAKS with exact deficit `-4,543,260,596,431,345`. |
| `mersenne_palindromy_naive_involutions_fail` | Machine-checked infinite theorem `mersenne_palindromy_naive_involutions_fail` proved in pure Lean 4 `Init`. |
| `or_mul5_strict_evil_dominance` | **THEOREM 2 (Nonlinear Bitwise-OR Evil Dominance for `n /// 5*n`, ALL `N ≥ 1`):** For EVERY `N ≥ 1`, strictly more `n < N` have `s_2(n /// 5*n)` even than odd. |
| `mul3_newman_benchmark` | **THEOREM 4 (Classical Newman 1969 Benchmark Recovered in 9 Rows):** Demonstrates engine reuse across both linear (`3*n`) and nonlinear (`n /// 3*n`, `n /// 5*n`) binary carry transducers. |
| `hostile_mutation_U0_rejected` | Machine-checked infinite theorem `hostile_mutation_U0_rejected` proved in pure Lean 4 `Init`. |
| `engineII_three_way_sharpness` | **3-WAY SHARPNESS COUNTEREXAMPLES FOR ENGINE II:** Replacing `///` by `^^^`, replacing `///` by `&&&`, or replacing `c ∈ {3, 5}` by `c = 7` all break strict evil dominance immediately at `N = 3` (`evil = 1 < 2 = odious`). |

## Prior-Art Context

- - **Classical Literature Distinguished:** - **Gelfond (1968), Newman (1969), Coquet (1983), Grabner (1993), Drmota–Skałba (1995), Spiegelhofer–Wallner (2019):** Gelfond (1968) established asymptotic equidistribution of sum-of-digits residue classes in arithmetic progressions; Newman (1969), Coquet (1983), Grabner (1993), Drmota–Skałba (1995), and Spiegelhofer–Wallner (2019) studied linear multiplicative parity biases $\sum _ {n < N} (-1)^{s _ 2(c n)}$ and modular sum-of-digits correlations along arithmetic progressions and multiples. Here `mul3_newman_benchmark` is explicitly labeled as a classical benchmark verifying Engine II. - **Stolarsky
- Hostile-verified PASS by `referee-4`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).