# Bit-Sliced Carry-Holonomy 2-Adic Lifting Engine (`bit-sliced-carry-holonomy-2adic`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism:** **Bit-Sliced Carry-Holonomy 2-Adic Lifting Engine (`CarryHolonomyEngine`)** Classical 2-adic Hensel lifting and Lifting-the-Exponent (LTE) rely on differentiability or constant Jacobian congruences modulo $4$. Carry-twisted recurrences mixing arithmetic addition (`+`, `*`) with bitwise operations (`^`, `&`, `<<`) at every bit scale violate constant-derivative hyp*

## For Mathematicians

**Mechanism:** **Bit-Sliced Carry-Holonomy 2-Adic Lifting Engine (`CarryHolonomyEngine`)** Classical 2-adic Hensel lifting and Lifting-the-Exponent (LTE) rely on differentiability or constant Jacobian congruences modulo $4$. Carry-twisted recurrences mixing arithmetic addition (`+`, `*`) with bitwise operations (`^`, `&`, `<<`) at every bit scale violate constant-derivative hypotheses (their finite differences oscillate between $1$ and $3 \pmod 4$), yet exhibit exact infinite 2-adic valuation and modular period-doubling laws. Our engine replaces analytic/van der Put machinery with a **pure-silicon finite-to-infinite bit-slicing compiler** built directly on `Nat.testBit`, exact GF(2) parity sums `xorRange`, and `TPerm` (1-Lipschitz, bit-$k$ fiber-invertible maps on $\mathbb{N}$): 1. **Cycle-Holonomy Bifurcation Law (`iter_testBit_eq_holonomy`, `holonomy_double_cycle`):** For any `TPerm` $f$, any bit level $k$, and any cycle length $L$ cl

## For Non-Mathematicians

**Mechanism:** **Bit-Sliced Carry-Holonomy 2-Adic Lifting Engine (`CarryHolonomyEngine`)** Classical 2-adic Hensel lifting and Lifting-the-Exponent (LTE) rely on differentiability or constant Jacobian congruences modulo $4$. Carry-twisted recurrences mixing arithmetic addition (`+`, `*`) with bitwise operations (`^`, `&`, `<<`) at every bit scale violate constant-derivative hyp

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BitSlicedCarryHolonomy2adic/Theorems.lean`, definitions in `BitSlicedCarryHolonomy2adic/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `iter_testBit_eq_holonomy` | **Core Engine Theorem A (`holonomy_lift_step`)**: For any `TPerm f`, any level `k`, and any `L`, the bit `k` of `iter f L x0` is exactly `x0.testBit k ^^ holonomy f k x0 L`! |
| `majority_carry_holonomy` | **Core Engine Theorem B1 (`majority_carry_holonomy`)**: For ANY `TPerm Φ`, ANY `c`, and ANY doubled cycle `2L` at level `k+1` (with `L` even): `holonomy (Φ · + c) (k+1) x0 (2*L)` equals the XOR of the twist derivative `β` and the carry-overflow parity over the half-cycle `y_i = iter T i x0 % 2^k`! |
| `tower_to_min_period` | **Core Engine Theorem C3 (Exact Minimal Periodicity Mod `2^(k0 + m)`)**: Under the certified doubling tower plus base minimality (`∀ 0 < r < L0, iter f r 0 % 2^k0 ≠ 0`), for EVERY `m : Nat`, `L0 * 2 ^ m` is the **EXACT minimal period** of `iter f · 0` modulo `2 ^ (k0 + m)`! |
| `grayCarry_ge2_odd_period` | **Theorem 1A (Gray-Carry Ergodicity for `s ≥ 2`, odd `c`)**: For ALL `s ≥ 2`, ALL odd `c`, and ALL `k : Nat`, the orbit of `0` modulo `2^k` has exact minimal period `2^k` (the Lean statement is: `iter (grayCarryStep s c) (2^k) 0 % 2^k = 0` and no smaller positive `d` returns to `0`). The valuation law `v2 (iter (grayCarryStep s c) n 0) = v2 n` is not part of this statement. |
| `quadAnd_v2` | For `1 <= s < t`, `t >= 3`, `c != 0`, `n != 0`: `v2 (iter (quadAndStep s t c) n 0) = v2 c + v2 n`, where `quadAndStep` is the quadratic AND-carry recurrence `b_{n+1} = Psi_{s,t}(b_n) + c`. |
| `affineXor_even_v2` | **Theorem 3B (Affine-XOR Exact Valuation Law for ALL even `A ≥ 2`, ALL `c ≥ 1`, ALL `n ≥ 1`)**: `v2 (iter (affineXorStep A c) n 0) = if n % 2 = 1 then v2 c else v2 n + v2 c + v2 A - 1`! |
| `sharpness_affineXor_A0_period2` | **Sharpness 2 (`A = 0` in Affine-XOR, i.e. `a_{n+1} = a_n ^^^ c`)**: `A = 0` has zero holonomy at every level: exact period 2 forever (`d_{2m} = 0`, `d_{2m+1} = c`)! |
| `sharpness_carryless_gray_period_collapse` | Machine-checked finite instance: for `carrylessGrayStep 1`, `iter _ 4 0 = 8`, so `v2 = 3` while `v2 1 + v2 4 = 2`: the carried valuation law fails for the carry-less step. |

## Prior-Art Context

- - **Relation to Classical T-Function Literature (Anashin 1994/2002; Larin 2002; Klimov–Shamir 2002/2004; Anashin–Khrennikov 2009, Ch. 4):** Anashin (1994, 2002) and Anashin–Khrennikov (2009, Ch. 4, *Applied Algebraic Dynamics*) characterized measure-preserving and ergodic (single-cycle mod $2^k$) 1-variable 1-Lipschitz maps on $\mathbb{Z} _ 2$ via van der Put series coefficients; Larin (2002) characterized transitive polynomial/T-function recurrences modulo $2^k$; and Klimov–Shamir (2002, 2004) constructed cryptographic single-cycle T-functions of the form $x + (x^2 \lor C)$. Our engine differs fundamentally in three respects: 1. **Non-ergodi
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).