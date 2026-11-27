# Coupled 2-Variable Reversible T-Function Orbit-Lifting Engine (`coupled-s4-tfunction-orbits`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): non-abelian $S _ 4 = \mathrm{AGL}(2, \mathbb{F} _ 2)$ fiber-monodromy orbit-lifting engine for coupled 2-variable reversible T-functions, proving $D _ 4$ cocycle decoupling, an infinite-dimensional functional full-period family, the universal no-shear obstruction, exact $3 ^ {\mathrm{popcount}(x)}$ twisted ternary odometer partitions, and a hybrid two-cycle partition across all bit-widths, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

For any coupled 2-variable causal T-function $T$ on $\mathrm{BitVec}\; w \times \mathrm{BitVec}\; w$, lifting from width $w$ to $w + 1$ acts on the top-bit fiber $\mathbb{B} \times \mathbb{B}$ by permutations in $S _ 4 = \mathrm{AGL}(2, \mathbb{F} _ 2)$. We prove the general **orbit-lifting theorem** (`orbit_lift_exact_period`): a base orbit of exact period $L$ whose monodromy permutation has exact period $d$ on a fiber point lifts to an exact orbit of period $d \cdot L$. Restricting to the dihedral subgroup $D _ 4$ of sheared translations yields a sharp parity criterion (`full_period_of_D4_parity`) and **$D _ 4$ cocycle decoupling**: for arbitrary causal perturbations $P, Q, R$, `family1 P Q R` achieves full period $4 ^ w$ at every width $w$ (`family1_full_period`).

Conversely, we prove the **universal no-shear obstruction** (`no_shear_never_full_period`): if every fiber action is a pure translation (zero shear), then $T _ w ^ {2 ^ w} = \mathrm{id}$ and full period $4 ^ w$ is impossible at every width $w \ge 1$. Using the order-3 elements of $S _ 4 \setminus D _ 4$, we construct the **Twisted Ternary Odometer** (`ternPoly_exact_cycle_partition`, `ternTwistY_exact_partition`), partitioning all $4 ^ w$ states into exact cycles of length $3 ^ {\mathrm{popcount}(x)}$ even under twists that destroy the classical $x \mathbin{|} y$ invariant (with a subtle $w = 5$ sharpness decoy `ternSharpX_breaks_at_w5`), plus a hybrid two-cycle family of exact lengths $4 ^ {w'}$ and $3 \cdot 4 ^ {w'}$ (`hybridTwoCycle_exact_two_cycles`).

## For Non-Mathematicians

Imagine a digital counter that updates two $w$-bit registers at once using only fast bit-sliced operations (addition, XOR, AND, multiplication). Can it cycle through all $4 ^ w$ pairs before repeating? We prove that if the top bits only ever flip without mixing between the two registers, it is mathematically impossible at every bit-width. Adding a single cross-register "shear" flip unlocks a huge infinite family of full-cycle counters, while a 3-way rotation of the top bits splits the state space into exact cycles of length $3 ^ k$ for every width.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `CoupledS4TfunctionOrbits/Theorems.lean`, definitions in `CoupledS4TfunctionOrbits/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `orbit_lift_exact_period` | If base state $s$ has exact period $L$ at width $w$ and its fiber monodromy has exact period $d$ on $p$, then the lifted state $(p, s)$ has exact period $d \cdot L$ at width $w + 1$. |
| `d4Elem_is_4cycle_iff` | An element of the dihedral fiber group $D _ 4$ acts as a single 4-cycle on $\mathbb{B} \times \mathbb{B}$ if and only if both its shear bit $\lambda$ and translation parity bit $\beta$ are `true`. |
| `full_period_of_D4_parity` | Any $D _ 4$-fibered coupled T-function whose global shear and translation XOR-parities are `true` at every width achieves full period $4 ^ w$ on every state. |
| `no_shear_never_full_period` | No coupled T-function whose fibers are pure translations can achieve full period $4 ^ w$ at any width $w \ge 1$. |
| `family1_full_period` | For arbitrary causal perturbations $P, Q, R$, `family1 P Q R` achieves exact full period $4 ^ w$ on every state at every bit-width $w$. |
| `ternPoly_exact_cycle_partition` | For any list of positive shifts, `ternPoly` partitions all $4 ^ w$ states into exact cycles of length $3 ^ {\mathrm{popcount}(x)}$. |
| `ternTwistY_exact_partition` | The twisted ternary odometer preserves the exact $3 ^ {\mathrm{popcount}(x)}$ cycle partition at every width $w$, even while destroying the $x \mathbin{|} y$ invariant. |
| `hybridTwoCycle_exact_two_cycles` | At every width $w = w' + 1$, `hybridTwoCycle` partitions all $4 ^ w$ states into exactly two cycles of lengths $4 ^ {w'}$ and $3 \cdot 4 ^ {w'}$. |

## Proof Architecture

1. **Non-abelian $S _ 4$ monodromy lifter (`orbit_lift_exact_period`):** lifts exact base periods by the exact cycle length of the fiber monodromy permutation over the base orbit.
2. **$D _ 4$ cocycle decoupling (`D4Elem.is_4cycle_iff`, `full_period_of_D4_parity`):** characterizes 4-cycles in $D _ 4$ by $(\lambda, \beta) = (\mathrm{true}, \mathrm{true})$ and decouples the global parity sums so arbitrary higher-bit perturbations $P, Q, R$ preserve full period $4 ^ w$.
3. **No-shear obstruction (`no_shear_period_bound`, `no_shear_never_full_period`):** proves pure-translation fibers satisfy $T _ w ^ {2 ^ w} = \mathrm{id}$, capping every orbit strictly below $4 ^ w$.
4. **Order-3 ternary odometer & hybrid split (`ternPoly_exact_cycle_partition`, `ternTwistY_exact_partition`, `hybridTwoCycle_exact_two_cycles`):** exploits $S _ 4 \setminus D _ 4$ 3-cycles to prove exact $\binom{w}{k} \times 3 ^ k$ and $(4 ^ {w'}, 3 \cdot 4 ^ {w'})$ global cycle decompositions.

## Prior-Art Context

- **Classical T-function & 2-adic dynamics lineage:** single-cycle multi-word T-functions and the Family I carry-mask trigger $m(x, y) = ((x \mathbin{\&} y) + 1) \oplus (x \mathbin{\&} y)$ trace directly to **Klimov & Shamir** (*New Cryptographic Primitives Based on Multiword T-Functions*, FSE 2004, [pdf](https://www.iacr.org/archive/fse2004/30170001/30170001.pdf); *New Applications of T-Functions in Block Ciphers and Hash Functions*, FSE 2005 / CT-RSA 2005, Parameter-0 construction) and **Anashin & Khrennikov** (*Applied Algebraic Dynamics*, De Gruyter 2009).
- **Contributions claimed here (not independently reviewed; no prior-art search was recorded):** the unified non-abelian $S _ 4 = \mathrm{AGL}(2, \mathbb{F} _ 2)$ fiber-monodromy lifting engine, $D _ 4$ cocycle decoupling to infinite-dimensional functional universality ($\forall P, Q, R$), the universal no-shear obstruction, the $x \mathbin{|} y$-destroying twisted ternary odometer (with $w = 5$ decoy `ternSharpX_breaks_at_w5`), and the hybrid two-cycle family.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
