# Dual-Rail Redundant Binary Addition: Exact Carry Horizon and All-Width Certificates (`dualrail-tropical-carry-horizon`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): finite potential and relational certificates lift to exact all-width identities for dual-rail (Avizienis-style) redundant binary addition, with a tropical rank-1 horizon calculus, an exactly tight horizon bound and a verified expression compiler, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Dual-rail digits are pairs of bits $(p, n)$ with value $p - n$. For a finite transducer $T$ over streams, a finite **potential certificate** $\varphi$ yields the exact identity $\mathrm{prefixVal} _ w (\text{out}) + 2 ^ w \varphi(\text{state} _ w) = \mathrm{prefixSum} _ w (\text{target}) + \varphi(q)$ at every width $w$, and a finite **relational invariant** between two transducers yields equality of prefix values modulo $2 ^ w$ at every width. Applied to the two-stage radix-2 dual-rail adder this gives exact integer semantics (`avizAdd_exact_int`) and associativity modulo $2 ^ w$ on arbitrary streams (`avizAdd_assoc_mod`), even though the adder is neither raw-commutative nor raw-associative at the bit level.

Carry-boundedness is certified by a finite pair-Lyapunov rank certificate and $2 \times 2$ tropical max-plus matrices whose product is rank one; every output digit depends only on a window of $2$ preceding input positions (`avizAdd_horizon2`), and for chains of adders the exact lag is attained by an explicit one-position perturbation (`exact_horizon_achieved`). Ripple carry has no horizon certificate for any $H$ (`no_horizon_cert_for_ripple`). A verified compiler flattens any dual-rail expression tree to a right chain preserving the value modulo $2 ^ w$ for all $w$ (`compileRight_equiv_all_widths`).

## For Non-Mathematicians

In ordinary addition a carry can ripple across a whole number: adding $1$ to $999999$ changes every digit. A "redundant" adder allows digits $-1, 0, +1$ so that each output digit only looks at a few neighbouring input digits, which is why such adders are fast in hardware. We prove, for numbers of any length at once, that the redundant adder computes the correct sum, that it is associative modulo every power of two, that each digit only depends on a window of three input positions, that this window size cannot be improved for chains, and that ordinary ripple carry has no window at all.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `DualrailTropicalCarryHorizon/Theorems.lean`, definitions in `DualrailTropicalCarryHorizon/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `potential_lift_all_widths` | A valid finite potential certificate $\varphi$ for a dual-rail transducer gives, at every width $w$, $\mathrm{prefixVal} _ w (\text{out}) + 2 ^ w \varphi(\text{state} _ w) = \mathrm{prefixSum} _ w (\text{target}) + \varphi(q)$. |
| `relational_bisim_mod_eq` | A valid finite relational invariant between two transducers, vanishing on the initial pair, forces equal prefix values modulo $2 ^ w$ at every width $w$. |
| `avizAdd_exact_int` | For every width $w$ and all streams $x, y$: $\mathrm{prefixVal} _ w (x \boxplus y) + 2 ^ w \varphi(\text{state} _ w) = \mathrm{prefixVal} _ w (x) + \mathrm{prefixVal} _ w (y)$ for the dual-rail adder $\boxplus$. |
| `avizAdd_assoc_mod` | For every width $w$ and all streams $x, y, z$, $(x \boxplus y) \boxplus z$ and $x \boxplus (y \boxplus z)$ have equal prefix values modulo $2 ^ w$. |
| `avizAdd_horizon2` | If two pairs of input streams agree on positions $i - 2, i - 1, i$ then the adder outputs agree at position $i$. |
| `compileRight_equiv_all_widths` | For every width $w$, environment and dual-rail expression $e$, the right-chain compilation of $e$ has the same prefix value modulo $2 ^ w$ as the direct evaluation. |
| `exact_horizon_achieved` | For every outer port word and inner port, two streams differing only at position $0$ give chain outputs that differ at the computed maximal lag, so the horizon bound is attained. |
| `no_horizon_cert_for_ripple` | For every $H$ and rank table $R$, the ripple-carry transducer admits no valid horizon certificate. |

## Proof Architecture

1. **Generic lifters (`DRTransducer`, `ValidPotential`, `ValidRelInvariant`):** finite certificates checked locally lift to all widths by induction on $w$, with direct `BitVec w` semantics.
2. **Carry boundedness (`ValidHorizonCert`, `TropicalMat2`, `RailBounded`):** pair-Lyapunov DAG ranks bound the carry lag; the rail-lag matrices form a non-commutative tropical rank-$1$ semigroup, giving closed forms for chains of adders (`chainMat_closed_form`).
3. **Tightness (`tailPulse_exact_lower_bound`, `exact_horizon_achieved`):** an explicit tail pulse realizes the exact lag $d + 1 + \#\{i < d - 1 : w _ i = \mathrm{p1}\}$ for every port word.
4. **Compiler (`compileRight_equiv_all_widths`, `horizon_halving_exact_separation`):** expression trees compile to right chains, halving the horizon from $2 d$ to $d + 1$ with an exact separation.
5. **Obstructions (`radix2_horizon1_impossible`, `radix3_horizon1_witness`, `no_horizon_cert_for_ripple`):** an encoding-independent radix-$r$ horizon-$1$ obstruction with a constructive radix-$3$ witness, and the absence of any horizon for ripple carry.

## Prior-Art Context

- **Classical background:** Avizienis (1961) signed-digit carry-free addition, Chow-Robertson (1978) and Frougny (1992) on redundant binary automata, and Parhami's redundant number system surveys; max-plus/tropical matrix semigroups (Baccelli et al.).
- **Referee audit (referee-1, referee-6; recorded in `REGISTRY.md` and `TOP_MECHANISMS.md`):** the reusable certificate lifters, the tropical rank-$1$ horizon calculus with exact `TailPulse` tightness, the horizon-halving equivalence compiler and the encoding-independent radix-$r$ horizon-$1$ obstruction are new; zero overlap with the other packages of this repository.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
