# Self-Delimiting Binary Prefix-Code Kirchhoff-Bellman Transducer Engine (`self-delimiting-prefix-transducers`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): unified exact-integer Kirchhoff-Bellman potential engine over leaky prefix-code automata and compositional order-preserving Elias-lift engine, proving exact Kraft and signed-character conservation, the order-type $\omega$ obstruction, $k$-bonacci zero Hamming bias and a Jacobsthal popcount-vs-length parity identity (an index shift between two defined potentials), symmetry of the `runAut` bias polynomials, and iterated Elias-lift order preservation, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

For any finite-state prefix-code automaton `PrefixAut S`, we prove strict prefix-freeness (`accepts_prefix_free`) and build an exact-integer **Kirchhoff-Bellman Potential Engine** (`layer0_conservation`, `layer1_conservation`, `layer0_contraction`, `layer1_contraction`): local finite-state Kirchhoff equations over $\mathbb{Z}$ lift across all bit-lengths $N \in \mathbb{N}$ to exact conservation of Kraft sums, signed characters, and bit-cost potentials without real numbers or floating-point arithmetic.

Applying the engine discharges four infinite families: (1) the **Order-Type $\omega$ Obstruction** (`order_type_omega_obstruction`), proving that any prefix automaton with a `0`-cycle reaching an accepting `1`-branch contains an infinite lexicographically descending chain and admits no order-preserving enumeration by $\mathbb{N}$; (2) **$k$-bonacci prefix automata** (`fibAut k`), proving exact Kraft conservation, exact zero Hamming bias (`fibAut_zero_bias`), and a **Jacobsthal popcount-vs-length parity identity** (`fibAut_parity_duality_embedding`, an index-shift identity between two potentials defined in `Defs.lean`); (3) **asymmetric-Kraft / symmetric-bias** run-length automata (`runAut_bias_symmetric`, symmetry of two explicit polynomials); and (4) a compositional **order-preserving Elias-lift tower** (`eliasLift_orderPreserving`; the $+1/2$ popcount-parity collapse across levels $r \ge 1$ is in `Theorems.lean`).

## For Non-Mathematicians

Variable-length binary codes let computers store numbers of any size back-to-back without commas. Using exact integer accounting equations on finite-state machines, we prove that $k$-bonacci codes always balance 0s and 1s with zero bias, uncover a hidden symmetry swapping the parity of a codeword's length with the parity of its 1-bits, prove exactly when a code can never be sorted in alphabetical order, and show that stacked Elias codes preserve numerical order at every level.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `SelfDelimitingPrefixTransducers/Theorems.lean`, definitions in `SelfDelimitingPrefixTransducers/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `accepts_prefix_free` | Every language accepted by a finite-state `PrefixAut` is strictly prefix-free. |
| `layer0_conservation` | Any integer Kirchhoff-0 potential $\kappa$ certifies exact conservation $D \cdot \mathrm{charSum} + \mathrm{activePot} = B ^ N \cdot \kappa(q)$ at every length $N$. |
| `order_type_omega_obstruction` | Any prefix automaton with a `0`-cycle reaching an accepting `1`-branch has an infinite lexicographically descending chain and no order-preserving enumeration by $\mathbb{N}$. |
| `fibAut_kraft_conservation` | For every $k \ge 1$ and length $N$, the $k$-bonacci prefix automaton satisfies exact dyadic Kraft conservation. |
| `fibAut_zero_bias` | For every $k \ge 1$ and length $N$, the $k$-bonacci prefix automaton has exact zero signed Hamming bias. |
| `fibAut_parity_duality_embedding` | The popcount-parity potential of `fibAut (k + 1)` embeds the length-parity potential of `fibAut k` with negated root. This is an index-shift identity between two potentials (`fibPopKappa`, `fibLenPKappa`) written down in `Defs.lean` (Jacobsthal numbers with a sign), true by unfolding them. |
| `runAut_bias_symmetric` | For all $a, b \in \mathbb{N}$, the signed Hamming bias numerator and denominator of `runAut a b` are strictly symmetric in $(a, b)$ despite asymmetric Kraft measures. Both are explicit polynomial expressions defined in `Defs.lean`; the statement is symmetry of those polynomials. |
| `eliasLift_orderPreserving` | The compositional Elias lift preserves strict lexicographic order-preservation on every order-preserving prefix code. (The $+1/2$ popcount-parity collapse across tower levels mentioned above is proved in `Theorems.lean`, not in `Challenge.lean`.) |

## Proof Architecture

1. **Prefix-automaton & Kirchhoff-Bellman engine (`accepts_prefix_free`, `layer0_conservation`, `layer1_conservation`):** lifts exact integer node potentials to all lengths $N$ for both Kraft weights and signed bit-costs.
2. **Order-type $\omega$ obstruction (`order_type_omega_obstruction`):** constructs an explicit descending chain from any `0`-cycle reaching a `1`-accept branch.
3. **$k$-bonacci & run-length families (`fibAut_*`, `runAut_*`):** proves Kraft conservation, zero Hamming bias, Jacobsthal parity reciprocal duality, and asymmetric-Kraft / symmetric-bias laws uniformly in $k, a, b$.
4. **Compositional Elias-lift tower (`eliasLift_orderPreserving`, `eliasTower`):** proves order-preservation and $+1/2$ popcount-parity collapse across all tower heights $r \ge 1$.

## Prior-Art Context

- **Classical prefix-coding & probability lineage:** Kraft (1949) and McMillan (1956) inequalities, Elias (1975) universal codes, Fraenkel & Klein (1996) Fibonacci codes, Guibas & Odlyzko (1981) string overlaps, Wald's identity and Feller (1968) (for zero-bias stopping-time intuition), and Levenshtein (1968) / Fenwick (2003) for Elias-$\delta$ / universal code length divergence.
- **Claimed contribution (not independently reviewed):** the unified exact-integer Kirchhoff-Bellman Potential Engine over leaky automata and signed characters, the $k$-bonacci Jacobsthal popcount-vs-length parity identity, the symmetry of the Hamming-bias polynomials of `runAut a b`, the order-type $\omega$ obstruction, and the compositional `eliasTower` $+1/2$ popcount-parity collapse. No prior record was found by the authors; the search was not recorded. The parity identity and the symmetry statement are short consequences of the definitions (see the table).

## Scope of the formal statement

The automata, potentials and bias polynomials are the definitions in `Defs.lean`. The Kirchhoff-Bellman conservation laws are universal over all finite automata and lengths; the $k$-bonacci parity identity and the `runAut` symmetry are identities between explicit formulas written in `Defs.lean`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
