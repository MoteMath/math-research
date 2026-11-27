# Shift-Faithful 2-Adic Conjugacy, Ultrametric Gluing & Carry-vs-Carryless Collatz (`carryless-collatz-2adic-gluing`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **87 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): three-layer ShiftFaithful 2-adic conjugacy & O(k) Hensel-inversion engine, exact iff finite-table ultrametric gluing certifiers for 2^r-branch carried/carryless maps, universal binary degree-balance cycle obstruction, and the Carry-vs-Carryless Self-Coding Phase Transition (2^v vs 2 vs 6 vs >= k+1), formalized in pure Lean 4 Init.*

## For Mathematicians

We build a three-layer pure-Init Lean 4 proof engine for 2-adic piecewise-affine and carryless-Collatz dynamics:

1. **Layer A — `ShiftFaithful` 2-Adic Conjugacy & $O(k)$ Hensel Inversion (`Syracuse_conjugacy`, `carried_carryless_3x1_syracuse_conjugate`, `periodic_orbit_classification`):** From two local bitwise axioms — 1-shift causality ($x \equiv y \pmod{2^{k+1}} \implies T(x) \equiv T(y) \pmod{2^k}$) and local bit-flipping ($T(x+2^k) \equiv T(x)+2^{k-1} \pmod{2^k}$) — the parity-vector encoder $Q _ T(k, x)$ and constructive $O(k)$-bit Hensel decoder $R _ T(k, y)$ establish exact 2-adic isometry, $m$-step Haar measure preservation, universal mutual conjugacy $\Phi _ {T _ 1 \to T _ 2} = R _ {T _ 2} \circ Q _ {T _ 1}$ with bit-exact Syracuse $v _ 2$-valuation preservation (in particular conjugating carried $3x+1$ to carryless $\mathrm{clmul}(3,x) \oplus 1$), and exact classification of projective 2-adic $p$-periodic orbits.
2. **Layer B — Exact `iff` Finite-Table Ultrametric Gluing Certifiers (`checkAffTable_iff_shiftFaithful`):** For any $r \ge 1$ and any $2^r$-branch carried or carryless piecewise-affine table $\tau$, a decidable finite Boolean checker inspecting only the $2^r$ residue classes is proved both necessary and sufficient (`↔`) for `ShiftFaithful` across all $k, x \in \mathbb{N}$.
3. **Layer C — Carry-vs-Carryless Self-Coding Phase Transition & Cycle Obstruction (`carryless_selfCoding_exact`, `carried_mod4_eq1_collapse`, `carryless_3x1_unique_nonzero_cycle`):** Counting $k$-bit self-coding residues $F _ T(k) = |\{x < 2^k : Q _ T(k, x) = x\}|$ reveals a sharp carry phase transition: carryless $T _ {p,1}^\oplus$ has exact count $2^{\min(k, v _ 2(p-1))}$, whereas a single binary carry collapses carried $T _ {a,1}^+$ ($a \equiv 1 \pmod 4$) to $F(k) = 2$ for all $k \ge 1$ (and $a \equiv 11 \pmod{16}$ to $F(k) = 6$ for $k \ge 3$), while classical $3x+1$ grows unboundedly ($F(k) \ge k+1$). Finally, an exact carryless trajectory bit-degree identity proves $x = 1$ is the unique non-zero cycle of carryless $3x+1$ in $\mathbb{N}$.

## For Non-Mathematicians

The famous $3x+1$ Collatz map multiplies odd numbers by $3$, adds $1$, and divides by $2$. What happens if you run the exact same rule on a carryless binary multiplier (XOR instead of addition)? In the 2-adic numbers, we prove that carried $3x+1$ and carryless $3x+1$ are exact mirror images of each other — with a fast $O(k)$-bit decoder translating every parity trajectory back and forth — and we give a finite table checker that certifies this mirror property for arbitrary $2^r$-branch Collatz-like rules in one step. Yet turning carries on or off triggers a dramatic phase transition in "self-coding" numbers (numbers equal to their own parity trajectory): carryless maps freeze at $2^{v _ 2(p-1)}$, carried $a \equiv 1 \pmod 4$ maps collapse all the way to just $2$, while classical $3x+1$ produces infinitely many. Meanwhile, in ordinary integers, carryless $3x+1$ has $x = 1$ as its unique non-zero cycle.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of the `ShiftFaithful` 2-adic conjugacy and $O(k)$ Hensel-inversion engine, exact `iff` $2^r$-branch ultrametric gluing certifiers, the Carry-vs-Carryless Self-Coding Phase Transition, and carryless Collatz cycle uniqueness.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `Syracuse_conjugacy` | For any two even-halving `ShiftFaithful` maps $T _ 1, T _ 2$, $\Phi _ {T _ 1 \to T _ 2} = R _ {T _ 2} \circ Q _ {T _ 1}$ conjugates $T _ 1$ to $T _ 2$ with bit-exact Syracuse $v _ 2$-valuation preservation. |
| `checkAffTable_iff_shiftFaithful` | For all $r \ge 1$ and any $2^r$-branch carried table $\tau$, the finite Boolean checker `checkAffTable r tab = true` holds if and only if `evalAffTable r tab` is `ShiftFaithful` on all of $\mathbb{N}$. |
| `carried_carryless_3x1_syracuse_conjugate` | Carried Collatz ($3x+1$) and carryless Collatz ($\mathrm{clmul}(3,x) \oplus 1$) are constructively 2-adically conjugate with exact Syracuse $v _ 2$-valuation preservation. |
| `carryless_selfCoding_exact` | For every odd $p > 1$ and $v = v _ 2(p-1)$, carryless $T _ {p,1}^\oplus$ has exact self-coding count $2^{\min(k, v)}$ for all $k \in \mathbb{N}$ and unique 2-adic fixed point $0$. |
| `carried_mod4_eq1_collapse` | Single-carry collapse: for every $a \equiv 1 \pmod 4$ and all $k \ge 1$, carried $T _ {a,1}^+$ has exactly $2$ self-coding $k$-bit residues and unique 2-adic fixed point $0$. |
| `carryless_3x1_unique_nonzero_cycle` | For every $L \ge 1$ and $x > 0$, if $(T _ {3,1}^\oplus)^L(x) = x$ in $\mathbb{N}$, then $x = 1$. |
| `periodic_orbit_classification` | For any `ShiftFaithful` map $T$ and period $p \ge 1$, the Hensel sequence `perOrbit T p w` gives an exact constructive bijection between $[0, 2^p)$ and projective 2-adic $p$-periodic orbits of $T$. |

## Proof Architecture

1. **Constructive $O(k)$ Hensel Inversion (`ShiftFaithful`):** Two bitwise axioms yield the iterated flip invariant $T^j(x+2^k) \equiv T^j(x)+2^{k-j} \pmod{2^{k-j+1}}$, giving a bit-by-bit decoder $R _ T(k, y)$ with zero $2^k$ search and proving 2-adic isometry, Haar measure preservation, Syracuse conjugacy, and periodic-orbit classification.

2. **Exact `iff` Finite-Table Gluing (`checkAffTable_iff_shiftFaithful`, `checkClTable_iff_shiftFaithful`):** Proves that checking odd slopes plus cross-branch causality and bit-flipping on the $2^r$ residue classes is both necessary and sufficient for global `ShiftFaithful`ness.

3. **Finite-Certificate Self-Coding Collapse (`selfCoding_collapse_of_no_odd`):** Proves $F _ T(k+1) = F _ T(k) + O _ T(k+1)$ and shows that a single finite zero witness $O _ T(k _ 0) = 0$ lifts to an infinite plateau $F _ T(k) = F _ T(k _ 0 - 1)$ for all $k \ge k _ 0 - 1$, establishing the carry/carryless phase transition ($2^v$ vs $2$ vs $6$ vs $\ge k+1$).

4. **Carryless Degree Balance (`carryless_3x1_unique_nonzero_cycle`):** Exact bit-degree accounting $\mathrm{bitDeg}((T _ {p,q}^\oplus)^L(x)) + L = \mathrm{bitDeg}(x) + d \cdot \mathrm{popcount}(Q(L, x))$ obstructs all non-trivial cycles for $T _ {3,1}^\oplus$.

## Prior-Art Context

- **Classical 2-adic Collatz & polynomial Collatz lineage:** Layer A sits in the Terras (1976), Lagarias (1985), Bernstein (1994), and Anashin–Khrennikov (2009) 2-adic conjugacy lineage, while Hicks–Mullen–Yucas–Zavislak (2008) prove full termination of polynomial $x+1$ Collatz over $\mathbb{F} _ 2[x]$ (our `carryless_3x1_unique_nonzero_cycle` gives a self-contained pure-Init proof of cycle uniqueness via bit-degree balance, distinct from full termination).
- **Contribution claimed here (not independently reviewed; no prior-art search was recorded):** the exact `iff` $2^r$-branch ultrametric gluing certifiers (`checkAffTable_iff_shiftFaithful`, `checkClTable_iff_shiftFaithful`), the universal $(p, q)$ binary degree-balance law, and the Carry-vs-Carryless Self-Coding Phase Transition ($2^v$ vs $2$ vs $6$ vs $\ge k+1$).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build logs and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. `scripts/explore_and_verify.py` replays the finite certificates and sharpness counterexamples in exact integer arithmetic (zero floats).
