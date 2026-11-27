# Signed-Digit NAF Carry-Absorption & Odd-Lookahead Parallel Addition (`signed-digit-naf-lookahead`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **82 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a reusable pure-data finite-state certificate compiler for signed-digit carry absorption, instantiated on the 5-state SD-to-NAF recoder (exact defect conservation, global minimality, two exact cubic counting recurrences) and on a constant-depth odd-lookahead carry-free parallel adder, together with a sharp universal impossibility theorem for every finite causal lookback radius and an explicit $3/2$ weight blowup for classical Chow-Robertson addition. Formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

A signed-digit stream is a word in $\{-1, 0, 1\}^{*}$ with value $\mathrm{sdVal}(D) = \sum _ i d _ i 2^i$ and Hamming weight $\mathrm{sdWt}(D) = \sum _ i |d _ i|$. We formalize a finite-state transducer as pure executable data (no `Prop` fields): a state space $\mathrm{Fin}\ m$, an input alphabet $\mathrm{Fin}\ k$, a transition $\delta(q, a) = (\mathrm{out}(q, a), q')$, a flush map, an integer carry-debt potential $\phi$ and a natural weight potential $\psi$. Three finite Boolean certificates over $Q \times \Sigma$ lift to every finite input stream:

- **value conservation** $\mathrm{out}(q, a) + 2 \phi(q') = c \cdot \mathrm{valIn}(a) + \phi(q)$ implies $\mathrm{sdVal}(\mathrm{run}(x)) = c \cdot \mathrm{streamVal}(x)$;
- **exact additive defect conservation** with a pointwise non-negative edge defect $\Delta(q, a) \in \mathbb{N}$, so that $\mathrm{streamWt}(x) = \mathrm{sdWt}(\mathrm{run}(x)) + \sum _ i \Delta(q _ i, x _ i) + \Delta _ {\mathrm{flush}}$;
- **signed-digit range safety** of all output digits.

The headline theorems (all `∀`, over unbounded streams, integers and radii) are:

1. `nat_naf_conservation` (all $n \in \mathbb{N}$): the 5-state recoder turns the binary expansion of $n$ into the non-adjacent form of $n$, and $\mathrm{popcount}(n) = \mathrm{sdWt}(\mathrm{nafRecode}(\mathrm{natToSD}(n))) + \mathrm{nafTotalDefect}(\mathrm{natToSD}(n))$.
2. `nafRecode_minimal_iff` (all $D$): $D$ already has minimal NAF weight iff every transducer step has defect $0$.
3. `naf_global_minimal` (all $A, D$): if $\mathrm{sdVal}(A) = \mathrm{sdVal}(D)$ then $\mathrm{sdWt}(\mathrm{nafRecode}(A)) \le \mathrm{sdWt}(D)$.
4. `countZeroDefectBin_recurrence`: the number $Z(w)$ of $w$-bit words on which NAF recoding saves no weight satisfies $Z(w + 3) + Z(w) = Z(w + 2) + 2 Z(w + 1)$ for all $w$ (characteristic polynomial $\lambda^3 - \lambda^2 - 2\lambda + 1$, dominant root $2 \cos(\pi / 7)$).
5. `countZeroDefectSD_recurrence`: the number $M(w)$ of minimal-weight signed-digit words of length $w$ satisfies $M(w + 3) + M(w) = M(w + 2) + 3 M(w + 1)$ for all $w$.
6. `olAdd_sound_and_subadditive` (all $A, B$): the **odd-lookahead carry-free parallel adder** (carry $c _ i$ from the three digit sums $s _ {i-1}, s _ i, s _ {i+1}$, output $z _ i = (s _ i - 2 c _ i) + c _ {i-1}$, a strictly local $4$-digit window, no ripple) is exact, $\mathrm{sdVal}(A \boxplus B) = \mathrm{sdVal}(A) + \mathrm{sdVal}(B)$, and weight-subadditive, $\mathrm{sdWt}(A \boxplus B) \le \mathrm{sdWt}(A) + \mathrm{sdWt}(B)$.
7. `causal_adder_not_subadditive` (all radii $r$, all valid causal adders): **no** zero-lookahead carry-free parallel adder of any finite lookback radius $r$ can be weight-subadditive; some $k$ with $1 \le k \le r + 1$ has output weight strictly above $k$ on $1^k + 0$.
8. `chowRobertson_periodic_blowup` (all $m$): classical Chow-Robertson addition ($r = 1$) has an unbounded $3/2$ blowup, $\mathrm{causalOutWt}(\mathrm{crCarry}, (1, 1, 0)^m) = 3m$ against $\mathrm{sdWt} = 2m$.

`Theorems.lean` additionally proves the local-window equivalence `olParallelEval_eq_transducer`, the NAF fixed-point law `olAdd_naf_fixed`, arbitrary-depth addition-tree conservation `addTree_conservation`, NAF weight uniqueness `naf_unique_wt`, non-vacuity witnesses (including `Nonempty (CausalAdder 1)` via `chowRobertsonAdder`) and kernel-checked rejection of hostile (mutated) certificates.

## For Non-Mathematicians

Computers can write a number using the digits $-1$, $0$ and $+1$ instead of only $0$ and $1$. That lets them add two numbers with a tiny fixed-size circuit that never waits for a carry to ripple across a million digits. It also lets them store a number with fewer non-zero digits, which makes multiplying by it cheaper. This project proves, for numbers of **any** length, that a small five-state machine always finds the cheapest such representation, and that a simple local rule adds two such numbers without ever making the result heavier. It also proves that the obvious local rule (look only at the digits to the right) can never work, however far back it looks, and that the textbook version really can make results one and a half times heavier. Every statement is checked by Lean's kernel with no unproved assumptions.

## Prior Art

- Reitwiesner (1960) proved existence, uniqueness and minimality of the non-adjacent form (NAF). Avizienis (1961) and Chow-Robertson (1978) introduced constant-depth redundant signed-digit addition using one position of lookback. Heuberger-Prodinger (2001) and Grabner-Heuberger (2006) studied minimal-weight signed-digit expansions through automata and syntactic conditions.
- What is formalized here beyond that baseline: the pure-data certificate compiler with exact additive defect conservation, the two exact cubic counting recurrences, the odd-lookahead adder with weight subadditivity and the universal zero-lookahead impossibility theorem. No prior record of these statements was found by the authors; the search was not recorded. This is a heuristic claim, not a proof of novelty.
- The NAF existence, uniqueness and minimality results are classical background (Reitwiesner); the lookahead phase transition is the part the authors consider new, and it has not been independently reviewed.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
python scripts/explore_and_verify.py
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. The package depends only on Lean 4 core (`Init`).
