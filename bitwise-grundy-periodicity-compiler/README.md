# Bitwise Grundy Periodicity Compiler: Borrow-Guarded Subtraction Games (`bitwise-grundy-periodicity-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **7 / 10** | **10 / 10** | **80 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a dyadic borrow-wall theory for subtraction games whose move legality depends on the binary borrow/carry structure of $n - s$, with a kernel-checked certificate compiler that lifts finite tables to exact $\forall n$ periodicity and winning-bitmask laws, the full multi-heap Sprague-Grundy XOR theorem, and a proved aperiodic borrow-parity game, all in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Fix a finite list of rules $(s, g)$: a move $n \to n - s$ is legal when $0 < s \le n$ and a guard $g$ on the binary borrow/carry structure of the subtraction $n - s$ holds (borrow-free, at most $B$ borrows, Hamming weight not increasing by more than $\Delta$, mask tests, and boolean combinations). Let $g _ G$ be the Sprague-Grundy function. The formalization proves three regimes:

1. **Borrow calculus.** With $\mathrm{borrowCount}(n, s) = \mathrm{popcount}(n \oplus (n - s) \oplus s)$, the Kummer-type identity $\mathrm{popcount}(n - s) + \mathrm{popcount}(s) = \mathrm{popcount}(n) + \mathrm{borrowCount}(n, s)$ holds for all $s \le n$. If $s < 2^k$ and $s \le n$, then $\mathrm{borrowCount}(n + m \cdot 2^{k + B}, s) \le B$ if and only if $\mathrm{borrowCount}(n, s) \le B$, so every borrow-budget guard is exactly $2^{k+B}$-periodic in $n$.
2. **Regime I (dyadic borrow wall).** If every guard of $G$ is a wall guard and $L = \mathrm{gameShiftBits}(G)$, then no legal move crosses a multiple of $2^L$ and $g _ G(n + 2^L) = g _ G(n)$ for all $n \in \mathbb{N}$: the game is purely periodic from $n = 0$.
3. **Regime II (reflection compiler).** A pure-data certificate `PeriodWinCert` (preperiod, period, minimal period, table, packed winning bitmasks, winning-move oracles) is checked by the executable `checkCert G c : Bool`. A single `decide` of `checkCert G c = true` yields, for all $n \in \mathbb{N}$, $g _ G(n) = \mathrm{evalPeriodic}(c, n)$, the minimal period, the winning bitmask, a constructive winning-move oracle and the multi-heap law. The proved **multi-heap Sprague-Grundy theorem** states $\mathrm{IsWinningMulti}(G, hs) \iff \mathrm{nimSum}(hs.\mathrm{map}(g _ G)) \ne 0$ for every game and every list of heaps. Six certified games exercise it, among them wall-breaching games with preperiod $5$ and period $24$, and the game $\{2\,(\text{borrow-free}), 3, 7\}$ whose Grundy sequence has the odd period $5$ for all $n \ge 15$ even though one move is dyadically gated.
4. **Regime III (sharp aperiodic boundary).** Replacing the bounded borrow count by its parity gives the game $\{1 \text{ if } \mathrm{borrowCount}(n, 1) \text{ is even},\; 2\}$. Its Grundy values satisfy $g(4k) = 2$ or $1$ according to the parity of $v _ 2(k)$ (for $k \ge 3$), $g(4k + 1) = g(4k + 2) = 0$, $g(4k + 3) = 1$, and for every $n _ 0$ and every $p > 0$ there is $n \ge n _ 0$ with $g(n + p) \ne g(n)$. The 1-heap winning set is nevertheless periodic of period $4$ for $n \ge 12$, while the 2-heap sum $(4k, 4)$ is losing iff $v _ 2(k)$ is even, hence aperiodic.

Sharpness and non-vacuity are kernel-checked as well: the modulus $2^{k+B}$ is minimal (for $s = 1$, $B = 1$, shift $2$ fails at $n = 2$), the preperiods $15$ and $5$ are minimal, concrete winning and losing heaps are exhibited, and eight corrupted certificates are rejected by `decide`.

## For Non-Mathematicians

Imagine a pile of $n$ stones and two players who alternately remove $s$ stones, but a removal is only allowed if the binary digits of the subtraction behave in a certain way, for example "the subtraction must not need any borrowing" or "the number of 1-bits must not go up". Who wins with perfect play? For ordinary games with fixed allowed moves, the answer eventually repeats with a fixed period. Here the rules look at the binary carries, so it is not obvious whether anything repeats.

We prove that if every rule is a "borrow wall" rule, the pattern repeats from the very beginning with a period that is a power of two, for all pile sizes at once. For other rules we built a small checker: it examines a short finite table, and when it says yes, Lean's kernel concludes a statement about every pile size, and about any collection of piles played together. Some games repeat with odd periods such as $5$. And one game, whose rule asks about the *parity* of the borrow count, provably never repeats at all, even though the question "does the first player win from a single pile?" still has a period-$4$ answer.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of borrow-guarded subtraction games, the dyadic borrow-wall theorem, a kernel-checked periodicity/winning-strategy compiler and the aperiodic borrow-parity boundary.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `kummer_borrow_popcount` | For $s \le n$: $\mathrm{popcount}(n - s) + \mathrm{popcount}(s) = \mathrm{popcount}(n) + \mathrm{borrowCount}(n, s)$. |
| `borrowCount_le_shift_inv` | For $s < 2^k$ and $s \le n$: $\mathrm{borrowCount}(n + m \cdot 2^{k+B}, s) \le B \iff \mathrm{borrowCount}(n, s) \le B$. |
| `isWinningMulti_iff_nimSum_ne_zero` | For every game $G$ and every list of heaps $hs$: $\mathrm{IsWinningMulti}(G, hs) \iff \mathrm{nimSum}(hs.\mathrm{map}(g _ G)) \ne 0$. |
| `dyadic_borrow_wall_periodicity` | If all guards of $G$ are wall guards, then $g _ G(n + 2^{\mathrm{gameShiftBits}(G)}) = g _ G(n)$ for all $n$. |
| `checkCert_sound_grundy` | If `checkCert G c = true`, then $g _ G(n) = \mathrm{evalPeriodic}(c, n)$ for all $n$. |
| `G_coprime_p5_period_5` | For the game $\{2\,(\text{borrow-free}), 3, 7\}$ and all $n \ge 15$: $g(n + 5) = g(n)$. |
| `grundyParity_not_eventually_periodic` | For all $n _ 0$ and $p > 0$ there is $n \ge n _ 0$ with $g _ {\mathrm{par}}(n + p) \ne g _ {\mathrm{par}}(n)$. |
| `grundyParity_oneHeap_periodic_vs_twoHeap_aperiodic` | For $n \ge 12$, $g _ {\mathrm{par}}(n) \ne 0 \iff n \bmod 4 \in \{0, 3\}$; for $k \ge 3$, $g _ {\mathrm{par}}(4k) \oplus g _ {\mathrm{par}}(4) = 0 \iff v _ 2(k)$ is even. |

## Proof Architecture

1. **Borrow calculus.** Popcount, bit length and 2-adic valuation are defined by fuel-bounded structural recursion, so that `decide` reduces them in the kernel; fuel-independence lemmas connect them to the usual recurrences. The Kummer identity follows from the carry identity for addition applied to $(n - s) + s = n$. Splitting $n = q \cdot 2^k + r$ at $k = \mathrm{bitLen}(s)$ gives two exact regimes for the borrow chain (no cross-boundary borrow, or a ripple of length $v _ 2(q) + 1$), which yields the localization theorem and the impossibility of crossing a $2^L$ wall with at most $B$ borrows.
2. **Game semantics.** The guard language `BitGuard` is deeply embedded and evaluated by `evalGuard`. The Grundy function is defined directly by well-founded recursion as the `mex` of the Grundy values of legal successors, and `IsWinning` and `IsWinningMulti` are defined directly from the moves, with no reference to the certificate machinery. The 1-heap bridge `IsWinning ↔ grundy ≠ 0` and the multi-heap XOR theorem are proved by strong induction, using a most-significant-bit argument for the nim-sum move.
3. **Dyadic borrow wall.** Every guard has an exact shift exponent `guardShiftBits`; for wall guards the guard is false whenever a move would cross a multiple of $2^L$, so the legal-move lists at $n$ and $n + 2^L$ coincide up to the shift and the Grundy values agree by strong induction.
4. **Reflection compiler.** `checkCert` checks positivity and divisibility conditions, the Grundy recurrence and seam continuity on $[0, n _ 0 + p + \max s)$, minimal-period compression, the packed winning bitmasks and the winning-move oracles. Soundness is proved by strong induction using the shift invariance of the guards (`evalGuard_shift_inv`); the six showcase games and eight mutated (rejected) certificates are discharged by `decide`.
5. **Aperiodic boundary.** For the borrow-parity game, $\mathrm{borrowCount}(n, 1) = \mathrm{ctz}(n) + 1$ turns the guard into a ruler-function parity test. An exact closed form of the Grundy values for $n \ge 12$ is proved by induction on $k$ with the ruler function $v _ 2$, and the aperiodicity for every candidate period follows from this closed form by exhibiting, for each preperiod and period, an index at which the two sides differ.

## Prior-Art Context

- **Classical subtraction games:** Golomb (1966), Guy and Smith (1956) and Berlekamp, Conway and Guy (*Winning Ways*, 1982) treat state-independent move sets, where periodicity follows from a pigeonhole argument on a window of length $\max S$. Fraenkel and collaborators study numeration-system and aperiodic subtraction games (Wythoff, Beatty and Zeckendorf families) by combinatorial numeration, not by hardware carry/borrow propagation.
- **Referee note:** the internal referee audit of this mechanism (S-Tier novelty audit, 4.5/5) distinguishes it from the classical constant-subtraction theory and from the neighbouring carry-structure packages of this repository (`binary-lyness-periods`, `bitrev-increment-cycles`, `clmul-lift-determinants`, `zero-carry-spanning-trees`, `carry-determinants`): the borrow-count localization, the dyadic borrow-wall theorem, the wall-breaching phase transition $B = 0 \to 1 \to \infty$ on the move set $\{1, 3, 4\}$, the collapse to an odd period despite a dyadic gate, and the periodic-1-heap versus aperiodic-2-heap split of the borrow-parity game appear to be new. A literature search found no prior record of these statements; this is a heuristic claim, not an exhaustive survey.
- **Sprague-Grundy theory:** the multi-heap theorem proved here is the classical Sprague-Grundy XOR theorem (Sprague 1935, Grundy 1939), formalized for the borrow-guarded games defined here and proved from the game definitions.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

The script [`scripts/explore_and_verify.py`](scripts/explore_and_verify.py) is an independent exact-integer Python replay of the six showcase games, the borrow-wall theorem on five wall-guarded games, the parity-game closed form and the certificate mutations. See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
