# Popcount Clock and Borrow-Acceleration Engine (`popcount-clock-borrow-accel`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **7 / 10** | **6 / 10** | **10 / 10** | **76 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): exact unit-clock and inversion-clock laws, Mersenne hitting times, a synchronous-collision criterion, borrow acceleration and unique modular attractor cycles for popcount-driven bitwise dynamics, which are anti-causal and so outside T-function and Hensel techniques, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Let $s _ 2(x)$ be the popcount and consider the anti-causal flow $T _ \oplus(x) = x \oplus 2^{s _ 2(x)}$ on $\mathbb{N}$, whose popcount feedback comes from the high bits. With the quadratic bit-moment $V(x) = 2 \sum _ {i \ge 0} i\, x _ i - s _ 2(x)^2$ and the inversion energy $\Phi(x) = \sum _ {i \ge 0} i\, x _ i - \binom{s _ 2(x)}{2}$ we prove, for **all** $x \in \mathbb{N}$:

1. **Unit clock:** $V(T _ \oplus^t(x)) = V(x) - t$ for all $t$; in particular $T _ \oplus$ has no cycles. It hits the Mersenne word $2^m - 1$ in exactly $V(x) + m$ steps whenever $x < 2^m$, and two numbers collide synchronously under $T _ \oplus$ if and only if $V(x) = V(y)$.
2. **Borrow acceleration:** hardware subtraction $T _ -(x) = x - 2^{s _ 2(x)}$ equals the $(1 + \mathrm{ctz}(x \gg s _ 2(x)))$-fold iterate of $T _ \oplus$ whenever $\Phi(x) > 0$, and decreases $\Phi$ by exactly $1$; hence $T _ -$ reaches a Mersenne word in exactly $\Phi(x)$ steps, independent of the length of the borrow chain. The shifted variant $x \mapsto x - 2^{s _ 2(x) - 1}$ reaches $0$ in exactly $\Phi(x) + s _ 2(x)$ steps.
3. **Modular attractors:** the wrapped $w$-bit flows have a unique global attractor cycle: length $2w$ at $2^w - 1$ for the carry-free flow, length $w + 1$ for the borrow-coupled flow, for every $w \ge 1$; and the complement map conjugates the borrow flow to the carry-synchronized addition dual (exact complement carry-borrow conjugacy).

The method is a reusable certificate compiler (`ClockCert`): pointwise finite-difference equations on the popcount potential lift to the global bit-moment clock at arbitrary width.

## For Non-Mathematicians

Take any whole number, count how many 1s appear in its binary form, and flip the bit at that position. Repeat. The count feeds back from the whole number to a single far-away bit, which is why the usual tools for bit-level generators do not apply. This package proves the process is a perfect clock: a single formula ("moment") of the number drops by exactly one at every step, so the process never repeats a value and eventually becomes a string of all 1s (a number like 7, 15, 31, ...) after a step count you can read off the starting number in advance. Replacing flipping by genuine binary subtraction, with its long chains of borrows, changes nothing: the whole borrow chain collapses into one tick of the same clock. On fixed-width words the process has exactly one cycle that every starting value runs into, of length 2w, or w + 1 for the subtraction version, for every width w.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of exact clock, hitting-time and attractor laws for the anti-causal popcount-driven bitwise flows $x \oplus 2^{s _ 2(x)}$ and $x - 2^{s _ 2(x)}$ over unbounded $\mathbb{N}$.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `T_xor_unit_clock` | For all $t, x$, the quadratic bit-moment decreases by exactly one per step: $V(T _ \oplus^t(x)) = V(x) - t$. |
| `T_xor_hits_mersenne_exact` | If $x < 2^m$ and $V(x) + m = N$, then $T _ \oplus^N(x) = 2^m - 1$. |
| `T_xor_sync_collision_iff` | Two numbers $x, y$ collide synchronously under $T _ \oplus$ for some $t$ if and only if $V(x) = V(y)$. |
| `T_sub_borrow_acceleration` | If $\Phi(x) > 0$ then $2^{s _ 2(x)} \le x$, the borrow step $T _ -(x)$ equals $T _ \oplus^{1 + \mathrm{ctz}(x \gg s _ 2(x))}(x)$, and $\Phi(T _ -(x)) = \Phi(x) - 1$. |
| `T_sub_hits_mersenne_exact` | For every $x$, after exactly $\Phi(x)$ borrow steps the orbit is a Mersenne word $2^k - 1$. |
| `F_xor_wrap_unique_2w_cycle` | For every $w \ge 1$, the wrapped carry-free flow sends every $x < 2^w$ to $2^w - 1$, which lies on a cycle of exact length $2w$. |
| `F_sub_wrap_unique_cycle` | For every $w \ge 1$, the wrapped borrow-coupled flow sends every $x < 2^w$ to $2^w - 1$, which lies on a cycle of exact length $w + 1$. |
| `complement_carry_borrow_conjugacy` | For $w \ge 1$ and $x < 2^w$, complementing the borrow-coupled flow on the complement of $x$ gives exactly the carry-synchronized addition dual flow at $x$. |

## Proof Architecture

1. **`ClockCert` compiler (`ClockCert.pot_step`, `ClockCert.unit_clock_iter`, `ClockCert.no_cycles`):** local finite-difference equations on a popcount potential $g$ and weight map $\mu$ imply the global identity $V(T _ h(x)) = V(x) - \delta$ at any bit-width.
2. **XOR flow (`T_xor_unit_clock`, `T_xor_hits_mersenne_exact`, `T_xor_sync_collision_iff`):** instantiate the compiler with $h = \mathrm{id}$; Mersenne hitting follows because $V(x) + m$ counts the steps to fill the word.
3. **Borrow acceleration (`T_sub_borrow_acceleration`):** the borrow chain flips consecutive zero bits to one exactly as repeated XOR steps do; the telescope reduces by induction on the trailing-zero gap to the identity $(x + 2^p) - 2^{p+1} = x - 2^p$.
4. **Modular flows (`F_xor_wrap_unique_2w_cycle`, `F_sub_wrap_unique_cycle`, `complement_carry_borrow_conjugacy`):** a permuted-bit potential gives an exact hitting time of $2^w - 1$ and an exact cycle length there; complementation intertwines the borrow and carry flows.

## Prior-Art Context

- **Closest literature:** the binary inversion statistic and Young-diagram area behind $\Phi$ (the exponent of $q$-binomial coefficients), the Thue-Morse and Hamming-weight literature, and self-referential bit dynamics such as Collatz-like popcount maps. No prior record is known to the packager of the popcount-addressed flows $x \oplus 2^{s _ 2(x)}$ and $x - 2^{s _ 2(x)}$ with an exact unit clock, an exact Mersenne hitting time, the synchronous-collision criterion or the borrow-acceleration identity.
- **Review status:** not independently reviewed. No novelty audit of this mechanism has been completed; the claim above that no prior record is known is the packager's reading and the search behind it was not recorded.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib). See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts, [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest, and `scripts/explore_and_verify.py` for the exact-integer exploration and verification script (zero floating point).
