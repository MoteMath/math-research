# Kummer Carry-Valuation Automata Engine (`kummer-carry-valuation-automata`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): Legendre and Kummer built from scratch, a reusable finite-state carry-valuation automaton engine whose `decide`-checked certificates lift to all $n$ (including exact-equality pumping families), shifted-bitwise Kummer collapse laws, Gray-code binomial sandwiches and sharp non-integer slopes for $v _ 2 \binom{kn}{n}$, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Write $s _ 2$ for the binary popcount and $v _ 2$ for the $2$-adic valuation. Legendre's formula $v _ 2(n!) + s _ 2(n) = n$ and Kummer's theorem $v _ 2 \binom{a+b}{a} + s _ 2(a + b) = s _ 2(a) + s _ 2(b)$ (and its trinomial form) are proved from scratch. Any integer combination of such valuations at bitwise-shifted or Gray-coded arguments is then read LSB-first by a finite carry-valuation automaton $\mathcal{A} = (S, \delta, w, \tau)$, and four meta-theorems turn finite `decide`-checked certificates into statements for all $n$:

1. **Coboundary lifting (`CVA.coboundary_sound`):** a finite potential with $w(q, b) + \phi(\delta(q, b)) = \phi(q)$ proves $\mathrm{eval}(\mathcal{A}, q, n) = \phi(q)$ for every $n$.
2. **Tropical bounds (`CVA.lower_sound`, `CVA.upper_sound`):** sub- and super-potentials prove two-sided bounds for every $n$ (and for every $n \ge 1$ with offset, via doubling invariance).
3. **Zero-slack pumping (`CVA.pumping_exact`):** a finite lasso with zero slack yields an infinite family $x _ m = \mathrm{fromBits}(u \cdot v^m \cdot t)$ with exact equality, certifying that both slope and offset are sharp.

Consequences for **all** $n \in \mathbb{N}$: $2 v _ 2 \binom{n + (n \oplus 2n)}{n} = 2 s _ 2(n) + s _ 2(n \oplus 2n)$ and $v _ 2 \binom{n + (n \mathbin{|} 2n)}{n} = s _ 2(n \mathbin{|} 2n)$ (similarly for AND and for the trinomial $(n, 2n, n \oplus 2n)$); for the Gray code $G(n) = n \oplus \lfloor n/2 \rfloor$ and $n \ge 1$, $\binom{n + G(n)}{n}$ is even and $v _ 2 \binom{n + G(n)}{n} + 1 \le v _ 2 \binom{n + (n \oplus 2n)}{n}$; and the sharp slope laws $2 v _ 2 \binom{11 n}{n} + 2 \le 5 s _ 2(n)$, $3 v _ 2 \binom{25 n}{n} + 3 \le 8 s _ 2(n)$, $4 v _ 2 \binom{55 n}{n} + 8 \le 13 s _ 2(n)$ for $n \ge 1$, each attained with equality on an explicit infinite family.

## For Non-Mathematicians

When you add two binary numbers, carries ripple from digit to digit. A classical fact (Kummer's theorem) says the number of carries in that addition tells you exactly how many times 2 divides a certain huge counting number (a binomial coefficient, the number of ways to choose a team). This package turns that fact into a small machine: a finite table of states reads the digits of a number one at a time, keeping a running tally of carries. Instead of arguing separately for every number, it checks a short table once, by computer, and the proof assistant derives a statement about every number, however many digits. It uses the machine to prove several new exact counting laws, for example how often 2 divides the number of ways to choose n items out of n + (n XOR 2n), and best-possible ceilings (slopes such as 5/2, 8/3 and 13/4) for choosing n items out of 11n, 25n and 55n.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of Legendre and Kummer from scratch, a finite carry-valuation automaton engine with `decide`-checked certificates, and exact shifted-bitwise, Gray-code and sharp-slope binomial valuation laws over unbounded $\mathbb{N}$.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `v2_binom_add_popcount` | Kummer: for all $a, b$, $v _ 2 \binom{a + b}{a} + s _ 2(a + b) = s _ 2(a) + s _ 2(b)$. |
| `v2_trinom_add_popcount` | Trinomial Kummer: for all $a, b, c$, $v _ 2$ of the trinomial coefficient $\frac{(a + b + c)!}{a!\, b!\, c!}$ plus $s _ 2(a + b + c)$ equals $s _ 2(a) + s _ 2(b) + s _ 2(c)$. |
| `shifted_xor_kummer_exact` | For all $n$, $2 v _ 2 \binom{n + (n \oplus 2n)}{n} = 2 s _ 2(n) + s _ 2(n \oplus 2n)$. |
| `shifted_or_kummer_exact` | For all $n$, $v _ 2 \binom{n + (n \mathbin{|} 2n)}{n} = s _ 2(n \mathbin{|} 2n)$. |
| `gray_binom_even` | For every $n \ge 1$, $2$ divides $\binom{n + G(n)}{n}$ where $G(n) = n \oplus \lfloor n/2 \rfloor$ is the Gray code. |
| `gray_strictly_below_shifted_xor` | For every $n \ge 1$, $v _ 2 \binom{n + G(n)}{n} + 1 \le v _ 2 \binom{n + (n \oplus 2n)}{n}$. |
| `binom_11n_sharp_slope` | For every $n \ge 1$, $2 v _ 2 \binom{11 n}{n} + 2 \le 5 s _ 2(n)$. |
| `binom_55n_sharp_infinite` | On the explicit infinite family $n _ m$ (`fam55`), $4 v _ 2 \binom{55 n _ m}{n _ m} + 8 = 13 s _ 2(n _ m)$ and $s _ 2(n _ m) = 4m + 8$, so the slope $13/4$ and offset $8$ are sharp. |

## Proof Architecture

1. **Foundations (`v2_fact_add_popcount`, `v2_binom_add_popcount`, `v2_trinom_add_popcount`):** structurally recursive `fact`, `binom`, `trinom`, `popcount` and `v2`; exact characterization of `v2` by divisibility; Legendre then Kummer then trinomial Kummer, with no Mathlib.
2. **Engine (`CVA.coboundary_sound`, `CVA.lower_sound`, `CVA.upper_sound`, `CVA.pumping_exact`):** generic finite-state automaton over bits with recursive evaluation; each lifting theorem is an induction on $n$ against a finite `decide`-checkable certificate.
3. **Shifted-bitwise and Gray laws:** each law is a $3$- or $4$-state exact coboundary or tropical certificate for the automaton reading the pair of bit-streams of $n$ and its shift.
4. **Slope laws (`kBinom_upper_pos_of_cert`, `binom_11n_sharp_slope`, `binom_55n_sharp_infinite`):** a parametric $2(k - 1)$-state automaton for $\binom{kn}{n}$ with the certificate for $k = 11, 25, 55$ (20, 48, 108 states) checked by `decide`; `fam55` comes from a pumping lasso.

## Prior-Art Context

- **Classical foundations:** Legendre (1808) and Kummer (1852); carry-counting automata and digit-sum transducers in the style of Karp (1978) and Heuberger and Prodinger, as noted by the referee, are the closest prior art for the automaton viewpoint and should be cited alongside this package.
- **What is new (referee-4 / referee-7 reading):** novelty audited at 4.2 / 5 (Tier A+ / S-Tier candidate); the zero-slack pumping lemma `CVA.pumping_exact` that certifies sharpness of both slope and offset, the Gray-code binomial laws, and the sharp $k$-binomial slopes at $k = 11, 25, 55$ were judged fresh. The shifted-bitwise Kummer collapse laws are instances of Kummer's theorem on bitwise-shifted arguments and are presented as consequences of the engine.
- **Verdict status:** Referee-4 `PASS` (swarm board #47); novelty note recorded in `REGISTRY.md`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib). See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts, [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest, and `scripts/explore_and_verify.py` for the exact-integer exploration and verification script (zero floating point).
