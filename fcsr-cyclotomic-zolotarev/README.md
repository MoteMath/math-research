# FCSR Cyclotomic and Zolotarev Engine (`fcsr-cyclotomic-zolotarev`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **7 / 10** | **8 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **79 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): an exact global $2$-adic potential bijection for hardware Feedback-with-Carry Shift Registers of every odd connection integer $q \ge 3$, constructive Goresky-Klapper carry bounds, half-period and $d$-section cyclotomic conservation laws and a from-scratch Zolotarev parity proof of the even-period law, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

A hardware FCSR of width $r$ with connection integer $q = 2c - 1 \ge 3$ evolves on states $(a, m)$ with $a < 2^r$ and integer carry $m$. Its exact integer potential
```math
P _ q(a, m) = \sum _ {j < r} \mathrm{bit}(c, j)\, 2^{j+1}\, (a \bmod 2^{r - 1 - j}) - a - m \cdot 2^r
```
is a global bijection onto $\mathbb{Z}$ conjugating the clock tick to the $2$-adic map $p \mapsto (p - q (p \bmod 2))/2$. We prove, for every odd $q \ge 3$:

1. **Word representation:** $q \cdot W _ n(s) + 2^n P _ q(\mathrm{step}^n s) = P _ q(s)$ for all $n$, with no limits or topology; `step` is a bijection on the periodic core $\{-q < P _ q < 0\}$ with explicit inverse.
2. **Carry bounds and conservation:** constructively $0 \le m \le \mathrm{wt}(c) - 1$ on the core (Goresky-Klapper), and over every periodic orbit $\sum m _ t = (\mathrm{wt}(c) - 1) \sum a _ t$.
3. **Half-period certificate:** if $q \mid (2^h + 1) P _ q(s)$ then $\mathrm{step}^h s$ is the bitwise-and-carry complement of $s$, bits and carries anti-periodic, with exact balance $\sum _ {t < 2h} a _ t = h$.
4. **$d$-section cyclotomic engine:** if $q$ divides the repunit $\sum _ {j < d} 2^{jk}$ then the $d$-equispaced potential sum is quantized as $-q \cdot c(t)$ with section quantum $1 \le c(t) \le d - 1$ of period $k$, giving $\sum _ {j < d} a _ {t + jk} = 2 c(t + 1) - c(t)$ and the full-period bit and carry weights.
5. **Zolotarev even-period law:** if $q \equiv 3, 5 \pmod 8$ (prime or composite) and $2^T \equiv 1 \pmod q$ then $T$ is even, proved from scratch via the inversion parity of the permutation $x \mapsto 2x \bmod q$ and a parity homomorphism, with no Jacobi symbols.
6. **Infinite families:** e.g. $q = 2^k + 3$ for all $k \ge 3$: single-bit carries, an exact $k$-block coupling $P(s) + 3 P(\mathrm{step}^k s) = q\,(W _ k(s) + P(\mathrm{step}^k s))$ and even period on $-1$.

## For Non-Mathematicians

A feedback-with-carry shift register is a tiny hardware circuit: a row of bits that shifts one place each tick, with a feedback that adds some of the bits together and keeps a small carry in memory, much like a car odometer remembering what to carry. Such circuits generate long repeating bit streams used in testing and stream encryption, and their behavior is governed by an odd number q written into the wiring. This package proves, for every odd q and every register size, that a single exact integer (a "potential") captures the entire circuit state, so that the circuit's output is exactly the binary expansion of a fraction with denominator q. From this follow exact guarantees that hold for every wiring: the carry memory never exceeds a bound set by the number of taps, carries and output bits balance exactly over a full cycle, and for suitable q the second half of the cycle is the exact opposite of the first half. The package also proves that when q leaves remainder 3 or 5 on division by 8, the cycle length is always even.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of exact $2$-adic potential, reversibility, conservation and parity laws for Feedback-with-Carry Shift Registers of every odd connection integer $q \ge 3$.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `word_representation_exact` | For every FCSR specification and state $s$ and every $n$, $q \cdot W _ n(s) + 2^n P _ q(\mathrm{step}^n s) = P _ q(s)$: an exact $2$-adic rational representation with no limits. |
| `step_bijection_on_core` | On the periodic core of any FCSR, the clock tick has an exact two-sided inverse: $\mathrm{invStep}(\mathrm{step}\, s) = s$ and $\mathrm{step}(\mathrm{invStep}\, s) = s$. |
| `carry_bounds_on_core` | On the periodic core the carry satisfies $0 \le m \le \mathrm{wt}(c) - 1$ (Goresky-Klapper bounds, proved constructively). |
| `universal_carry_bit_conservation` | Over every periodic orbit of length $T$, $\sum _ {t < T} m _ t = (\mathrm{wt}(c) - 1) \sum _ {t < T} a _ t$. |
| `halfPeriod_certificate` | If $s$ is in the core and $q \mid (2^h + 1) P _ q(s)$, then $\mathrm{step}^h s$ is the complement of $s$, $\mathrm{step}^{2h} s = s$, bits and carries are anti-periodic with shift $h$, and over $2h$ ticks $\sum a _ t = h$ and $\sum m _ t = h (\mathrm{wt}(c) - 1)$. |
| `dSection_cyclotomic_engine` | If $q$ divides the $d$-section repunit $\sum _ {j < d} 2^{jk}$, then for every core state the section quantum $c(t)$ lies in $[1, d - 1]$, is $k$-periodic, $S(t) = -q \cdot c(t)$, and the section bit and carry sums obey the stated conservation laws. |
| `even_period_of_mod8_3_or_5` | For every odd $q \ge 3$ with $q \equiv 3$ or $5 \pmod 8$, if $2^T \equiv 1 \pmod q$ then $T$ is even (prime or composite $q$). |
| `family_pow2_add_3` | For $q = 2^k + 3$ and all $k \ge 3$: tap weight $2$, single-bit carries on the core, exact $k$-block coupling with $W _ k(s) + P(\mathrm{step}^k s) \in \{-3, -2, -1\}$, and every period of the state encoding $-1$ is even. |

## Proof Architecture

1. **Potential bijection (`potential_injective`, `word_representation_exact`, `step_bijection_on_core`):** the potential is built from bit-truncation masks; its inverse `encode` is constructive; the tick commutes with the $2$-adic shift-divide map `divStep`, which gives the word representation by induction on $n$.
2. **Complementation (`complement_potential`, `complement_step`, `carry_bounds_on_core`, `universal_carry_bit_conservation`):** the complement map negates the potential ($P(\mathcal{C}(s)) = -q - P(s)$) and commutes with the tick on all states; the carry bounds follow from the potential bounds plus this involution, and conservation by telescoping over a periodic orbit.
3. **Certificates (`halfPeriod_certificate`, `dSection_cyclotomic_engine`):** a finite divisibility condition on $q$ gives exact state, bit and carry anti-periodicity or section quantization for every core state.
4. **Zolotarev engine (`even_period_of_mod8_3_or_5`):** inversion parity is defined as a Boolean XOR reduction over index pairs, proved a homomorphism under composition, and evaluated on the multiplication-by-$2$ permutation mod $q$, giving parity $q \bmod 8 \in \{3, 5\}$; an odd-length period would force the permutation to be even.
5. **Families (`family_pow2_add_3`):** the specification `specPow2Add3` instantiates the engine at $q = 2^k + 3$.

## Prior-Art Context

- **FCSR theory:** Klapper and Goresky (1997, *Feedback shift registers, 2-adic span, and combiners with memory*) introduced FCSRs and the carry bounds; Arnault and Berger developed the $2$-adic analysis of FCSR sequences. The $2$-adic expansion of $p / q$ and the shape of the periodic core are classical; this package gives an exact integer potential-bijection formulation with a constructive carry-bound proof in kernel-checked form.
- **Zolotarev's lemma:** the parity of multiplication by $a$ modulo a prime is the Legendre symbol (Zolotarev 1872); for odd composite $q$ the even-period statement is also the Jacobi symbol $(2 / q) = -1$ for $q \equiv 3, 5 \pmod 8$. The packaged proof is a from-scratch inversion-parity argument that avoids quadratic reciprocity and is not claimed as a new theorem.
- **Possibly new:** the half-period and $d$-section cyclotomic conservation laws for the full hardware state (bits and carries), the repunit section quantum, and the infinite family laws. Not independently reviewed; no prior-art search is recorded, so "possibly new" means only that the authors did not locate these statements.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib). See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts, [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest, and `scripts/explore_and_verify.py` for the exact-integer exploration and verification script (zero floating point).
