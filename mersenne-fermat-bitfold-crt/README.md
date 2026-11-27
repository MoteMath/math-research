# Mersenne Fermat Bitfold CRT (`mersenne-fermat-bitfold-crt`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **6 / 10** | **7 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **74 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): Sharp-to-the-integer Mersenne and signed-Fermat bit-folding absorption thresholds, schedule-invariant carry conservation, the exact minimal-depth dichotomy $d + 2$ versus $d + 1$ for $2^{2^d k}$-bit inputs, the three-round Crandall threshold $c^2 \le 2^k$, and explicit Rademacher CRT idempotents for the tower $2^{2^d k} - 1$. Formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Let $\mathrm{fold}(n) = (n \bmod 2^k) + \lfloor n / 2^k \rfloor$ be the Mersenne fold and let its signed variant reduce modulo $2^k + 1$. The package formalizes the following.

- **Compilers.** A decidable checker for multi-level folding programs lifts a finite stride-parity check to congruence for all $k$ (`prog_congruent_of_check`); a symbolic base-$B$ envelope compiler (`SymPoly`) lifts a finite polynomial-envelope check to exact range bounds for all $k$ with $B _ 0 \le 2^k$, and compiles the canonical 4-, 5- and 6-step circuits for $2^{4k}$, $2^{8k}$ and $2^{16k}$ inputs.

- **Exact thresholds.** After $r$ Mersenne folds every $n < 2^{rk} + 2^k - 1$ is absorbed into $[0, 2^k)$ at its canonical residue, sharp to the single integer; the signed Fermat fold absorbs exactly the asymmetric envelope $[-2^{rk},\, 2^{rk} + 2^k - 1]$ into $[-1, 2^k]$, with dual-end sharpness and the 2-cycle $\{-1, 2^k\}$ dichotomy.

- **Carry conservation.** For every folding schedule that absorbs $n$, the schedule-independent identity $\mathrm{carries} = \mathrm{pop}(n) - \mathrm{pop}(\mathrm{canon}(n))$ holds, with the carry count defined from first-principles ripple-carry propagation (Kummer-style).

- **Minimal depth.** Folding $2^d k$-bit inputs modulo $2^k - 1$ needs exactly $d + 2$ stride rounds: a dyadic schedule of length $d + 2$ always absorbs, and every schedule of length $d + 1$ fails for some input (`mersenne_exact_min_depth_dichotomy`, for $2 \le d \le 2^k$, $k \ge 2$). The same method gives the exact Crandall-prime threshold: three rounds modulo $2^k - c$ absorb all $2k$-bit inputs if and only if $c^2 \le 2^k$, which covers Curve25519 ($k = 255$, $c = 19$).

- **CRT tower.** $(2^k - 1) \cdot \prod _ {j < d} (2^{2^j k} + 1) = 2^{2^d k} - 1$, with explicit Rademacher square-wave idempotents of popcount $2^d$ (Mersenne channel) and $2^{d-1} k$ (each Fermat channel), pairwise orthogonality, partition of unity modulo $2^{2^d k} - 1$, and a dyadic bit-folding butterfly that reconstructs $x$ exactly.

## For Non-Mathematicians

Computers reduce large numbers modulo special values like $2^k - 1$ and $2^k + 1$ by chopping the number into $k$-bit chunks and adding them up, a trick used in fast cryptography and fast multiplication. This package answers precisely: how many rounds of chopping and adding are needed so that the result is guaranteed to fit in $k$ bits, for numbers of every size and every $k$? The threshold is proved sharp to the single integer. It also proves that the total number of carries thrown away is the same no matter how you schedule the folding, and it writes down explicit binary patterns that split the big modulus $2^{2^d k} - 1$ into independent pieces, one per layer of a Fermat-number tower.

## Headline Theorems

The trusted statements are in [`Challenge.lean`](Challenge.lean) (namespace `MersenneFermatBitfoldCrtChallenge`) and are proved in [`Solution.lean`](Solution.lean) with identical signatures.

| Theorem | Statement |
| :--- | :--- |
| `mersenne_exact_threshold` | For $k, r \ge 1$ and $n < 2^{rk} + 2^k - 1$, $r$ Mersenne folds give a value below $2^k$ equal to the canonical residue of $n$ modulo $2^k - 1$. |
| `fermat_exact_envelope` | For $-2^{rk} \le x \le 2^{rk} + 2^k - 1$, $r$ signed Fermat folds land in $[-1, 2^k]$. |
| `total_carry_conservation` | Any positive-stride Mersenne folding schedule that absorbs $n$ returns the canonical residue and removes exactly $\mathrm{pop}(n) - \mathrm{pop}(\mathrm{canon}(n))$ carries. |
| `tower_factorization` | For all $d, k$: $(2^k - 1) \cdot \prod _ {j < d} (2^{2^j k} + 1) = 2^{2^d k} - 1$. |
| `idemM_popcount` | The Mersenne Rademacher idempotent has exactly $2^d$ one bits for every $d$ and $k \ge 1$. |
| `idem_partition_of_unity` | The Mersenne idempotent plus all Fermat idempotents sum to $1$ modulo $2^{2^d k} - 1$. |
| `dyadic_butterfly_exact` | The dyadic bit-folding butterfly tree of $x$ reconstructs $x$ modulo $2^{2^d k} - 1$ exactly, for every $d$, $k \ge 1$ and integer $x$. |
| `mersenne_exact_min_depth_dichotomy` | For $2 \le d$, $2 \le k$, $d \le 2^k$: a positive-stride schedule of length $d + 2$ absorbs every $n < 2^{2^d k}$, while every schedule of length at most $d + 1$ fails for some such $n$. |

## Layout

- [`MersenneFermatBitfoldCrt/Defs.lean`](MersenneFermatBitfoldCrt/Defs.lean): definitions needed to state the headline theorems.
- [`MersenneFermatBitfoldCrt/Theorems.lean`](MersenneFermatBitfoldCrt/Theorems.lean): all proofs (zero `sorry`, zero `native_decide`, zero custom axioms, no imports beyond `Init`).
- [`scripts/explore_and_verify.py`](scripts/explore_and_verify.py): exact pure-`int` replay and sharpness checks (no floating point).

## Scope of the formal statement

All eight headline statements quantify over all `k`, `r`, `d` as stated. The minimal-depth dichotomy (`d + 2` versus `d + 1`) is proved only under the hypotheses `d >= 2`, `k >= 2` and `d <= 2^k`; it makes no claim outside that range.

## Prior-Art Context

- **Mersenne and Fermat folding and Crandall primes:** bit folding for reduction modulo $2^k \pm 1$ is classical (Crandall and Fagin, *Discrete weighted transforms and large-integer arithmetic*, 1994; Crandall and Pomerance, *Prime Numbers: A Computational Perspective*, 2001) and underlies Nussbaumer convolution and Fermat number transforms (Nussbaumer 1981, Rader 1972).
- **Carry counting and CRT idempotents:** carry counts follow Kummer (1852); the factorization $2^{2^d k} - 1 = (2^k - 1) \prod (2^{2^j k} + 1)$ is classical. The conservation law and the CRT-idempotent parts are classical (Kummer, Nussbaumer, Crandall-Fagin). The authors consider the sharp-to-the-integer absorption thresholds, the exact minimal-depth dichotomy, the three-round Crandall threshold $c^2 \le 2^k$ and the explicit Rademacher square-wave idempotents with exact popcounts to be less standard; no prior record was found by the authors, and the search was not recorded.
- **Review status:** not independently reviewed. The package is checked only by the Lean build, the comparator manifest and the finite replay in `scripts/explore_and_verify.py` (which proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. Toolchain: `leanprover/lean4:v4.34.1`.
