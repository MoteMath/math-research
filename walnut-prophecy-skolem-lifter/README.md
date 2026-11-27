# Walnut-Style Base-2 Automatic Predicate & Backward-Prophecy Skolem Lifter (`walnut-prophecy-skolem-lifter`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a zero-trust, pure-Init Lean 4 certificate verifier for first-order base-2 automatic predicates featuring a Backward-Prophecy / Bimachine Skolem lifter (`ProphecyCert`) with 80x–197x state compression over forward subset determinization, applied to prove exact finite square- and cube-period spectra and unconditional fifth-power-freeness for the non-classical Gray-Sum Parity word.*

## For Mathematicians

First-order arithmetic predicates over $\mathbb{N}$ combining addition, order, carry/bitwise transducers, and $2$-automatic sequences compile to synchronized multi-track LSB-first DFAs on $\mathrm{Fin}\, k \to \mathbb{N}$. Standard decision procedures (such as Walnut) run unverified subset determinization and Hopcroft minimization outside a proof assistant. This package separates untrusted certificate synthesis from kernel-checked soundness via four compositional, **pure-data** certificate lifters (zero `Prop` fields, checked by kernel `decide` over balanced binary tries `BTree`, zero `native_decide`):

1. **Trailing-zero pad invariance (`DFA.PadInv`):** Every $k$-track LSB-first DFA invariant under appending an all-zero bit-slice assigns a canonical bit-length-independent truth value $M.\mathrm{eval}(x)$ for all $x : \mathrm{Fin}\, k \to \mathbb{N}$.
2. **Quotient minimization (`HomCert`, `homCert_sound`):** Certifies DFA minimization $M _ 1 \to M _ 2$ via a reachability bitmask and `BTree` quotient map, preserving exact language, `PadInv`, and `eval`.
3. **Bidirectional existential projection (`ExistsCert`, `existsCert_sound`):** Certifies $D(x) \iff \exists y \in \mathbb{N},\; M(y, x)$ using subset bitmasks, bit-packed backward witness slots, and a rank-certified trailing-zero saturation check (`ZeroReachCert`).
4. **Backward-Prophecy / Bimachine Skolem lifter (`ProphecyCert`, `prophecyCert_sound`):** Forward LSB subset determinization of universal avoidance formulas can blow up exponentially ($17{,}895$ states for squares and $20{,}719$ states for cubes on our target word). `ProphecyCert` pairs a compact MSB-first prophecy DFA $B$ with sparse invariant masks, premise coupling, and a local Skolem selector, constructively extracting a natural-number witness $y \in \mathbb{N}$ with **80x–197x state compression** ($223$ and $105$ states).
5. **Global validity/emptiness (`UniversalCert`, `universalCert_sound`):** Certifies $\forall x \in \mathbb{N}^k,\; M.\mathrm{eval}(x) = \mathrm{target}$ from a single reachability bitmask.

We apply the engine to the non-classical $2$-automatic **Gray-Sum Parity word**:

```math
w_{\oplus}(n) := \mathrm{popcount}\big(n + (n \oplus \lfloor n / 2 \rfloor)\big) \bmod 2.
```

After proving the arithmetic-to-automaton bridge `dfaGrayAdd_sound` (a 9-state pad-invariant DFA), we prove over all of $\mathbb{N}$:
- **Exact square-period spectrum (`grayAddParity_exact_square_spectrum`):** $w _ {\oplus}$ contains a square of period $p \ge 1$ if and only if $1 \le p \le 7$.
- **Exact cube-period spectrum (`grayAddParity_exact_cube_spectrum`):** $w _ {\oplus}$ contains a cube of period $p \ge 1$ if and only if $p = 1$.
- **Unconditional fifth-power-freeness (`grayAddParity_fifth_power_free`):** for all $n \in \mathbb{N}$ and $p \ge 1$, there exists $i < 4p$ with $w _ {\oplus}(n + i) \ne w _ {\oplus}(n + i + p)$ (sharp at $n = 2$, which starts `0000`).

We also prove `grayAddParity_non_classical` (separating $w _ {\oplus}$ from Thue–Morse, Rudin–Shapiro, Baum–Sweet, Period-Doubling, $t(3n)$, and their complements), `nonvacuity_all_lifters`, and five kernel-checked adversarial mutation rejections (`neg_test_*_mutated`).

## For Non-Mathematicians

Take any whole number $n$, write it in binary, compute its reflected Gray code $n \oplus \lfloor n/2 \rfloor$, add that back to $n$, and ask whether the resulting number of `1`-bits is odd or even. That produces an infinite sequence of `0`s and `1`s.

Because a sequence of `0`s and `1`s goes on forever, you can never prove by testing examples that a repeating pattern (like a block repeated twice or three times in a row) never appears after some point. Instead, this package builds a small, self-contained proof checker in Lean 4 that verifies compact finite "certificates" for infinite statements about binary numbers. Using a trick called backward prophecy — reading the binary digits in reverse to guess where a mismatch must occur — the certificates shrink by up to nearly 200x, small enough for Lean's kernel to check directly. The result is a complete proof that this binary sequence has consecutive doubled blocks **only** of lengths $1$ through $7$, consecutive tripled blocks **only** of length $1$, and **never** five identical blocks in a row anywhere up to infinity.

## Contents

| Theorem | Statement |
| :--- | :--- |
| `homCert_sound` | Verified `HomCert` preserves word acceptance, `PadInv`, and `eval` on all $\mathbb{N}^k$ |
| `existsCert_sound` | Verified `ExistsCert` characterizes $D.\mathrm{eval}(x) \iff \exists y,\; M.\mathrm{eval}(y, x)$ |
| `prophecyCert_sound` | Verified `ProphecyCert` constructively extracts a witness $y \in \mathbb{N}$ under any reversed premise DFA |
| `universalCert_sound` | Verified `UniversalCert` establishes global validity/emptiness on all $\mathbb{N}^k$ |
| `dfaGrayAdd_sound` | The 9-state `dfaGrayAdd` computes `grayAddParity n` for every $n \in \mathbb{N}$ |
| `grayAddParity_exact_square_spectrum` | `grayAddParity` has a square of period $p \ge 1$ iff $1 \le p \le 7$ |
| `grayAddParity_exact_cube_spectrum` | `grayAddParity` has a cube of period $p \ge 1$ iff $p = 1$ |
| `grayAddParity_fifth_power_free` | `grayAddParity` contains no 5th power of any period $p \ge 1$ |

The layout is `WalnutProphecySkolemLifter/Defs.lean` (engine & word definitions), `WalnutProphecySkolemLifter/Theorems.lean` (soundness proofs, pure-data certificates, and main theorems), `Challenge.lean` (headline statements with `sorry`), `Solution.lean` (proved headline statements), and `scripts/explore_and_verify.py` (exact integer/boolean certificate synthesizer and replay, zero floats).

## Prior Art and Credit

- **Automatic sequences and Presburger decision procedures:** Büchi (1960), Bruyère–Hansel–Michaux–Villemaire (1994), and Mousavi's *Walnut* prover (2016; Shallit 2022, *The Logical Approach to Automatic Sequences*) establish the automaton-theoretic decision framework for $k$-automatic sequences. Standard *Walnut* executes unverified determinization and minimization outside a proof assistant; `WalnutLifter` decouples synthesis from kernel-checked pure-data certificates in standalone Lean 4 `Init`, adding the Backward-Prophecy / Bimachine Skolem lifter (`ProphecyCert`) to overcome forward subset blowup.
- **Square-avoiding binary words:** Binary words avoiding all squares of period $\ge L$ were studied via morphism constructions by Fraenkel–Simpson (1995) and Rampersad–Shallit–Wang (2005). Classical $2$-automatic words (Thue–Morse, Rudin–Shapiro, Baum–Sweet, Period-Doubling, $t(3n)$) all have infinite sets of square periods; here $w _ {\oplus}$ arises directly from carried addition with the reflected Gray code and naturally exhibits finite square spectrum $\{1, \dots, 7\}$ and cube spectrum $\{1\}$.

## Build and Verification

Pinned toolchain `leanprover/lean4:v4.34.1`, pure `Init`, zero external dependencies.

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest.
