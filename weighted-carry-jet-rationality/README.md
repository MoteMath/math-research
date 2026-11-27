# Weighted Carry-Transducer Bilinear Jet-Lift and Krylov Rationality Engine (`weighted-carry-jet-rationality`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): weighted carry-transducer bilinear jet-lift ($S \to 4 S$) and decidable Krylov-annihilator rationality engine in $\mathbb{Z}[[t]]$, discharging exact binary carry-borrow and parity-correlation rational generating functions, the exact binary triangular-square covariance law, and the universal arbitrary-radix $B \ge 2$ even/odd independence-vs-perfect-square covariance and parity-partition dichotomies, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

We build a reusable **Weighted Carry-Transducer Bilinear Jet-Lift** (`CorrMachine S A → 4 S × 4 S jetMat`, `jetMat_pow_sound`) coupled to a decidable $O(d N ^ 2)$ **Left/Right-Krylov Annihilator Rationality Engine** (`recurrence_of_leftKrylov`, `fps_rational_of_recurrence`, `closedForm_of_recurrence`) operating strictly in exact integer formal power series $\mathbb{Z}[[t]]$ (zero floats, zero reals), bridged directly to hardware radix-$B$ overflow and underflow predicates (`radixCarryState_eq_div`, `radixBorrowState_eq_lt`).

Instantiating the engine discharges: (1) exact rational generating functions in $\mathbb{Z}[[t]]$ and all-4-state closed forms for binary carry-borrow and parity-twisted correlations (`binary_carry_borrow_gf`, `binary_parity_corr_gf`); (2) the exact **Binary Triangular-Square Covariance Law** (`binary_triangular_square_covariance`): $\mathrm{Cov}(C, B) = \mp (2 ^ {w - 1}(2 ^ w - 1)) ^ 2 / 4 ^ w$; and (3) the universal **Arbitrary-Radix $B \ge 2$ Even/Odd Dichotomy** — exact zero carry-borrow covariance in every odd base $B = 2 m + 1$ (`odd_radix_zero_covariance`), exact signed perfect-square covariance in every even base $B = 2 m$ (`even_radix_perfect_square_covariance`), and exact even-vanishing vs. odd-growth parity partition sums (`radix_parity_partition_formula`).

## For Non-Mathematicians

Pick two random $w$-digit numbers in base $B$, add them (counting carries), and subtract them (counting borrows). You might expect carries and borrows to be linked in a messy way that depends on $B$. Instead, we prove an astonishing exact rule for every base $B \ge 2$ and every word length $w$: in every **odd** base (base 3, 5, 7, …) the covariance between carries and borrows is **identically zero**, while in every **even** base (binary, base 4, base 10, …) it is an **exact perfect square**—all proved by an automatic exact-integer generating-function engine.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `WeightedCarryJetRationality/Theorems.lean`, definitions in `WeightedCarryJetRationality/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `jetMat_pow_sound` | The $w$-th power of the $4 S \times 4 S$ bilinear jet matrix applied to `jetBeta` computes all four exact weighted carry-borrow moments at width $w$. |
| `fps_rational_of_recurrence` | Any integer sequence satisfying a finite linear recurrence satisfies an exact rational generating-function identity in $\mathbb{Z}[[t]]$. |
| `binary_carry_borrow_gf` | The binary carry-borrow joint moment sequence satisfies the exact degree-5 rational generating function identity with denominator $[1, -16, 100, -304, 448, -256]$ in $\mathbb{Z}[[t]]$. |
| `binary_parity_corr_gf` | The parity-twisted binary carry-borrow correlation satisfies the exact degree-3 rational generating function identity with denominator $[1, -2, -4, 8]$ in $\mathbb{Z}[[t]]$. |
| `binary_triangular_square_covariance` | For every width $w \ge 1$ and initial flags $c _ 0, b _ 0$, binary carry and borrow counts have exact signed squared-triangular covariance $\mp (2 ^ {w - 1}(2 ^ w - 1)) ^ 2$. |
| `odd_radix_zero_covariance` | In every odd base $B = 2 m + 1$ ($m \ge 1$) and every width $w$, carry and borrow counts have exact zero covariance. |
| `even_radix_perfect_square_covariance` | In every even base $B = 2 m$ ($m \ge 1$) and width $w \ge 1$, carry-borrow covariance is an exact signed perfect square. |
| `radix_parity_partition_formula` | The parity-twisted partition sum vanishes identically in every even base $B$ and equals $\pm B ^ {2 \lfloor w / 2 \rfloor}$ in every odd base $B$. |

## Proof Architecture

1. **Bilinear jet-lift (`CorrMachine`, `jetMat_pow_sound`):** lifts an $S$-state weighted transducer to a $4 S \times 4 S$ integer transfer matrix tracking joint first and second moments simultaneously.
2. **Krylov rationality engine (`recurrence_of_leftKrylov`, `fps_rational_of_recurrence`, `closedForm_of_recurrence`):** converts finite Krylov annihilators into exact rational $\mathbb{Z}[[t]]$ identities and closed forms.
3. **Binary rational GFs & triangular-square law (`binary_carry_borrow_gf`, `binary_parity_corr_gf`, `binary_triangular_square_covariance`):** discharges exact binary generating functions and closed forms via finite certificates.
4. **Universal radix-$B$ dichotomy (`odd_radix_zero_covariance`, `even_radix_perfect_square_covariance`, `radix_parity_partition_formula`):** proves the exact even/odd covariance and parity-partition dichotomies for all $B \ge 2$ and all $w$.

## Prior-Art Context

- **Classical carry Markov chains & transfer matrices:** Holte (*Carries, Combinatorics, and an Amazing Matrix*, AMM 1997) and Diaconis & Fulman (*Carries, shuffling, and symmetric functions*, Adv. Appl. Math. 2009) study carry Markov chains for addition; transfer-matrix rationality in $\mathbb{Z}[[t]]$ is classical (Stanley, *Enumerative Combinatorics* Vol. 1).
- **Referee audit (referee-1 PASS #186; recorded in `REGISTRY.md`):** the mechanized bilinear $4 S \times 4 S$ jet-lift + decidable Krylov rationality engine in $\mathbb{Z}[[t]]$, the exact binary triangular-square covariance law, and the universal radix-$B$ even/odd zero-vs-perfect-square carry-borrow covariance and parity-partition dichotomies are new; zero Section 4 overlap.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
