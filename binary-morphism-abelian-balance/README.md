# Binary Word-Morphism Modular-Stratified Abelian Balance Engine (`binary-morphism-abelian-balance`)

**Scope of the formal statement.** every balance statement in `Challenge.lean` is an UPPER bound (`<= C`) on `| |w[i..i+n)|_1 - |w[j..j+n)|_1 |`. No theorem says that `tauB` is not 3-balanced, that `sigma_k` attains `phaseBound k`, or that `mu1`/`mu2` cannot be certified with a smaller constant. `phaseBound k` is the piecewise-linear function `k` for `k <= 3`, `2k-3` for `4 <= k <= 7` and `2k-4` for `k >= 8` (`Defs.lean`); the quadratic `2k^2 - 21k + 48` quoted below is not a Lean object.

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **10 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **92 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): zero-real `Int × Int` quadratic-ring Brahmagupta compiler and modular-stratified abelian balance certificate engine (`MS-QR-PAIE`), proving upper bounds on abelian balance (the piecewise-linear `phaseBound k` for the family $\sigma _ k$, `tauA` $\le 2$, `tauB` $\le 4$, `mu1` $\le 2$, `mu2` $\le 4$), explicit prefix families attaining the stated discrepancy values for $\sigma _ k$, and one instance (`mu1`) where a stated inequality and one rejected certificate show that the unstratified ($M = 1$) certificate with $C = 2$ fails, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

We build `MS-QR-PAIE`: a zero-real `Int × Int` quadratic-ring Brahmagupta compiler paired with a verified $O(\log n)$ Dumont-Thomas prefix oracle (`dtTakeOnes_spec`) and a pure-data modular-stratified certificate checker (`StratCert`, `stratCert_sound_balance`). By stratifying prefix discrepancies modulo $M$, a finite kernel-checked certificate discharges uniform abelian balance $| |w[i..i+n)| _ 1 - |w[j..j+n)| _ 1 | \le C$ across **all** positions $i, j$ and **all** lengths $n \in \mathbb{N}$.

This engine proves three flagship infinite theorems: (1) for the symbolic non-unimodular family $\sigma _ k$ ($\det = k$, $k \ge 1$), a uniform balance **upper bound** `phaseBound k` for the symbolic family $\sigma _ k$ (`family_sigmaK_balance`; the piecewise-linear bound switches from `2k-3` to `2k-4` at $k = 8$, which the authors attribute to a quadratic discriminant `2k^2 - 21k + 48` that changes sign between $k = 7$ and $k = 8$, an explanation that is not itself a Lean statement) paired with explicit infinite geometric prefix families whose discrepancies equal the stated quadratic-ring values (`family_sigmaK_prefix_sharp`); (2) **same-matrix balance bounds** (`tauA_balance_infinite` with bound $2$ and `tauB_balance_infinite` with bound $4$, for morphisms with identical incidence matrices; both are upper bounds, so no doubling of the true balance is proved); and (3) **one unstratified-vs-stratified comparison** (`mu1_unstrat_impossible`: a stated inequality and the rejection of one specific unstratified certificate `mu1CertM1_failC2`; against `mu1_strat_balance_infinite` and `mu2_strat_balance_infinite`). There is no `mu2_unstrat_impossible` theorem in `Challenge.lean`.

## For Non-Mathematicians

Take a binary string built by repeatedly replacing `0` and `1` with short patterns, and ask: how unevenly can the `1`s clump together in two equal-length slices? Instead of using approximate decimals, our engine computes exact integer coordinates in a quadratic number ring and groups lengths by their remainder mod $M$. This proves unevenness upper bounds for entire infinite families of rules, including a bound whose formula changes at $k = 8$. For one rule (`mu1`) it also shows that one specific ungrouped certificate fails.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BinaryMorphismAbelianBalance/Theorems.lean`, definitions in `BinaryMorphismAbelianBalance/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `stratCert_sound_balance` | Any `StratCert` passing `verifyCert m cert = true` certifies uniform abelian balance $\le C$ across all factor positions $i, j$ and all lengths $n$. |
| `family_sigmaK_balance` | For every $k \ge 1$, the non-unimodular morphism $\sigma _ k$ is uniformly `phaseBound k`-balanced across all factor positions and lengths (upper bound; `phaseBound` switches from `2k-3` to `2k-4` at $k = 8$). |
| `family_sigmaK_prefix_sharp` | For every $k \ge 2$ and $m \in \mathbb{N}$, explicit infinite geometric prefixes `uMin k m` and `vMax k m` achieve the exact quadratic-ring discrepancy extrema of $\sigma _ k$. |
| `tauA_balance_infinite` | The morphism `tauA` is uniformly 2-balanced across all factor positions $i, j$ and lengths $n$. |
| `tauB_balance_infinite` | The morphism `tauB` (sharing the incidence matrix of `tauA`) is uniformly $4$-balanced across all factor positions and lengths (upper bound only; the Lean statement does not show that $3$ fails). |
| `mu1_unstrat_impossible` | A stated rational-ring inequality for `mu1`, and the unstratified ($M = 1$) certificate `mu1CertM1_failC2` with $C = 2$ is rejected by `verifyCert` (a statement about that one certificate, not about all unstratified intervals). |
| `mu1_strat_balance_infinite` | Modular length stratification certifies uniform balance $\le 2$ for `mu1` across all factor positions and lengths. |
| `mu2_strat_balance_infinite` | Modular length stratification certifies uniform balance $\le 4$ for `mu2` across all factor positions and lengths. |

## Proof Architecture

1. **Zero-real quadratic ring (`QElem := Int × Int`):** implements exact integer arithmetic and decidable order in $\mathbb{Z}[\lambda]$ without reals or floats.
2. **Dumont-Thomas oracle & `StratCert` (`stratCert_sound_prefix`, `stratCert_sound_balance`):** compiles finite modular-stratified discrepancy certificates into universal abelian balance bounds.
3. **Symbolic $\sigma _ k$ bound (`family_sigmaK_balance`, `family_sigmaK_prefix_sharp`):** proves the upper bound `phaseBound k` uniformly for all $k \ge 1$, together with explicit geometric prefixes whose discrepancy values are stated exactly.
4. **Comparisons (`tauA`/`tauB`, `mu1`/`mu2`, `sharp_*`, `hostile_mutation_rejections`):** the `mu1` unstratified-certificate rejection and the `tauA`/`tauB` upper bounds 2 and 4.

## Prior-Art Context

- **Classical combinatorics on words & balance lineage:** Dumont & Thomas (*Systèmes de numération et fonctions fractales relatifs aux substitutions*, TCS 1989), Adamczewski (*Balances for fixed points of primitive substitutions*, TCS 2003), Berthé & Tijdeman (*Balance properties of multi-dimensional words*, TCS 2002), Rauzy fractals, and Richomme, Saari & Zamboni (*Balance and Abelian complexity of the Tribonacci word*, Adv. Appl. Math. 2010).
- **Prior-art status:** not independently reviewed; no literature search was recorded. The authors believe the following are new but this is unchecked: the zero-real `Int × Int` Brahmagupta compiler with a zero-`Prop` `StratCert` checker, the `mu1` unstratified-certificate rejection, the symbolic non-unimodular $\sigma _ k$ bound `phaseBound k` with geometric prefix families, and the `tauA`/`tauB` bounds for same-matrix morphisms.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
