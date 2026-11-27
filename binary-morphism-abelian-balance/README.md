# Binary Word-Morphism Modular-Stratified Abelian Balance Engine (`binary-morphism-abelian-balance`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **10 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **92 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): zero-real `Int × Int` quadratic-ring Brahmagupta compiler and modular-stratified abelian balance certificate engine (`MS-QR-PAIE`), formally proving that modular length stratification strictly beats unstratified Rauzy diameters, discharging the symbolic non-unimodular $\sigma _ k$ exact $k = 7 \to 8$ discriminant phase transition with geometric prefix sharpness and same-matrix balance doubling, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

We build `MS-QR-PAIE`: a zero-real `Int × Int` quadratic-ring Brahmagupta compiler paired with a verified $O(\log n)$ Dumont-Thomas prefix oracle (`dtTakeOnes_spec`) and a pure-data modular-stratified certificate checker (`StratCert`, `stratCert_sound_balance`). By stratifying prefix discrepancies modulo $M$, a finite kernel-checked certificate discharges uniform abelian balance $| |w[i..i+n)| _ 1 - |w[j..j+n)| _ 1 | \le C$ across **all** positions $i, j$ and **all** lengths $n \in \mathbb{N}$.

This engine proves three flagship infinite theorems: (1) for the symbolic non-unimodular family $\sigma _ k$ ($\det = k$, $k \ge 1$), an exact **$k = 7 \to 8$ quadratic-discriminant phase transition** (`2 k ^ 2 - 21 k + 48`, `family_sigmaK_balance`) paired with explicit infinite geometric prefix families realizing the exact extrema (`family_sigmaK_prefix_sharp`); (2) **same-matrix oscillating balance doubling** (`tauA_balance_infinite` with balance $2$ vs. `tauB_balance_infinite` with balance $4$ despite identical incidence matrices); and (3) **formal separation from unstratified Rauzy diameters** (`mu1_unstrat_impossible`, `mu2_unstrat_impossible` vs. `mu1_strat_balance_infinite`, `mu2_strat_balance_infinite`).

## For Non-Mathematicians

Take a binary string built by repeatedly replacing `0` and `1` with short patterns, and ask: how unevenly can the `1`s clump together in two equal-length slices? Instead of using approximate decimals, our engine computes exact integer coordinates in a quadratic number ring and groups lengths by their remainder mod $M$. This proves exact unevenness bounds for entire infinite families of rules—catching a sharp jump between $k = 7$ and $k = 8$ and solving cases where standard ungrouped methods provably cannot give a tight answer.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `BinaryMorphismAbelianBalance/Theorems.lean`, definitions in `BinaryMorphismAbelianBalance/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `stratCert_sound_balance` | Any `StratCert` passing `verifyCert m cert = true` certifies uniform abelian balance $\le C$ across all factor positions $i, j$ and all lengths $n$. |
| `family_sigmaK_balance` | For every $k \ge 1$, the non-unimodular morphism $\sigma _ k$ is uniformly `phaseBound k`-balanced across all factor positions and lengths (exact $k = 7 \to 8$ phase transition). |
| `family_sigmaK_prefix_sharp` | For every $k \ge 2$ and $m \in \mathbb{N}$, explicit infinite geometric prefixes `uMin k m` and `vMax k m` achieve the exact quadratic-ring discrepancy extrema of $\sigma _ k$. |
| `tauA_balance_infinite` | The morphism `tauA` is uniformly 2-balanced across all factor positions $i, j$ and lengths $n$. |
| `tauB_balance_infinite` | The morphism `tauB` (sharing the exact incidence matrix of `tauA`) has doubled uniform balance bound $4$ across all factor positions and lengths. |
| `mu1_unstrat_impossible` | No unstratified Rauzy discrepancy interval can certify balance $\le 2$ for `mu1`. |
| `mu1_strat_balance_infinite` | Modular length stratification certifies uniform balance $\le 2$ for `mu1` across all factor positions and lengths. |
| `mu2_strat_balance_infinite` | Modular length stratification certifies uniform balance $\le 4$ for `mu2` across all factor positions and lengths. |

## Proof Architecture

1. **Zero-real quadratic ring (`QElem := Int × Int`):** implements exact integer arithmetic and decidable order in $\mathbb{Z}[\lambda]$ without reals or floats.
2. **Dumont-Thomas oracle & `StratCert` (`stratCert_sound_prefix`, `stratCert_sound_balance`):** compiles finite modular-stratified discrepancy certificates into universal abelian balance bounds.
3. **Symbolic $\sigma _ k$ phase transition (`family_sigmaK_balance`, `family_sigmaK_prefix_sharp`):** proves the $k = 7 \to 8$ discriminant transition uniformly for all $k \ge 1$ with matching geometric prefix lower bounds.
4. **Separation & doubling (`tauA`/`tauB`, `mu1`/`mu2`, `sharp_*`, `hostile_mutation_rejections`):** formally separates modular stratification from unstratified Rauzy intervals and proves same-matrix balance doubling.

## Prior-Art Context

- **Classical combinatorics on words & balance lineage:** Dumont & Thomas (*Systèmes de numération et fonctions fractales relatifs aux substitutions*, TCS 1989), Adamczewski (*Balances for fixed points of primitive substitutions*, TCS 2003), Berthé & Tijdeman (*Balance properties of multi-dimensional words*, TCS 2002), Rauzy fractals, and Richomme, Saari & Zamboni (*Balance and Abelian complexity of the Tribonacci word*, Adv. Appl. Math. 2010).
- **Referee audit (referee-1 PASS #162, referee-6 S-Tier Flagship 9.5/9.0/9.5 #205; recorded in `REGISTRY.md`):** the zero-real `Int × Int` Brahmagupta compiler + zero-`Prop` `StratCert`, the formal proof that one-step modular length stratification strictly beats unstratified Rauzy diameters (`mu1`/`mu2`), the symbolic non-unimodular $\sigma _ k$ exact $k = 7 \to 8$ phase transition with geometric prefix sharpness, and same-matrix oscillating balance doubling are new; zero Section 4 overlap.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
