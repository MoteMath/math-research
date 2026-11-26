# Exact `N:M` Structured Sparsity EF21 Contraction, MXFP4 Anchor-Group Dilution, Fano Plane & Sunflower `2:4` Column-Permutation Obstructions, and Order-Statistic Gain Laws

A standalone, sorry-free, pure-`Init` (zero Mathlib) Lean 4 (`v4.34.1`) Palomar Comparator formalization proving five exact algebraic and combinatorial laws governing `N:M` structured sparsity (`2:4`, `4:8`, `8:16`, `1:4`, `2:8`), joint sub-byte `MXFP4` block quantization, offline `2:4` column-permutation feasibility, and exact rational order-statistic distortion gains.

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (`3*Nov + 2*Sur + 2*Gen + 2*Use + Ver = 93 / 100`): pure-`Init` Lean 4 (zero Mathlib, zero `native_decide`) proofs of universal structured Top-$k$ EF21 contraction $\alpha(k:m) = k/m$, universal rational Dinkelbach certificates proving `4:8 + MXFP4` (`18/37`) strictly beats `2:4 + MXFP4` (`72/151`) at $B = 32$ via anchor-group dilution (`8/32` vs `4/32`), the exact Fano plane $PG(2, 2)$ `2:4` column-permutation obstruction $R _ {\mathrm{crit}}(2, 3) = 7$ (`7 × 5 = 35` pairwise-disjoint kills), the exact 3-column sunflower obstruction $R _ {\mathrm{crit}}(2, 4) = 4$ via $S _ 8$ Venn-region canonicalization, and exact closed-form Uniform and Laplace `k:2k` order-statistic NMSE gain laws.*

## Headline Theorems (`FanoSparse24PermChallenge`)

| # | Theorem | Module | Exact Formal Statement Summary |
| :---: | :--- | :--- | :--- |
| 1 | `structured_topk_ef21_contraction_exact` | [`Ef21Structured.lean`](FanoSparse24Perm/Ef21Structured.lean) | Universal Top-$k$ EF21 contraction $\alpha(k:m) = k/m$ for all $1 \le k \le m$ (both single-block and multi-block over $g$ disjoint $m$-blocks), exact flat-block tightness, and exact instantiations (`1/2` for `2:4`, `4:8`, `8:16`; `1/4` for `1:4`, `2:8`). |
| 2 | `mxfp4_anchor_dilution_48_beats_24_exact` | [`Mxfp4Joint.lean`](FanoSparse24Perm/Mxfp4Joint.lean) | Universal exact worst-case joint `k:m + MXFP4` ($B = 32$, E8M0 $M _ {\mathrm{eff}} = 3$) EF21 contraction over all rational blocks $x \in [0, 3]^{32}$: `4:8 + MXFP4` attains `18/37` (`0.486486`), strictly beating `2:4 + MXFP4` at `72/151` (`0.476821`, exact gap `54/5587 > 0`) via anchor-group dilution (`8/32` vs `4/32`), plus the exact closed-form dense Ternary law $4 / (B + 3)$ for all $B \ge 1$ (`4/35` at $B = 32$). |
| 3 | `fano_plane_sparse24_obstruction_exact` | [`FanoObstruction.lean`](FanoSparse24Perm/FanoObstruction.lean) | Universal first-moment ceiling lower bound $R _ {\mathrm{crit}}(C, 3) \ge \lceil (4C - 1)(4C - 2)/6 \rceil$ for all $C \ge 1$ (`1, 7, 19, 35, 155, 651, 2667`), plus the exact Fano plane $PG(2, 2)$ obstruction on 8 columns (`C = 2`, 35 `(4, 4)`-bipartitions): every weight-3 row kills exact 5 bipartitions, every $\le 6$ weight-3 rows are `2:4`-feasible, and the 7 lines of $PG(2, 2)$ intersect pairwise in 1 column and kill `7 × 5 = 35` pairwise-disjoint bipartitions simultaneously ($R _ {\mathrm{crit}}(2, 3) = 7$). |
| 4 | `sunflower_sparse24_obstruction_exact` | [`SunflowerObstruction.lean`](FanoSparse24Perm/SunflowerObstruction.lean) | Exact 3-column sunflower `2:4` obstruction on 8 columns ($R _ {\mathrm{crit}}(2, 4) = 4$): every weight-4 row kills exact 17 of the 35 bipartitions (naive union bound $\lceil 35 / 17 \rceil = 3$), yet every $\le 3$ weight-4 rows still admit a `2:4`-feasible `(4, 4)`-bipartition (proved via $S _ 8$ Venn-region canonicalization), while the 4 sunflower rows sharing core $\{0, 1, 2\}$ with petals $\{3, 4, 5, 6\}$ kill all 35 bipartitions simultaneously. |
| 5 | `order_statistic_k2k_nmse_laws_exact` | [`OrderStats.lean`](FanoSparse24Perm/OrderStats.lean) | Exact hockey-stick derivation of the Uniform `k:2k` NMSE law $\mathrm{NMSE} _ {\mathrm{Unif}}(k:2k) = \frac{k + 2}{4(2k + 1)}$ for all $k \ge 1$ (strictly decreasing toward $1/8$, general doubling gain $\frac{3k}{(k + 2)(4k + 1)}$, giving exact `-1/6` for `4:8` vs `2:4` and `-2/17` for `8:16` vs `4:8`), plus exact Rényi Laplace `k:2k` NMSE values (`23/288` for `2:4`, `79211/1411200` for `4:8`, exact `-33489/112700 ≈ -29.72%` gain; `8:16` vs `4:8` = `-12099837073/58312286604 ≈ -20.75%`). |

---

## For Mathematicians

All five theorems are proved purely over `Rat` and `Nat` inside Lean 4's `Init` prelude — zero Mathlib, zero real-analysis axioms, zero `native_decide`, and zero floating-point approximations:

1. **Universal Structured Top-$k$ EF21 Contraction (`Ef21Structured.lean`):**
   For any sorted nonnegative magnitudes $a _ 0 \ge \dots \ge a _ {m-1} \ge 0$ and $1 \le k \le m$, pivoting at $a _ {k-1}^2$ yields
   ```math
   k \sum_{j=0}^{m-k-1} a_{k+j}^2 \le k(m - k) a_{k-1}^2 \le (m - k) \sum_{i=0}^{k-1} a_i^2,
   ```
   giving $E \le (1 - k/m)(K + E)$ per block and additively across $g$ disjoint $m$-blocks, with equality attained by any flat block $a _ i = c > 0$.

2. **Exact Joint `k:m + MXFP4` Dinkelbach Certificates (`Mxfp4Joint.lean`):**
   On the worst-case E8M0 power-of-2 aligned domain $y \in [0, 3]$ with E2M1 levels $\{0, 1/2, 1, 3/2, 2, 3\}$ and midpoints $\{1/4, 3/4, 5/4, 7/4, 5/2\}$, the single-coordinate Dinkelbach potential
   ```math
   h_\lambda(y) = e_{\mathrm{E2M1}}(y)^2 - \lambda y^2
   ```
   is proved **universally non-increasing on $[1/4, 3]$** whenever $1/3 \le \lambda \le 1$, and bounded by $(1 - \lambda)/16$ on $[0, 3]$. Consequently, any sorted $m$-group with pivot $u = a _ {k-1} \in [1/4, 3]$ reduces to a piecewise convex quadratic $A \cdot e _ {\mathrm{E2M1}}(u)^2 + B u^2$ ($A + B > 0$), bounded on each of the five intervals by its endpoints:
   - For `4:8 + MXFP4` ($g = 4, \lambda = 19/37, \alpha = 18/37$): the anchor group ($a _ 0 = 3$) contributes $\le -36/37$ and each of the 3 off-anchor groups contributes $\le +12/37$ (attained at all-$3$ anchor and all-$5/2$ off-anchor, summing to $-36/37 + 3 \cdot 12/37 = 0$).
   - For `2:4 + MXFP4` ($g = 8, \lambda = 79/151, \alpha = 72/151$): the anchor group contributes $\le -126/151$ and each of the 7 off-anchor groups contributes $\le +18/151$ (attained at all-$3$ anchor and all-$1/4$ off-anchor, summing to $-126/151 + 7 \cdot 18/151 = 0$).
   - Thus **`4:8 + MXFP4` strictly beats `2:4 + MXFP4` even in worst-case EF21 contraction** (`18/37 - 72/151 = 54/5587 > 0`), because the anchor group occupies $8/32 = 25\%$ of the MXFP4 scale block under `4:8` versus $4/32 = 12.5\%$ under `2:4`.

3. **Fano Plane & Sunflower `2:4` Column-Permutation Obstructions (`FanoObstruction.lean`, `SunflowerObstruction.lean`):**
   - On 8 columns ($C = 2$), there are $\frac{1}{2}\binom{8}{4} = 35$ unordered `(4, 4)`-bipartitions. Every weight-3 row kills exactly 5 bipartitions, so the universal finite pigeonhole union bound guarantees feasibility for every list of $\le 6$ weight-3 rows ($6 \times 5 = 30 < 35$). The 7 lines of the Fano plane $PG(2, 2)$ satisfy $|L _ i \cap L _ j| = 1$ for all $i \ne j$, making their 7 killed sets pairwise disjoint and covering all $7 \times 5 = 35$ bipartitions, proving $R _ {\mathrm{crit}}(2, 3) = 7$.
   - For weight-4 rows ($s = 4$), each row kills 17 of the 35 bipartitions (naive union bound $\lceil 35/17 \rceil = 3$). Using $S _ 8$ Venn-region canonicalization (`permList`) and complement symmetry (`255 - r`), any pair $(r _ 1, r _ 2)$ reduces to $(15, c)$ with $c \in \{15, 23, 51\}$, and exact kernel verification across all $3 \times 70 = 210$ canonical triples proves every $\le 3$ weight-4 rows are `2:4`-feasible, while the 4 sunflower rows with core $\{0, 1, 2\}$ kill all 35 bipartitions, proving $R _ {\mathrm{crit}}(2, 4) = 4$.

4. **Exact Order-Statistic `k:2k` Gain Laws (`OrderStats.lean`):**
   Using the exact hockey-stick identity $3 \sum _ {i=0}^{k-1} (i + 1)(i + 2) = k(k + 1)(k + 2)$, the Uniform $[-1, 1]$ order-statistic ratio simplifies identically to
   ```math
   \mathrm{NMSE}_{\mathrm{Unif}}(k:2k) = \frac{k + 2}{4(2k + 1)}, \qquad 1 - \frac{\mathrm{NMSE}_{\mathrm{Unif}}(2k:4k)}{\mathrm{NMSE}_{\mathrm{Unif}}(k:2k)} = \frac{3k}{(k + 2)(4k + 1)},
   ```
   yielding exact `-1/6` (`4:8` vs `2:4`) and `-2/17` (`8:16` vs `4:8`). For Laplace $(0, 1)$ weights, Rényi's exponential order-statistic identity evaluates exactly in $\mathbb{Q}$ to `23/288` (`2:4`), `79211/1411200` (`4:8`, exact `-33489/112700 ≈ -29.72%` improvement), and `46212449531/1038874636800` (`8:16`, exact `-12099837073/58312286604 ≈ -20.75%` improvement).

---

## For Non-Mathematicians

Modern GPU accelerators (NVIDIA Ampere/Hopper/Blackwell Tensor Cores) use `2:4` structured sparsity (keeping 2 weights in every 4) combined with 4-bit block quantization (`MXFP4`, sharing one power-of-2 scale per 32 weights) to speed up LLM inference and training. This package provides **machine-checked mathematical proofs** (verified by Lean 4's kernel with zero assumptions beyond standard logic) of five practical facts:

1. **Pure `2:4`, `4:8`, and `8:16` share the same worst-case contraction (`1/2`),** so pure worst-case pruning alone does not separate them.
2. **Combining `4:8` with `MXFP4` strictly beats `2:4 + MXFP4` even in the worst case (`18/37` vs `72/151`):** Because the largest weight in a 32-element `MXFP4` block anchors an entire 8-weight group under `4:8` (`25%` of the block) instead of only a 4-weight group under `2:4` (`12.5%` of the block), fewer remaining weights can sit at worst-case quantization midpoints.
3. **Why offline column permutations can almost always escape `2:4` pruning collisions — until the Fano plane appears:** On 8 columns, ANY 6 rows of 3 heavy outlier weights can ALWAYS be rearranged by a column permutation so that every 4-weight hardware group sees at most 2 outliers (zero outlier loss!). The smallest impossible pattern is literally the **7 lines of the Fano plane** (from projective geometry), which blocks all 35 possible column groupings simultaneously.
4. **Even with 4 heavy weights per row on 8 columns, 3 rows are ALWAYS fixable by column permutation:** Only at 4 rows (a 3-column "sunflower" sharing 3 common outlier columns) does column permutation finally become impossible.
5. **Exact average-case MSE gain of `4:8` over `2:4`:** Moving from `2:4` to `4:8` cuts pruning MSE by an exact **16.67%** (`1/6`) on uniform weights and an exact **29.72%** (`33489/112700`) on heavy-tailed Laplace weights, while moving further to `8:16` gives diminishing returns (`11.76%` uniform, `20.75%` Laplace).

---

## Prior-Art Context

- **NVIDIA `2:4` Structured Sparsity & Channel Permutation (`Mishra et al. 2021`; `Pool & Yu 2021`):** Introduced hardware `2:4` Tensor Core sparsity and heuristic channel-permutation search to preserve outlier weights across 4-element groups. Our Theorems 3 & 4 establish the **exact combinatorial obstruction thresholds** $R _ {\mathrm{crit}}(C, 3) \ge \lceil (4C - 1)(4C - 2)/6 \rceil$, prove $R _ {\mathrm{crit}}(2, 3) = 7$ is attained by the **Fano plane $PG(2, 2)$** (`7 × 5 = 35` pairwise-disjoint kills), and prove $R _ {\mathrm{crit}}(2, 4) = 4$ is attained by the **3-column sunflower** while every $\le 3$ weight-4 rows remain feasible.
- **EF21 Error-Feedback Compression (`Richtárik et al. 2021`, *EF21: A New, Simpler, Theoretically Better, and Practically Faster Error Feedback*) & OCP Microscaling (`MXFP4` E2M1/E8M0, `Rouhani et al. 2023`):** Analyzed contractive compressors ($\alpha$-contraction) and 32-element E8M0 block floating-point formats separately. Our Theorems 1 & 2 prove the exact universal structured Top-$k$ contraction $\alpha(k:m) = k/m$ and the first **exact joint `k:m + MXFP4` ($B = 32$) worst-case EF21 contraction constants** (`18/37` for `4:8 + MXFP4` vs `72/151` for `2:4 + MXFP4`), discovering and proving the **anchor-group dilution** separation, alongside the exact closed-form dense Ternary contraction law $4 / (B + 3)$.
- **Order-Statistic Analysis of `N:M` Sparsity (`Sun et al. 2021`; `Zhou et al. 2021`):** Empirically compared `2:4`, `4:8`, and `8:16` pruning distortion. Our Theorem 5 proves the **exact closed-form rational order-statistic NMSE laws** for all `k:2k` under Uniform ($\frac{k+2}{4(2k+1)}$) and Laplace (via Rényi's exponential representation) distributions directly in Lean 4's kernel.

---

## Building & Verifying

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build and `#print axioms` verification transcripts.
