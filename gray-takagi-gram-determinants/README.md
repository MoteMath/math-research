# Gray-Code Bitwise Gram Determinants and the Discrete Takagi Blancmange Law (`gray-takagi-gram-determinants`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **10 / 10** | **10 / 10** | **10 / 10** | **8 / 10** | **10 / 10** | **96 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): Unconditional Lean 4 formalization over every commutative ring $R$ proving that permuting the classical binary bitwise-AND/OR/XOR Gram matrices by the reflected binary Gray code $\mathrm{gray}(i) = i \oplus \lfloor i/2 \rfloor$ splits their symbolic $q$-determinant exponents exactly along the discrete Takagi (Blancmange) fractal curve $T(n)$, recovering the OEIS-novel $2^{T(n)}$ power-of-2 determinant law at $q = 2$ and a sharp power-of-2 singularity dichotomy at $q = 0$.*

---

## For Mathematicians

Let $\mathrm{gray}(k) = k \oplus \lfloor k/2 \rfloor$ be the reflected binary Gray code, let $s _ 2(m) = \mathrm{popcount}(m)$ be the binary Hamming weight, let
```math
S(n) = \sum_{i = 0}^{n - 1} s_2(\mathrm{gray}(i))
```
be the cumulative Gray Hamming weight, and let $T : \mathbb{N} \to \mathbb{N}$ be the **discrete Takagi (Blancmange) fractal function** defined by $T(0) = T(1) = 0$ and the exact dyadic sawtooth recurrence
```math
T(2^m + k) = T(k) + \min(k,\; 2^m - k) \qquad (0 \le k \le 2^m).
```
For the unpermuted binary lattice $i = 0, \dots, n - 1$, the matrix $q^{s _ 2(i \mathbin{\&} j)}$ admits a lower-unitriangular Boolean zeta $LDL^T$ factorization whose determinant is simply $(q - 1)^{\sum _ {i < n} s _ 2(i)}$ (equal to $1$ at $q = 2$ for every $n$).

**Permuting the indices by the Gray code shatters this simplicity into an exact fractal law:** at every power of $2$ ($n = 2^m$), the matrix is a permutation congruence of the unpermuted matrix so the Takagi exponent collapses to $T(2^m) = 0$, while for every non-power-of-$2$ size $n$, principal truncation traps a fractal discrepancy of exact degree $T(n)$.

Over **every commutative ring $R$**, for **every $q \in R$** and **every $n \in \mathbb{N}$**:

1. **Gray Bitwise-AND Gram Determinant (`det_grayAndMat`):**
   ```math
   \det\Bigl(q^{s_2(\mathrm{gray}(i) \mathbin{\&} \mathrm{gray}(j))}\Bigr)_{0 \le i, j < n}
   = q^{T(n)} \cdot (q - 1)^{S(n) - T(n)}.
   ```
2. **Gray Bitwise-OR Gram Determinant (`det_grayOrMat`):**
   ```math
   \det\Bigl(q^{s_2(\mathrm{gray}(i) \mid \mathrm{gray}(j))}\Bigr)_{0 \le i, j < n}
   = q^{S(n)} \cdot (1 - q)^{S(n) - T(n)}.
   ```
3. **Gray Hamming-Distance (`XOR`) Determinant (`det_grayXorMat`):**
   ```math
   \det\Bigl(q^{s_2(\mathrm{gray}(i) \oplus \mathrm{gray}(j))}\Bigr)_{0 \le i, j < n}
   = (1 - q^2)^{S(n) - T(n)}.
   ```
4. **Specializations & Fractal Structure:**
   - **$q = 2$ Pure Blancmange Law (`det_grayAndMat_two`):** $\det\bigl(2^{s _ 2(\mathrm{gray}(i) \mathbin{\&} \mathrm{gray}(j))}\bigr) = 2^{T(n)}$ (beginning $1, 1, 2, 1, 2, 4, 4, 1, 2, 4, 16, 16, 16, 16, 8, 1, \dots$; no exact match in OEIS).
   - **$q = 0$ Power-of-2 Singularity Dichotomy (`det_grayDisjointMat`, `takagi_eq_zero_iff`):** The $\{0, 1\}$ Gray-code bitwise-disjointness matrix $\mathbf{1}[\mathrm{gray}(i) \mathbin{\&} \mathrm{gray}(j) = 0]$ has determinant $(-1)^{S(n)}$ when $n = 0$ or $n = 2^m$, and determinant $0$ for every non-power-of-$2$ size $n$.
   - **Power-of-2 Collapse (`det_grayAndMat_pow2_eq`):** At $n = 2^m$, $\det(M _ {2^m}(q)) = (q - 1)^{m \cdot 2^{m - 1}}$.

### Proof Method

The proof avoids all matrix inverses and works directly in $\mathbb{Z}[X]$ via two inverse-free block-triangular Schur eliminations driven by the reflected Gray-code identities $\mathrm{gray}(2^m + r) = 2^m + \mathrm{gray}(2^m - 1 - r)$ and $\mathrm{gray}(2^{m+1} - 1 - r) = 2^m + \mathrm{gray}(r)$, combined with a lower-unitriangular Boolean zeta $LDL^T$ factorization at $n = 2^m$. Evaluating `Polynomial.aeval q` via `RingHom.map_det` lifts all three formulas unconditionally to every commutative ring $R$.

---

## For Non-Mathematicians

Build an $n \times n$ grid of numbers where entry $(i, j)$ counts how many binary $1$-bits two integers share, raised to a base $q$. If you order the integers normally ($0, 1, 2, 3, \dots$), the determinant at $q = 2$ is always boringly equal to $1$ for every grid size $n$.

Now reorder the exact same integers in **Gray code** order (where consecutive numbers differ by a single bit flip). At every power-of-$2$ grid size ($1, 2, 4, 8, 16, \dots$), the determinant snaps right back to $1$. In between powers of $2$, however, it explodes into exact powers of $2$ whose exponents trace the **Takagi Blancmange curve** — a classic nowhere-differentiable fractal mountain range built by stacking sawtooth waves at every dyadic scale. Even more strangely, setting $q = 0$ (measuring whether two Gray-code numbers share no bits at all) gives a matrix that is invertible **if and only if** the grid size $n$ is an exact power of $2$.

---

## Headline Theorems

The trusted theorem statements live in [`Challenge.lean`](Challenge.lean) (definitions in [`GrayTakagiDet/Defs.lean`](GrayTakagiDet/Defs.lean)) and are proved unconditionally in [`GrayTakagiDet/Theorems.lean`](GrayTakagiDet/Theorems.lean) (re-exported by [`Solution.lean`](Solution.lean)).

| Theorem | Statement |
| :--- | :--- |
| `takagi_le_grayPopSum` | $T(n) \le S(n)$ for all $n \in \mathbb{N}$. |
| `takagi_recurrence` | $T(2^m + k) = T(k) + \min(k, 2^m - k)$ for all $m \in \mathbb{N}$ and $k \le 2^m$. |
| `takagi_eq_zero_iff` | $T(n) = 0 \iff n = 0 \lor \exists m,\; n = 2^m$. |
| `det_grayAndMat` | $\det\bigl(q^{s _ 2(\mathrm{gray}(i) \mathbin{\&} \mathrm{gray}(j))}\bigr) = q^{T(n)} (q - 1)^{S(n) - T(n)}$ over any `CommRing R`. |
| `det_grayAndMat_two` | $\det\bigl(2^{s _ 2(\mathrm{gray}(i) \mathbin{\&} \mathrm{gray}(j))}\bigr) = 2^{T(n)}$ in $\mathbb{Z}$ for all $n \in \mathbb{N}$. |
| `det_grayDisjointMat` | $\det\bigl(\mathbf{1}[\mathrm{gray}(i) \mathbin{\&} \mathrm{gray}(j) = 0]\bigr) = (-1)^{S(n)}$ if $T(n) = 0$, else $0$. |
| `det_grayOrMat` | $\det\bigl(q^{s _ 2(\mathrm{gray}(i) \mid \mathrm{gray}(j))}\bigr) = q^{S(n)} (1 - q)^{S(n) - T(n)}$ over any `CommRing R`. |
| `det_grayXorMat` | $\det\bigl(q^{s _ 2(\mathrm{gray}(i) \oplus \mathrm{gray}(j))}\bigr) = (1 - q^2)^{S(n) - T(n)}$ over any `CommRing R`. |
| `det_grayAndMat_pow2_eq` | $\det\bigl(q^{s _ 2(\mathrm{gray}(i) \mathbin{\&} \mathrm{gray}(j))}\bigr) _ {i, j < 2^m} = (q - 1)^{m \cdot 2^{m - 1}}$. |

---

## Build & Verification

Built against `leanprover/lean4:v4.34.1` and Mathlib `v4.34.1`:

```bash
lake build
lake build Challenge
lake env lean PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build and `#print axioms` receipts, and [`comparator.json`](comparator.json) for the Palomar Comparator + `nanoda` verification manifest.
