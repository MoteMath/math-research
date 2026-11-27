# Carry-Less $\mathbb{F} _ 2[x]$-Lift Monomial Determinants (`clmul-lift-determinants`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **7 / 10** | **9 / 10** | **88 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): high novelty and surprise for a $\{2^k - 1, 2^k, 2^k + 1\}$ vanishing locus (no prior record was found by the authors; the search was not recorded) and exact bit-reversed Hadamard Schur collapse over arbitrary commutative rings.*

## For Mathematicians

Let $P _ a(x) = \sum _ {r : \mathrm{bit} _ r(a)=1} x^r \in \mathbb{F} _ 2[x]$ and let $\mathrm{lift} _ {\mathbb{Z}} : \mathbb{F} _ 2[x] \to \mathbb{Z}[t]$ lift each binary coefficient directly into $\{0, 1\} \subset \mathbb{Z}$. For the $n \times n$ symmetric polynomial matrix $(M _ n(t)) _ {i,j} = \mathrm{lift} _ {\mathbb{Z}}(P _ {2i+1} \cdot _ {\mathbb{F} _ 2[x]} P _ {2j+1})(t)$ over an arbitrary commutative ring $R$, we construct an explicit division-free elimination matrix $X _ {k,m}(t) \in R^{2^k \times m}$ whose Schur complement collapses identically to $(-2 t^{k+1}) H _ {k,m}^{\mathrm{rev}}$, a scaled leading principal submatrix of the bit-reversed Sylvester Hadamard matrix $(H _ {k,m}^{\mathrm{rev}}) _ {r,j} = (-1)^{\mathrm{popcnt} _ k(\mathrm{bitrev} _ k(r) \mathbin{\&} j)}$. This yields closed-form single-monomial determinants $\pm 2^a t^b$ at every $n \in \{2^k - 1, 2^k, 2^k + 1\}$, identical vanishing $\det(M _ n(t)) = 0$ on every gap $2^k + 2 \le n \le 2^{k+1} - 2$ over every commutative ring $R$, and a complete non-vanishing characterization over integral domains with $2 \ne 0$ and $t \ne 0$.

## For Non-Mathematicians

Computers can multiply binary numbers in two ways: ordinary multiplication (which carries overflow bits to the left) and "carry-less" multiplication (which simply forgets all carries, a core operation built into modern CPUs for encryption and error-correcting codes). If you make an $n \times n$ multiplication table of odd numbers using carry-less multiplication and compute its determinant (a single summary number measuring how independent the table's rows are), you might expect messy, unpredictable values. Instead, the determinant is **almost always zero** — except when the table size $n$ is right next to a power of $2$ ($2^k - 1$, $2^k$, or $2^k + 1$, like $7, 8, 9$ or $15, 16, 17$), where it snaps into an exact power of $2$! Even more surprisingly, the hidden reason is a bit-reversed checkerboard pattern (a Hadamard matrix) buried inside the table.

---

A complete, sorry-free Lean 4 / Mathlib formalization proving that the odd carry-less multiplication (`CLMUL`) $\{0, 1\}$-lift polynomial matrix

```math
\bigl(M_n(t)\bigr)_{i,j} = \mathrm{lift}_{\mathbb{Z}}\bigl(P_{2i+1} \cdot_{\mathbb{F}_2[x]} P_{2j+1}\bigr)(t) \qquad (0 \le i, j < n),
```

where $P _ a(x) = \sum _ {r : \mathrm{bit} _ r(a)=1} x^r \in \mathbb{F} _ 2[x]$ and $\mathrm{lift} _ {\mathbb{Z}}$ evaluates the resulting binary coefficient word as a $\{0, 1\}$-polynomial at $t \in R$, has **exact single-monomial determinants** at $n \in \{2^k - 1, 2^k, 2^k + 1\}$ and **vanishes identically** on every gap $2^k + 2 \le n \le 2^{k+1} - 2$ over **every commutative ring** $R$.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `det_oddClmulMatrix_pow_two` | For every $k \ge 1$, every commutative ring $R$, and every $t \in R$, $\det(M _ {2^k}(t)) = (\text{if } k = 2 \text{ then } 1 \text{ else } -1) \cdot 2^{k \cdot 2^{k-1}} \cdot t^{(k-1) 2^k + 1}$. |
| `det_oddClmulMatrix_pow_two_add_one` | For every $k \in \mathbb{N}$, every commutative ring $R$, and every $t \in R$, $\det(M _ {2^k + 1}(t)) = (-2 t^{k+1}) \cdot \det(M _ {2^k}(t))$. |
| `det_oddClmulMatrix_pow_two_sub_one` | For every $k \ge 1$, every commutative ring $R$, and every $t \in R$, $\det(M _ {2^k - 1}(t)) = (\text{if } k \le 3 \text{ then } 1 \text{ else } (-1)^{k-1}) \cdot 2^{k \cdot 2^{k-1} - k} \cdot t^{(k-1) 2^k + 1 - k}$. |
| `det_oddClmulMatrix_eq_zero_of_gap` | For every $k \in \mathbb{N}$, every $2^k + 2 \le n \le 2^{k+1} - 2$, every commutative ring $R$, and every $t \in R$, $\det(M _ n(t)) = 0$. |
| `det_oddClmulMatrix_ne_zero_iff` | Over any integral domain $R$ with $2 \ne 0$ and $t \ne 0$, $\det(M _ n(t)) \ne 0$ **if and only if** $n \in \{2^k - 1, 2^k, 2^k + 1\}$ for some $k \in \mathbb{N}$. |

Evaluating at $t = 2$ yields the integer carry-less multiplication matrix $(\mathrm{clmul}(2i+1, 2j+1)) _ {0 \le i, j < n}$, whose determinant at $n = 2^k$ is $\pm 2^{(3k - 2) 2^{k - 1} + 1}$, while every $n \notin \{2^k - 1, 2^k, 2^k + 1\}$ gives determinant $0$.

## Proof Architecture (Division-Free Polynomial Schur Reduction to Bit-Reversed Hadamard)

For any $k \ge 0$ and $1 \le m \le 2^k$, decompose $M _ {2^k + m}(t) = \begin{pmatrix} A & B \\ B^T & C \end{pmatrix}$ with $A = M _ {2^k}(t)$.

1. **Explicit Polynomial Elimination Matrix $X _ {k, m}(t)$ (No Division):**
   Define the $2^k \times m$ matrix $X _ {k, m}(t)$ over $R$ column-by-column:
   - Column $0$: $(1 + t^{k+1})\, e _ 0$.
   - Column $j = 2^v (2q + 1)$ ($v = \mathrm{ctz}(j) < k$, $q = \lfloor j / 2^{v+1} \rfloor < 2^{k - 1 - v}$):
     ```math
     X_{:, j} = e_j + t^{v + 1}\bigl(e_{2^{k - 1 - v} + q} - e_q\bigr).
     ```
   Using the fundamental binary carry-free lift law $\mathrm{eval}(a \oplus b) = \mathrm{eval}(a) + \mathrm{eval}(b) - 2\,\mathrm{eval}(a \mathbin{\&} b)$, the shift $2(2^k + j) + 1 = 1 \oplus 2^{v+1}(2(2^{k-1-v} + q) + 1)$ causes every overlap term with $a = 2i + 1 < 2^{k+1}$ to cancel identically, giving $A X _ {k, m} = B$ over **every** commutative ring $R$.

2. **Exact Bit-Reversed Hadamard Schur Complement:**
   For rows $a = 2(2^k + r) + 1$ ($r < 2^k$), the single extra overlap at bit $k + 1$ equals bit $k - v$ of $\mathrm{clmul}(a, 2q + 1)$, which bijects cleanly onto $\mathrm{popcnt} _ k(\mathrm{bitrev} _ k(r) \mathbin{\&} j) \bmod 2$. Hence the Schur complement collapses identically to a scaled $m \times m$ leading principal submatrix of the **bit-reversed Sylvester Hadamard matrix** $(H _ {k, m}^{\mathrm{rev}}) _ {r, j} = (-1)^{\mathrm{popcnt} _ k(\mathrm{bitrev} _ k(r) \mathbin{\&} j)}$:
   ```math
   \det\bigl(M_{2^k + m}(t)\bigr)
   = \det\bigl(M_{2^k}(t)\bigr) \cdot \bigl(-2 t^{k+1}\bigr)^m \cdot \det\bigl(H_{k, m}^{\mathrm{rev}}\bigr).
   ```

3. **Exact Determinants of $H _ {k, m}^{\mathrm{rev}}$:**
   - **$m = 1$:** $\det = 1$, immediately giving Theorem 2.
   - **$2 \le m \le 2^k - 2$:** $\det = 0$ over every commutative ring $R$ (rows $0$ and $1$ coincide when $m \le 2^{k-1}$; for $2^{k-1} < m \le 2^k - 2$, the unimodular row combination $\sum _ {r=0}^{2^{k-1}-1} (-1)^{\mathrm{popcnt} _ {k-1}(r)} \mathrm{Row} _ r = 0$ via bit-flip pairing), giving Theorem 4.
   - **$m = 2^k$:** $\det(H _ k^{\mathrm{rev}}) = \mathrm{sign}(\mathrm{bitrev} _ k) \cdot \det(H _ k) = (\text{if } k \in \{1, 2\} \text{ then } -1 \text{ else } 1) \cdot 2^{k \cdot 2^{k-1}}$, where $\mathrm{sign}(\mathrm{bitrev} _ k) = +1$ for all $k \ge 3$ is proved by conjugating outer/inner fibers, giving Theorem 1 by induction.
   - **$m = 2^k - 1$:** From $H _ k^{\mathrm{rev}} (H _ k^{\mathrm{rev}})^T = 2^k I$ and the $(2^k - 1, 2^k - 1)$ cofactor entry of the adjugate identity $2^k\,\mathrm{adj}(H _ k^{\mathrm{rev}}) = \det(H _ k^{\mathrm{rev}})\,(H _ k^{\mathrm{rev}})^T$, lifted from $\mathbb{Q}$ to $\mathbb{Z}$ to $R$, giving Theorem 3.

## Prior-Art Context

Carry-less multiplication over $\mathbb{F} _ 2[x]$ (`PCLMULQDQ` / `PMULL`) is a standard hardware instruction in cryptography and coding theory, and Sylvester Hadamard matrices $H _ k$ (along with bit-reversal permutations) are classical objects in harmonic analysis and signal processing. However, lifting carry-less products of odd integers back to $\mathbb{Z}[t]$ and taking leading principal determinants yields an unexpected sparse non-vanishing locus $n \in \{2^k - 1, 2^k, 2^k + 1\}$ with pure-monomial determinants governed by the bit-reversed Hadamard Schur complement. No prior record of this determinant family, its $\{2^k - 1, 2^k, 2^k + 1\}$ vanishing dichotomy, or the polynomial elimination matrix $X _ {k, m}(t)$ was found by the authors; the search was not recorded.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
