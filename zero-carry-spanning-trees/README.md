# Zero-Carry Spanning Trees

Machine-checked Lean 4 / Mathlib formalization of the alternating-harmonic spectrum and exact Kirchhoff spanning-tree count of mixed-radix zero-carry graphs over arbitrary commutative rings.

## Main results

For any mixed-radix sequence $b : \mathbb{N} \to \mathbb{N}$ with $b _ r \ge 1$ and place values $P _ k = \prod _ {r < k} b _ r$, let $G _ b$ be the **mixed-radix zero-carry graph** on $V = \{0, \dots, P _ k - 1\}$, where distinct vertices $i \ne j$ are adjacent iff adding $i + j$ in mixed radix $b$ produces zero carries across all positions $r < k$ (i.e., $d _ r(i) + d _ r(j) < b _ r$ for all $r < k$). Let $L _ b$ be its graph Laplacian and $\tau(G _ b) = \det(L _ b^{(0,0)})$ its Kirchhoff spanning-tree count.

The trusted statement file [`Challenge.lean`](Challenge.lean) declares 5 universal theorems:

1. **Alternating-harmonic spectrum (`det_zeroCarryWalk_charpoly`):** Over $\mathbb{Q}$, the normalized zero-carry transition matrix $W _ {b,k} = B _ {b,k}^{-1} T _ {b,k}$ (where $B _ {b,k} = \mathrm{diag}(\prod _ {r < k} (b _ r - d _ r(i)))$ and $(T _ {b,k}) _ {i,j} = \mathbf{1} _ {\forall r < k,\, d _ r(i) + d _ r(j) < b _ r}$) is similar via the Kronecker-Pascal matrix $\bigotimes _ {r < k} P _ {b _ r}$ to an explicit upper-triangular matrix, so its characteristic polynomial splits completely over $\mathbb{Q}$:
```math
\det\bigl(x I - W_{b,k}\bigr)
= \prod_{0 \le j < P_k} \left( x - \prod_{r=0}^{k-1} \frac{(-1)^{d_r(j)}}{d_r(j) + 1} \right).
```
2. **Exact mixed-radix spanning-tree formula (`det_zeroCarryCofactor_mixed`):** Over any commutative ring $R$,
```math
\left(\prod_{r=0}^{k-1} \frac{b_r(b_r + 1)}{2}\right) \cdot \det\bigl(L_b^{(0,0)}\bigr)
= \prod_{1 \le j < P_k} \left( \prod_{r=0}^{k-1} \bigl(d_r(j) + 1\bigr) - \prod_{r=0}^{k-1} (-1)^{d_r(j)} \right).
```
3. **Uniform base-$B$ specialization (`det_zeroCarryCofactor_base`):**
```math
\left(\frac{B(B + 1)}{2}\right)^k \cdot \det\bigl(L_{B^k}^{(0,0)}\bigr)
= \prod_{1 \le j < B^k} \left( \prod_{r=0}^{k-1} \bigl(d_r(j) + 1\bigr) - \prod_{r=0}^{k-1} (-1)^{d_r(j)} \right).
```
4. **Binary zero-carry / bitwise-disjoint graph (`det_binaryZeroCarryCofactor`):** Defined directly via native bitwise AND `i &&& j = 0` on $\{0, \dots, 2^k - 1\}$, over any commutative ring $R$ (including characteristic $3$),
```math
\tau(G_{2^k}) = \det\bigl(L_{\mathrm{bin}}^{(0,0)}\bigr)
= \prod_{m = 2}^{k} \bigl(2^m - (-1)^m\bigr)^{\binom{k}{m}}
= 3^{2^k - k - 1} \prod_{m = 3}^{k} J_m^{\binom{k}{m}},
```
where $J _ m = (2^m - (-1)^m) / 3$ are the Jacobsthal numbers ($k = 2, 3, 4, 5, 6 \implies 3,\; 243,\; 71\,744\,535,\; 3^{36}\cdot 5^5 \cdot 11,\; 3^{78}\cdot 5^{15}\cdot 7\cdot 11^6$).
5. **Single-radix half-graph specialization (`det_singleRadixZeroCarryCofactor`):** At $k = 1$,
```math
\frac{B(B + 1)}{2} \cdot \tau(G_{(B)}) = \prod_{j = 1}^{B - 1} \bigl((j + 1) - (-1)^j\bigr).
```

## Proof idea

The key observation is that the self-loop at $i = j$ cancels identically between the degree matrix and adjacency matrix, giving $L _ b = B _ {b,k}(I - W _ {b,k})$ as a pure Kronecker difference. Each 1D factor $W _ b = B _ b^{-1} T _ b$ is upper-triangularized by the unimodular reversed Pascal matrix $(P _ b) _ {i,j} = \binom{b - 1 - i}{j}$ via the hockey-stick identity and an alternating binomial reduction, yielding eigenvalues $(-1)^r / (r + 1)$. Perturbing $L _ b$ by the rank-1 matrix $(B _ {b,k} \mathbf{1})\mathbf{1}^T$ preserves upper-triangularity in the Kronecker-Pascal basis while shifting the $(0,0)$-entry from $0$ to $P _ k$; equating this with the general rank-1 cofactor identity $\det(L + v \mathbf{1}^T) = P _ k (\sum v _ i) \det(L^{(0,0)})$ yields the exact formula over $\mathbb{Q}$, $\mathbb{Z}$, and hence every commutative ring $R$.

## Prior art and related work

- **Single-radix ($k = 1$) threshold graphs:** For $k = 1$, the graph $G _ {(B)}$ ($i \sim j \iff i + j < B$) is a threshold graph; Laplacian spectra and spanning-tree counts of threshold graphs are studied in P. L. Hammer and A. K. Kelmans, *"Laplacian spectra and spanning trees of threshold graphs"*, *Discrete Appl. Math.* **65** (1996), 255–273. For $k \ge 2$ (e.g., $G _ {2^3}$), $G _ b$ contains induced $P _ 4$ subgraphs (such as `011 - 100 - 010 - 101`) and is neither a threshold graph nor a cograph.
- **Spanning trees on fractal / self-similar graphs:** Spanning-tree enumerations on Sierpiński-type graphs are studied in E. Teufl and S. Wagner, *"Spanning trees on Sierpiński graphs"* (2006) and related works. No OEIS entry or prior closed form was found for the binary zero-carry spanning-tree sequence $3, 243, 71\,744\,535, \dots$ or its mixed-radix generalization.

## Layout

- [`ZeroCarrySpanningTrees/Defs.lean`](ZeroCarrySpanningTrees/Defs.lean): Pure-Mathlib definitions only (no proofs).
- [`Challenge.lean`](Challenge.lean): Trusted statement file importing only `ZeroCarrySpanningTrees.Defs`, with `sorry` placeholders for Comparator.
- [`ZeroCarrySpanningTrees/PascalTriangular.lean`](ZeroCarrySpanningTrees/PascalTriangular.lean): 1D alternating binomial identity, hockey-stick lemma, and reversed-Pascal triangularization `W_b * P_b = P_b * U_b`.
- [`ZeroCarrySpanningTrees/SpanningTrees.lean`](ZeroCarrySpanningTrees/SpanningTrees.lean): Mixed-radix Kronecker lift, general rank-1 Kirchhoff cofactor lemma, and proofs of all 5 headline theorems.
- [`Solution.lean`](Solution.lean): Proofs of all 5 challenge statements (zero `sorry`).
- [`scripts/PrintAxioms.lean`](scripts/PrintAxioms.lean) and [`AUDIT.md`](AUDIT.md): Axiom checks and verification record.

## Building and checking

From inside `zero-carry-spanning-trees/`:

```sh
lake exe cache get
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

To run the full Palomar Comparator check on Linux:

```sh
bash ../.github/scripts/comparator-check.sh
```
