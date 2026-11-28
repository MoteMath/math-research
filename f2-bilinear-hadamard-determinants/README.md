# Universal $\mathbb{F} _ 2$-Bilinear Hadamard Determinants: Integer Block Schur Elimination, the Sierpiński–Lucas–Pascal All-$n$ Law, and Conway Nimber Character Matrices

> **Hour 8 Grand Finale — 8-Hour Pure-Silicon GPU Hunt (`alien-silicon-hunt-20261128`, Track A `nim_sign_pop_0`, Score 125, `NO_EXACT_OEIS_MATCH`)**
> Zero floating-point ISA instructions on GPU (`gfx1100`); bit-identical CPU verification; 100% machine-checked in Lean 4 (`v4.34.1`) + Mathlib over **every `CommRing R`** with zero `sorry`, zero `native_decide`, and clean `#print axioms`.

## The Discovery & Universal Mechanism

In Track A of our 8-hour pure-silicon GPU hunt, the Conway nimber character matrix
```math
M_n^{\mathrm{nim}} := \Bigl((-1)^{\mathrm{popcount}(i \otimes j)}\Bigr)_{0 \le i, j < n}
```
produced a pure power-of-two leading-minor sequence (`1, -2, -4, 16, 32, -128, -512, 4096, -8192, ...`) with `NO_EXACT_OEIS_MATCH` whose consecutive ratios satisfied $|\det(M _ {k + 1}^{\mathrm{nim}}) / \det(M _ k^{\mathrm{nim}})| = 2^{\mathrm{popcount}(k)}$ for every $k$, and whose signs flipped according to the complemented Thue–Morse parity of the set bits of $k$.

Cracking the underlying algebra revealed a **completely general, division-free, ring-universal master theorem** governing **every** $\mathbb{F} _ 2$-bilinear form $B _ A(i, j) = i^T A j \in \mathbb{F} _ 2$ over **every commutative ring $R$** (including characteristic $2$!):

- **Integer Block Schur Elimination (Zero Division by $2$):** If a pivot $p < 2^d$ eliminates row $2^d$ over $\mathbb{F} _ 2$ on all columns $j < 2^d$ ($B _ A(2^d, j) = B _ A(p, j)$), then subtracting row $i' \oplus p$ from row $2^d + i'$ is a unit-lower integer row operation ($\det = 1$) that annihilates the entire $m \times 2^d$ lower-left block identically over any `CommRing R` and reduces the lower-right block to
  ```math
  (a - b) \cdot (-1)^{A_{d, d}} \cdot \mathbf{1}_{A_{d, d} \neq B_A(p, 2^d)} \cdot D_v W_m(A) D_u.
  ```
- **Universal Symmetric Law:** Whenever $A$ is symmetric and admits non-singular $\mathbb{F} _ 2$-pivots for all $d < D$, the diagonal sign matrices $D _ u = D _ v$ cancel identically ($\det(D _ u)^2 = 1$), yielding for **every** $1 \le n \le 2^D$ and **every** $a, b \in R$:
  ```math
  \det\!\bigl(\mathrm{walshCharMat}(A, n)\bigr) = \prod_{k = 0}^{n - 1} \Bigl(\mathrm{diagSign}_A(k) \cdot 2^{\mathrm{popcount}(k)}\Bigr),
  ```
  ```math
  \det\!\bigl(\mathrm{bilinCharMat}(A, a, b, n)\bigr) = a (a - b)^{n - 1} \prod_{k = 1}^{n - 1} \Bigl(\mathrm{diagSign}_A(k) \cdot 2^{\mathrm{popcount}(k) - 1}\Bigr).
  ```
- **Three Unconditional Specializations + Sharp Collapse Contrast:**
  1. **Standard Walsh–Hadamard ($A = I$, all $n \in \mathbb{N}$):** $\det(W _ n) = \prod _ {k < n} (-2)^{\mathrm{popcount}(k)}$.
  2. **Sierpiński–Lucas–Pascal ($P _ {r, s} = \binom{r + s}{r} \bmod 2 = \mathbf{1} _ {(r \mathbin{\&} s) = 0}$, all $n \in \mathbb{N}$):** Exact $\mathbb{F} _ 2$-Cholesky pivot $p _ d = \sum _ {r < d,\, (r \mathbin{\&} d) = r} 2^r$ yields $\det(W _ n(P)) = (-1)^{\lfloor n / 2 \rfloor} \cdot 2^{\sum _ {k < n} \mathrm{popcount}(k)}$ for **every** $n \in \mathbb{N}$.
  3. **Conway Nimber Character Matrices ($\mathbb{F} _ {2^8}$, all $1 \le n \le 256$):** Exact certified $\mathbb{F} _ 2$-pivots `[0, 1, 1, 2, 1, 2, 55, 110]` establish both the $\pm 1$ and $(a, b)$ determinant laws up to $256 \times 256$ (where $|\det| = 2^{1024}$).
  4. **Sharp Singularity Contrast (Carryless $\mathbb{F} _ 2[X]$ Gram Matrix):** Failure of the $\mathbb{F} _ 2$-Schur condition at $d = 1$ causes immediate total collapse $\det = 0$ for every $n \ge 3$ and every $a, b \in R$.

## Headline Theorems (9 Unconditional Theorems in `Challenge.lean` / `Solution.lean`)

1. `f2Bilin_xor_left_right` — exact $\mathbb{F} _ 2$-bilinearity in XOR and symmetry.
2. `bilinCharMat_det_block_elimination` — universal division-free block Schur elimination (both singular collapse and exact factorization) over every `CommRing R`.
3. `walshCharMat_det_symmetric` — universal symmetric $\pm 1$ Walsh determinant law for all $n \le 2^D$.
4. `bilinCharMat_det_symmetric` — universal symmetric two-parameter $(a, b)$ determinant law for all $1 \le n \le 2^D$.
5. `walshStandard_det` — all-$n$ standard Walsh–Hadamard leading-minor determinant.
6. `sierpinskiBitMat_cholesky_pivots` — exact all-$d$ $\mathbb{F} _ 2$-Cholesky pivot theorem for $P _ {r, s} = \mathbf{1} _ {(r \mathbin{\&} s) = 0}$.
7. `sierpinskiCharMat_det_all_n` — all-$n$ Sierpiński–Lucas–Pascal character determinant $(-1)^{\lfloor n / 2 \rfloor} 2^{\sum _ {k < n} \mathrm{popcount}(k)}$.
8. `nimCharMat_det_256` — exact $\pm 1$ and $(a, b)$ Conway nimber character determinant laws for all $1 \le n \le 256$.
9. `clmulBitMat_rank_collapse` — exact rank collapse $\det = 0$ for all $n \ge 3$ on the carryless $\mathbb{F} _ 2[X]$ Gram matrix.

## Verification

```powershell
lake build
lake build Challenge
lake env lean PrintAxioms.lean
```
See `AUDIT.md` for verbatim build and `#print axioms` receipts.
