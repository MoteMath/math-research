# Skew-Symmetric Thue–Morse Pfaffian Unimodularity (`skew-thue-morse-pfaffian`)

A complete, sorry-free Lean 4 / Mathlib formalization proving that the skew-symmetric Thue–Morse Hankel-sign matrices

```math
\bigl(A_n^{(s)}\bigr)_{i,j} = \mathrm{sgn}(j - i)\,(-1)^{s_2(i + j + s)} \qquad (0 \le i, j < n),
```

where $s _ 2(k)$ is the binary popcount (number of $1$-bits of $k$), are **identically unimodular** ($\det = 1$) at every even size $n = 2m$ for the three consecutive shifts $s \in \{0, 1, 2\}$, and vanish at every odd size $n = 2m + 1$ for every shift $s \in \mathbb{N}$, over **every commutative ring** $R$ (including characteristic $2$).

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `det_skewThueMorse_even` | For every commutative ring $R$ and every $m \in \mathbb{N}$, $\det(A _ {2m}^{(0)}) = 1$. |
| `det_skewThueMorse_shift1_even` | For every commutative ring $R$ and every $m \in \mathbb{N}$, $\det(A _ {2m}^{(1)}) = 1$. |
| `det_skewThueMorse_shift2_even` | For every commutative ring $R$ and every $m \in \mathbb{N}$, $\det(A _ {2m}^{(2)}) = 1$. |
| `det_skewThueMorse_odd` | For every commutative ring $R$ and all $s, m \in \mathbb{N}$, $\det(A _ {2m+1}^{(s)}) = 0$. |

Note that $s = 3$ is the exact sharpness boundary: $\det(A _ 4^{(3)}) = 9 = 3^2 \ne 1$, and in general $\det(A _ {2m}^{(s)})$ for $s \ge 3$ is a nontrivial odd square (Pfaffian square), not identically $1$.

## Proof Architecture

1. **Half-Swap Involution Schur Annihilation ($s \in \{0, 1\}$):**
   For $M = 2^p$, $N = 2M = 2^{p+1}$, and any $r \le N$, the block decomposition of $A _ {N + r}^{(s)}$ is
   ```math
   A_{N+r}^{(s)} = \begin{pmatrix} A_N^{(s)} & B \\ -B^T & -A_r^{(s)} \end{pmatrix}.
   ```
   The half-swap permutation matrix $J = \begin{pmatrix} 0 & I _ M \\ I _ M & 0 \end{pmatrix}$ satisfies $J A _ N^{(s)} J = -A _ N^{(s)}$ and $J B = -B$ (because adding $M$ flips the single bit at position $p + 1$ for $s \in \{0, 1\}$, negating $(-1)^{s _ 2}$ while preserving relative order in the cross-block $B$). Therefore, over $\mathbb{Q}$, whenever $A _ N^{(s)}$ is invertible:
   ```math
   B^T \bigl(A_N^{(s)}\bigr)^{-1} B
   = (-B^T J)\bigl(A_N^{(s)}\bigr)^{-1}(-J B)
   = B^T \bigl(J (A_N^{(s)})^{-1} J\bigr) B
   = -B^T \bigl(A_N^{(s)}\bigr)^{-1} B
   \implies B^T \bigl(A_N^{(s)}\bigr)^{-1} B = 0!
   ```
   The Schur complement collapses **identically** to $-A _ r^{(s)}$, yielding $\det(A _ {N+r}^{(s)}) = \det(A _ N^{(s)}) \det(-A _ r^{(s)}) = \det(A _ r^{(s)})$ for every even $r \le N$. Strong induction on $m$ (via $p = \lfloor \log _ 2(m - 1) \rfloor$) proves $\det(A _ {2m}^{(s)}) = 1$ for $s \in \{0, 1\}$.

2. **Explicit Null-Vector Rank-1 Bridge ($s = 2$):**
   For $s = 0$, row $0$ of $(A _ {2^{p+1}}^{(0)})^{-1}$ is explicitly $[0, 1, 1, \dots, 1]$, which implies $(A _ {2^{p+1}}^{(0)})^{-1} B$ has row $0$ equal to $[t(0), t(1), \dots, t(r - 1)]$ where $t(j) = (-1)^{s _ 2(j)}$. Strong induction constructs an exact null vector $w \in \ker(A _ {2m+1}^{(0)})$ satisfying $w _ 0 = t(m) = \pm 1$ and $w _ {2m} = 1$. Applying two unimodular congruences to the rank-1 perturbation $A _ {2m+1}^{(0)} + e _ 0 e _ 0^T$ extracts $A _ {2m}^{(2)}$ (deleting row/col $0$) on one side and $A _ {2m}^{(0)}$ (deleting row/col $2m$) on the other, giving $\det(A _ {2m}^{(2)}) = w _ 0^2 \det(A _ {2m}^{(0)}) = 1$.

3. **Characteristic-Free Ring Transfer:**
   Injectivity of $\mathbb{Z} \hookrightarrow \mathbb{Q}$ lifts the $\mathbb{Q}$-identities to $\mathbb{Z}$ (where skew-symmetry also forces $\det(A _ {2m+1}^{(s)}) = 0$), and the canonical ring homomorphism $\mathbb{Z} \to R$ transfers all four theorems to every commutative ring $R$, including rings of characteristic $2$ where skew-symmetry alone no longer implies odd-size vanishing.

## Prior-Art Context

The **symmetric** Thue–Morse Hankel matrices $H _ n(i, j) = (-1)^{s _ 2(i + j)}$ (and their $0/1$ counterparts) have a famous literature starting with Allouche, Peyrière, Wen, and Wen (1998), *Hankel determinants of the Thue–Morse sequence*, Ann. Inst. Fourier **48** (1998), 1–27, where the Hankel determinants modulo $2$ are always nonzero and over $\mathbb{Z}$ follow a rich fractal recurrence (OEIS A186026, with values $\pm 1, \pm 2, \pm 4, \dots$). By contrast, introducing the skew-symmetric factor $\mathrm{sgn}(j - i)$ produces a **Pfaffian** family whose determinant collapses identically to $1$ for every even $n = 2m$ across shifts $s \in \{0, 1, 2\}$ (and jumps to nontrivial odd squares starting at $s = 3$). A literature and OEIS search found no prior publication of this skew-symmetric Thue–Morse unimodularity phenomenon or the half-swap Schur annihilation mechanism.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
