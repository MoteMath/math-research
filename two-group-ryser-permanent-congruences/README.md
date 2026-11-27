# Permanent Mod 2^r and Ryser-Bitmask Exact Congruence Engine (`two-group-ryser-permanent-congruences`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **7 / 10** | **10 / 10** | **80 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): bitmask Ryser formula and a 2-group orbit-collapse engine giving exact congruences of permanents modulo $2 ^ {k + 1}$ and $2 ^ {k + 2}$ for equivariant, XOR-circulant and hypercube matrices, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

We first formalize the bitmask Ryser inclusion-exclusion formula $\mathrm{perm}(A) = \mathrm{ryserSum}(A)$ over all subsets encoded as bit masks (`perm_eq_ryserSum`). We then prove a **2-group orbit-collapse** divisibility principle (`twoGroup_sum_dvd`): if a group $G$ of order $2 ^ k$ acts on a finite set $X$ and $\Delta$ is $G$-invariant with $2 ^ {s + c} \mid \Delta(x)$ whenever the stabilizer of $x$ has order $2 ^ s$, then $2 ^ {k + c} \mid \sum _ x \Delta(x)$.

Applied to the transversal-sum expansion of the permanent this gives, for any matrix equivariant under a free $2 ^ k$-group action, $\mathrm{perm}(A) \equiv \#\{\text{odd solutions}\} \pmod {2 ^ {k + 1}}$ (`perm_mod_two_pow_succ`, `xorCirc_perm_mod_two_pow_succ`), divisibility by $2 ^ {k + 1}$ for XOR-circulants with even row sum when $k \ge 3$ (`xorCirc_even_rowSum_dvd`), an explicit congruence modulo $2 ^ {k + 2}$ for odd row sum (`xorCirc_odd_mod_two_pow_add_two`), and exact laws for the hypercube $Q _ k$: $\mathrm{perm} \equiv 1 + 2 ^ k (k - 1) \pmod {2 ^ {k + 2}}$ for odd $k$, $2 ^ {k + 1} \mid \mathrm{perm}$ for even $k \ge 4$, and $2 ^ {m + 1} \mid \mathrm{perm}(I + A(Q _ m))$ for odd $m \ge 3$, where $I + A(Q _ m)$ is the $2 ^ m \times 2 ^ m$ biadjacency matrix of the hypercube $Q _ {m+1}$ (so the permanent counts perfect matchings of $Q _ {m+1}$; it equals $272 = 16 \cdot 17$ for $m = 3$).

## For Non-Mathematicians

Computing the permanent of a big matrix is believed to be extremely hard. But when a matrix is symmetric under a group of $2 ^ k$ relabelings, such as the matrix of a hypercube or one built from XOR of indices, its permanent is nearly determined by the symmetry. We prove exact congruences: the permanent leaves a known remainder when divided by $2 ^ {k + 1}$ or $2 ^ {k + 2}$, for every $k$.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `TwoGroupRyserPermanentCongruences/Theorems.lean`, definitions in `TwoGroupRyserPermanentCongruences/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `perm_eq_ryserSum` | For every $n$ and every $n \times n$ integer matrix $A$, $\mathrm{perm}(A)$ equals the Ryser bitmask inclusion-exclusion sum $\mathrm{ryserSum}(A)$. |
| `perm_mod_two_pow_succ` | If $A$ is equivariant under a free action of a $2 ^ k$-group ($k \ge 1$), then $2 ^ {k + 1}$ divides $\mathrm{perm}(A) - \#\mathrm{oddSol}(A)$. |
| `xorCirc_perm_mod_two_pow_succ` | For every $k \ge 1$ and $f$, $2 ^ {k + 1}$ divides $\mathrm{perm}$ of the XOR-circulant of $f$ minus its odd-solution count. |
| `xorCirc_even_rowSum_dvd` | For $k \ge 3$ and even total row sum, $2 ^ {k + 1}$ divides the permanent of the $2 ^ k \times 2 ^ k$ XOR-circulant. |
| `xorCirc_odd_mod_two_pow_add_two` | For $k \ge 1$ and odd row sum, $\mathrm{perm}$ of the XOR-circulant is congruent modulo $2 ^ {k + 2}$ to $1 + 2 ^ k ((\mathrm{oddCount} - 1) + \mathrm{evenSum})$. |
| `hypercubeAdj_odd_mod` | For odd $k$, the permanent of the hypercube adjacency matrix is congruent to $1 + 2 ^ k (k - 1)$ modulo $2 ^ {k + 2}$. |
| `hypercubeAdj_even_dvd` | For even $k \ge 4$, $2 ^ {k + 1}$ divides the permanent of the hypercube adjacency matrix. |
| `hypercubeMatching_even_dvd` | For odd $m \ge 3$, $2 ^ {m + 1}$ divides the permanent of `hypercubeBiadj m`, the $2 ^ m \times 2 ^ m$ matrix $I + A(Q _ m)$ (the biadjacency matrix of $Q _ {m+1}$). The name says `even` but the hypothesis is `m` odd; the name `hypercubeAdj_even_dvd` refers to even `k`. |

**Scope of the formal statement.** `hypercubeAdj k` is the XOR-circulant of the indicator of single-bit differences (the adjacency matrix of $Q _ k$); `hypercubeBiadj m` is the XOR-circulant of the indicator of $\{0\} \cup \{2^b\}$, i.e. $I + A(Q _ m)$, which is the biadjacency matrix of $Q _ {m+1}$, not of $Q _ m$.

## Proof Architecture

1. **Bitmask Ryser formula (`perm_eq_ryserSum`):** the permanent as an inclusion-exclusion sum over bit masks, proved from the definition by exact integer induction.
2. **2-group orbit collapse (`twoGroup_sum_dvd`):** orbits of a $2$-group have sizes $2 ^ {k - s}$, so invariant sums gain a factor $2 ^ k$ from the stabilizer valuations.
3. **Equivariant matrices (`perm_mod_two_pow_succ`, `xorCirc_*`, `cycCirc_*`, `antiCyc_*`):** XOR, cyclic and anti-cyclic group actions on transversals give the modulus $2 ^ {k + 1}$ and refined $2 ^ {k + 2}$ laws.
4. **Hypercube laws and sharpness (`hypercubeAdj_*`, `hypercubeMatching_*`, `sharpness_*`):** exact congruences for $Q _ k$, with kernel-checked counterexamples when equivariance, row-sum parity or the group order is changed.

## Prior-Art Context

- **Classical background:** Ryser's inclusion-exclusion formula (Ryser 1963); permanents modulo powers of two and Valiant's hardness of the permanent (Valiant 1979); Kummer-style 2-adic orbit arguments for group actions; permanents of hypercube adjacency matrices relate to counts of perfect matchings and 2-factors of $Q _ k$.
- **Novelty:** the authors did not find the 2-group Ryser orbit-collapse engine, the mod $2 ^ {k + 2}$ XOR-circulant defect law or the hypercube permanent congruences in the sources above; no search was recorded and the claim is not independently reviewed.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
