# Two-Adic Carry-Firewall Covers (`two-adic-carry-firewall-covers`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **87 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a reusable pure-`Init` Lean 4 compiler that turns a finite, non-uniform 2-adic prefix tree into a kernel-checked proof of a universal statement over all of $\mathbb{N}$, with a single-wire "carry firewall" that lets a depth-$d$ prefix certify more than $d$ dynamical steps.*

## For Mathematicians

Every $n \in \mathbb{N}$ embeds in the compact ring $\mathbb{Z} _ 2$. A finite full binary prefix tree `CoverTree` partitions $\mathbb{Z} _ 2$ into clopen balls $B(r, d) = \{ r + q \cdot 2^d : q \in \mathbb{N} \}$ of non-uniform depths. The package has three layers, all sorry-free and proved with the kernel only (no `native_decide`, no Mathlib):

1. **Compactness engine.** `coverTree_sound`: for any predicate $P$ and any local leaf verifier, `checkCover valid 0 0 t = true` implies $\forall n,\ P(n)$. The tree has exact Haar mass $1$ (`coverTree_haar_partition`).
2. **Reflected `Expr` compiler.** A bitwise-arithmetic AST (`+`, `*`, `^^^`, `&&&`, `|||`, `<<<`, `>>>`, `clearBit`, composition) with an exact modulus-demand function `Expr.need`: $\mathrm{eval}(e, n) \bmod 2^d$ depends only on $n \bmod 2^{\mathrm{need}(e, d)}$. Shifts left contract the demand, shifts right expand it, and the firewall rule is $\mathrm{need}(\mathrm{clearBit}(e, k), k + 1) = \mathrm{need}(e, k)$. This gives automatic infinite theorems for non-collision (`neqCover_sound`) and exact 2-adic valuation ceilings (`valCover_sound`).
3. **Carry-firewall descent.** For any 1-Lipschitz odd core $c$ with $c(x) \le s x + o$, the step $n \mapsto n / 2$ (even $n$) and $n \mapsto \mathrm{clearBit}(c(n), k) / 2$ (odd $n$) preserves full precision $k$ on odd steps, so a depth-$d$ prefix certifies $t > d$ steps. A well-founded lift (`converges_below_of_descent`) gives global convergence from finite descent above $N _ 0$.

Discharged infinite theorems (headline subset in `Challenge.lean`):

* The modified Collatz-type map $T _ k$ (odd step $n \mapsto \mathrm{clearBit}(3n + 1, k)/2$; this is **not** the Collatz map, and nothing here concerns the Collatz conjecture) converges to $\{0, 1\}$ for $k = 1, \dots, 5$ (`T5_global_convergence`: a 506-leaf depth-15 tree replaces $2^{15} = 32768$ uniform residues; the ratio $2^{15}/506 \approx 64.8$ is a leaf count, not a theorem).
* Nonlinear XOR-Collatz maps $X _ {k,c}$ (odd core $(n \oplus 2n) + c$) converge to $0$ for $(k, c) = (2, 1)$ and $(3, 3)$.
* For the Gray code $G(n) = n \oplus (n \gg 1)$: $2^{15} \nmid G(n)^2 + 3n + 60$ and $G(n)^2 + 3n + 60 \ne n \ll 15$ for all $n$ (88-leaf depth-16 tree; the ratio $2^{16}/88 \approx 744.7$ is a leaf count, not a theorem).
* **Sharp phase transition in $k$.** Contraction holds for $k \le 5$, breaks at $k = 6$ (explicit expanding orbit from $290743719$, `T6_no_drop_48`), and breaks again at $k = 8$ with a positive integer 6-cycle $975 \to 1335 \to 1875 \to 2685 \to 3900 \to 1950 \to 975$ (`T8_nontrivial_6cycle_never_drops`).
* Seven hostile certificate mutations (`neg_test_*`) are rejected by `decide`.

**Prior art.** Stopping-time and residue-tree analysis of generalized $3n + 1$ maps over $\mathbb{Z} _ 2$ goes back to Terras (1976), Everett (1977), Matthews and Watts (1984) and Lagarias (1985); 1-Lipschitz T-functions over $\mathbb{Z} _ 2$ are due to Anashin (1994) and Klimov and Shamir (2002). The single-wire carry-firewall precision-preservation law, the reusable kernel-checked cover-tree compiler for reflected bitwise expressions with exact lookahead (including right shifts), and the non-monotone $k = 5, 6, 7, 8$ transition inside the family are not recorded in the sources above, to the authors' knowledge; no search was recorded. The comparator theorems depend only on the standard axioms (see [AUDIT.md](AUDIT.md)).

**Scope of the formal statement.** $T _ k$ is the map `TCollatz k` of `Defs.lean` (odd step `clearBitNat (3n+1) k / 2`), a modified Collatz-type map; the Challenge names `T4_global_convergence` etc. refer to it, not to the Collatz map.

## For Non-Mathematicians

Imagine checking that a statement about *every* whole number is true. You cannot test infinitely many numbers, but binary numbers have a trick: the last few binary digits often decide the outcome. We split all numbers into a short list of "families" by their last few digits (some families need only 2 digits to decide, others need 15) and prove one local fact per family. Because every number belongs to exactly one family, the computer's kernel can check this short list and conclude the statement for all numbers at once.

A second trick, the "carry firewall", is to force one binary digit of an intermediate result to zero. That stops carries from smearing information upward, so a handful of digits can predict several steps of a Collatz-like game, and we can prove such games always shrink to $0$ or $1$ for some choices of the cleared wire, and fail for others (and we exhibit exactly where and why).

## Contents

| File | Role |
| :--- | :--- |
| `TwoAdicCarryFirewallCovers/Defs.lean` | `clearBitNat`, `CoverTree`, `checkCover`, `Expr`, `Expr.eval`, `firewallStep`, `iterNat`, Collatz and Gray-quadratic definitions |
| `TwoAdicCarryFirewallCovers/Theorems.lean` | Compactness meta-theorems, lookahead soundness, descent compiler, certificates, concrete theorems, sharpness and mutation tests |
| `Challenge.lean` | 8 headline statements with `sorry` (imports `Defs` only) |
| `Solution.lean` | Proofs with identical signatures, delegating to `Theorems` |
| `scripts/PrintAxioms.lean` | `#print axioms` for every comparator theorem |
| `scripts/explore_and_verify.py` | Exact-integer replays of certificates, sharpness witnesses and mutations |

## Build Instructions

```text
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
python scripts/explore_and_verify.py
```

Toolchain: `leanprover/lean4:v4.34.1`, pure `Init`, zero Mathlib. See [AUDIT.md](AUDIT.md) for the receipts.
