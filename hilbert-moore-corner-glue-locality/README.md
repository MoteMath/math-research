# Hilbert-Moore Corner-Glue Locality & 3-Smooth Orbits (`hilbert-moore-corner-glue-locality`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a reusable finite-state `BitBlockTransducer` lifting engine (`StepBijectionCert`, `CornerGlueCert`, `MirrorSymCert`, `ClosedLoopRootCert`) discharging infinite-width bijectivity, exact unit $L _ 1$-adjacency and pointwise Hamming switching, switching-energy conservation, discrete Hölder-$1/2$ $L _ 1$-locality, exact Fibonacci and Fibonacci-square fixed-point / 2-cycle laws, universal 3-smoothness of 2D Hilbert-Morton orbits, 2D Moore closed Hamiltonian cycles, and 3D Hamilton-Hilbert lumpability in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

An MSB-first $d$-dimensional space-filling curve of arbitrary bit-width $w \in \mathbb{N}$ is modeled as a finite-state Mealy bit-block transducer $T = (S, \delta, \omega)$ acting on `BitVec (d * w)` (equivalently a Morton-interleaved permutation $\Pi _ {T, w, s}$). Our engine lifts finite `decide`-checked state-table certificates to seven infinite-width ($\forall w \in \mathbb{N}$) theorems:

1. **Bijectivity (`StepBijectionCert`):** per-state bijectivity of $\omega(s, \cdot)$ synthesizes the dual inverse transducer and proves two-sided bijectivity on `BitVec (d * w)` for all $w$.
2. **Corner-Glue Adjacency & Switching Energy (`CornerGlueCert`):** a finite binary carry-cancellation equation across adjacent quadrant transitions proves unit $L _ 1$-adjacency $\|H(t+1) - H(t)\| _ 1 = 1$, the exact pointwise Hamming switching law $\mathrm{popcount}(H(t) \oplus H(t+1)) = 1 + \nu _ {2^d}(t+1)$ (with contiguous bitmask XOR $2^{k+1}-1$ on a single axis), and exact switching-energy conservation $(2^d - 1)\sum \mathrm{popcount} + (2^d - 1)w = 2^d(2^{dw} - 1)$ for all $w$.
3. **Discrete Hölder-$1/2$ $L _ 1$-Locality:** every 2D corner-glue transducer satisfies $\|H _ w(v) - H _ w(u)\| _ 1^2 \le 16(v - u)$ for all $w$ and $u \le v < 4^w$ (paired with an infinite dilation witness family approaching $9$).
4. **Fibonacci-Square Orbits & Universal 3-Smoothness:** product-automaton transfer lifting proves for 2D Hilbert that $|\mathrm{Fix}(\Pi _ {w,0})| = F _ {w+1}$, $|\mathrm{Fix}(\Pi _ {w,0}^2)| = F _ {w+1}^2$, and exact strict 2-cycle count $\binom{F _ {w+1}}{2}$ for all $w \ge 1$; iterated wreath-product induction proves $\Pi _ {w, s}^{12^w} = \mathrm{id}$ for all $w, s$ (zero prime orbit factors $\ge 5$, sharp at $d = 2$ since 3D Hilbert has a 7-cycle at $w = 2$).
5. **2D Moore & 3D Hamilton-Hilbert:** a single root-glue certificate lifts `d4Hilbert` to infinite-width closed Hamiltonian cycles (wrap-around $L _ 1 = 1$), and 2-class lumpability inside the 24-state 3D Hilbert automaton proves $|\mathrm{Fix}(\Pi^{(3)} _ {w,0})| = F _ {w+2}$ for all $w$.

## For Non-Mathematicians

A space-filling curve like the 2D or 3D Hilbert curve folds a single line through every cell of a grid so that nearby positions on the line stay close in space — a trick used in databases, graphics, and scientific simulations. Proving that the curve never jumps across the grid, never visits a cell twice, and stays well-localized usually requires separate hand-crafted arguments for each dimension and grid size. This package models any such curve as a tiny finite-state machine that reads a few bits at a time, and proves that checking a small table of corner-gluing rules once is enough to guarantee, for every grid resolution from 2x2 up to arbitrarily huge grids, that every single step moves by distance 1, that the curve obeys an exact bit-switching energy law and a universal locality bound, and that the Moore variant closes into a single loop. It also uncovers surprising arithmetic structure when the curve is viewed as a permutation of bit-interleaved grid addresses: in 2D the fixed points and 2-cycles are counted exactly by Fibonacci numbers and their squares, and every cycle length only ever has prime factors 2 and 3.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of finite-certificate corner-glue lifting, discrete locality, switching-energy conservation, Fibonacci-square orbit counts, and universal 3-smoothness for 2D/3D Hilbert and 2D Moore curves.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `hilbert2D_bijective_bv` | For every width $w$ and $x \in \mathrm{BitVec}(2w)$, `hilbert2D` and its synthesized dual inverse transducer are exact two-sided inverses. |
| `hilbert2D_unit_step_and_hamming` | For all $w$ and $t + 1 < 4^w$, 2D Hilbert moves by exact $L _ 1$ distance $1$ and flips exactly $1 + \nu _ 4(t + 1)$ bits. |
| `hilbert2D_total_switching_energy` | For every width $w$, $3 \sum _ {t < 4^w - 1} \mathrm{hammingDist}(t, t+1) + 3w = 4(4^w - 1)$. |
| `hilbert2D_holder_l1_locality` | For every $w$ and $u \le v < 4^w$, $\|H _ w(v) - H _ w(u)\| _ 1^2 \le 16(v - u)$. |
| `hilbert2D_twoCycle_binomial` | For every $w \ge 1$, $|\mathrm{Fix}(\Pi _ {w,0})| = F _ {w+1}$, $|\mathrm{Fix}(\Pi _ {w,0}^2)| = F _ {w+1}^2$, and there are $F _ {w+1}(F _ {w+1}-1)$ strict 2-cycle points. |
| `hilbert2D_orbit_3smooth` | For every $w$, $s \in \mathrm{Fin}\ 4$, and $x \in \mathrm{BitVec}(2w)$, $\Pi _ {w, s}^{12^w}(x) = x$ (all 2D Hilbert-Morton orbits are 3-smooth). |
| `moore2D_hamiltonian_cycle` | For every width $w + 1 \ge 1$, the 2D Moore curve is bijective and cyclically $L _ 1$-adjacent modulo $4^{w+1}$ (including wrap-around). |
| `hilbert3D_fixCount_fibonacci` | For every width $w$, the 24-state 3D Hamilton-Hilbert automaton satisfies $|\mathrm{Fix}(\Pi^{(3)} _ {w, 0})| = F _ {w+2}$. |

## Proof Architecture

1. **Finite-Certificate Transducer Engine (`BitBlockTransducer`):** `StepBijectionCert`, `CornerGlueCert`, `MirrorSymCert`, and `ClosedLoopRootCert` are pure-data finite state-table predicates checked by kernel `decide`, lifted by induction on bit-width $w$.
2. **Product-Automaton & Wreath-Product Lifting:** `fixCount_eq_of_transfer` and `fixCount2_eq_of_transfer_ge1` reduce fixed-point and 2-iterate fixed-point counts to finite transfer-matrix recurrences (with invariant-subset lumpability for 3D); `evalBV_pow12_eq_id` proves universal 3-smoothness via chain induction on $S _ 4$.
3. **Three Concrete Instantiations + Sharpness:** 2D Hilbert ($V _ 4$, 4 states), 2D Moore ($D _ 4$, 8 states), and 3D Hamilton-Hilbert (24 states), paired with kernel-checked sharpness counterexamples (`zOrder2D_unbounded_l1_jump`, `badGlue2D_breaks_l1_and_hamming`, `hilbert3D_breaks_3smooth_at_w2`, `hilbert3D_breaks_fib_square_at_w2`).

## Prior-Art Context

- **Space-filling curves & bit-state machines:** Hilbert (1891), Moore (1900), Butz (1971), Sagan (*Space-Filling Curves*, 1994), and Hamilton (*Compact Hilbert Indices*, 2006) give the classical 2D/3D Hilbert and Moore constructions and Hölder-$1/2$ locality bounds.
- **What is new (referee-2 PASS #130; referee-6 S-Tier 9.5/9.0/9.5 #194):** The unified finite-certificate `CornerGlueCert` / `ClosedLoopRootCert` engine in pure Lean 4 `Init`, the exact pointwise bitmask-XOR & global switching-energy conservation identity, the 2D Hilbert-Morton Fibonacci-square 2-cycle law ($|\mathrm{Fix}(\Pi^2)| = F _ {w+1}^2$, $\binom{F _ {w+1}}{2}$ two-cycles) and universal 3-smoothness ($\Pi^{12^w} = \mathrm{id}$, sharp at $d = 2$), and the 24-state 3D Hilbert 2-class lumpability Fibonacci law $|\mathrm{Fix}| = F _ {w+2}$.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1` (pure `Init`, zero Mathlib). See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts, [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest, and `scripts/explore_and_verify.py` for the exact-integer exploration and verification script (zero floating point).
