# Reversible Toffoli and Fredkin Gate-Lattice Conservation Engine (`reversible-gate-lattice-flux`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): pure-kernel finite-window continuity certificate compiler (`FluxCert`) lifting generically to open segments on $\mathbb{Z} \to \mathbb{B}$ and arbitrary-width periodic rings, with a complete 256-gate 4-way ideal-mask classification for cubic non-Hamming charge conservation and all-width conservation laws for Fredkin-Toffoli, Double-Fredkin, and chiral SubCNOT reversible lattices, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

A local discrete continuity equation $q(\text{next}(u)) - q(u _ {\mathrm{out}}) = J(u _ {\mathrm{right}}) - J(u _ {\mathrm{left}})$ on an $M$-bit window is packaged as a zero-`Prop` pure-data record `FluxCert p r s M shiftOut`. Checking `c.verify = true` by kernel reduction over all $2 ^ M$ windows compiles generically via `FluxCert.open_segment_continuity` and `FluxCert.ring_conserved_iter` into exact Gauss-Noether charge-flux continuity on every open segment $[a, a + n)$ of every infinite bit-line $\mathbb{Z} \to \mathbb{B}$ and exact all-iteration conservation on every periodic ring $\mathrm{BitVec}\; (p \cdot n)$ ($n \ge 1$), closed under $\mathbb{Z}$-linear combinations (`linComb_verify`).

We instantiate the engine across two reversible brickwork topologies (`Margolus4` and `SubCNOT`): a complete **256-gate 4-way `iff` classification** (`fredkin_cnot_iff_1_2` and `fredkin_cnot_classification_*`) proving that a 3-variable mask $h$ is ideal (the Boolean condition $h(a,c,d) \Rightarrow a \wedge (c \vee d)$, `IdealMask`) if and only if the finite `FluxCert` `certFredCNOT h` (fixed charge $q _ {\mathrm{FT}}$ and flux $J _ {\mathrm{FT}}$) passes (the 3-test-vector width-8 completeness is in `Theorems.lean`, not in `Challenge.lean`), exact all-width conservation and reversibility of the **Fredkin-Toffoli** lattice, a 3D **Double-Fredkin** charge algebra (Hamming weight, dimer, rail, and asymmetric charges), a cubic-flux Dual-Fredkin law, and non-Rule-54 **chiral SubCNOT** domain-wall conservation.

## For Non-Mathematicians

Imagine a ring of bits updated simultaneously by tiled reversible logic gates (like Fredkin controlled-swaps and Toffoli gates). Even though bits flip and interact across the whole ring, certain subtle multi-bit patterns—not just the count of 1s—can remain strictly conserved forever. We prove that a single finite local check on a small window of bits automatically guarantees exact conservation on rings of every size (and on infinite lines), classify all 256 gate variants in a Fredkin-CNOT family, and prove exact conservation for four distinct reversible gate lattices.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `ReversibleGateLatticeFlux/Theorems.lean`, definitions in `ReversibleGateLatticeFlux/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `fluxCert_verify_sound` | If a finite `FluxCert` passes `c.verify = true`, then the exact discrete charge-flux continuity identity holds on every $M$-bit window $u : \mathrm{BitVec}\; M$. |
| `fluxCert_open_segment_continuity` | A passing `FluxCert` lifts to exact Gauss-Noether continuity: the one-step change of charge on any open segment $[a, a + n)$ of any infinite line $\mathbb{Z} \to \mathbb{B}$ equals the boundary flux difference. |
| `fluxCert_ring_conserved_iter` | A passing `FluxCert` proves exact conservation of the total ring charge under arbitrarily many steps $t$ on every ring $\mathrm{BitVec}\; (p \cdot n)$ ($n \ge 1$). |
| `fredkin_cnot_iff_1_2` | For every 3-variable Boolean mask $h$, `IdealMask h` (the Boolean condition $h(a,c,d) \Rightarrow a \wedge (c \vee d)$) holds if and only if the finite `FluxCert` `certFredCNOT h` (with the fixed charge $q _ {\mathrm{FT}}$ and flux $J _ {\mathrm{FT}}$) passes. This is an equivalence between a Boolean condition on the mask and a finite certificate check; 256 cases in total, 8 of them ideal. |
| `fredkin_toffoli_conserved_all_widths` | The Fredkin-Toffoli Margolus lattice conserves the cubic non-Hamming charge $q _ {\mathrm{FT}}$ for all iterations $t$ on every $4 n$-bit ring. |
| `fredkin_toffoli_reversible_all_widths` | The Fredkin-Toffoli Margolus step and its explicit inverse form an exact bijection on every $4 n$-bit ring. |
| `double_fredkin_three_laws_all_widths` | The Double-Fredkin lattice simultaneously conserves Hamming weight $q _ {\mathrm{HW4}}$, dimer charge $q _ {\mathrm{dimer}}$, rail charge $q _ {\mathrm{rail}}$, and the asymmetric charge at every width $4 n$. |
| `subcnot_chiral_domain_wall_conserved_all_widths` | The chiral SubCNOT lattice conserves the domain-wall charge $q _ {\mathrm{DW}}$ for all iterations $t$ on every $2 n$-bit ring. |

## Proof Architecture

1. **Zero-`Prop` continuity compiler (`FluxCert.verify_sound`):** exhaustively verifies the local continuity identity over `BitVec M` in kernel reduction without `native_decide`.
2. **5-level infinite lifting (`open_segment_continuity`, `infinite_line_conserved`, `periodic_conserved_iter`, `ring_conserved_iter`, `linComb_verify`):** telescopes the local flux across arbitrary open segments, infinite lines, periodic rings, and $\mathbb{Z}$-linear charge combinations.
3. **256-gate classification (`fredkin_cnot_iff_1_2`, `fredkin_cnot_classification_*`):** characterizes all 256 3-variable masks via `IdealMask h` and proves 3-vector width-8 completeness.
4. **Multi-topology instantiations (`margolusStep`, `subCNOTStep`):** proves exact reversibility and conservation for Fredkin-Toffoli, Double-Fredkin, Dual-Fredkin, and chiral SubCNOT lattices, paired with kernel-checked non-HW witnesses and mutation rejections.

## Prior-Art Context

- **Classical reversible CA & conservation-law lineage:** Fredkin & Toffoli (*Conservative Logic*, IJTP 1982), Margolus (*Physics-like models of computation*, Physica D 1984), Hattori & Takesue (*Additive conserved quantities in discrete-time lattice dynamical systems*, Physica D 1991), Takesue (1995), Boccara & Fukś (1998), Rule 54 (explicitly separated from our SubCNOT laws), and Gombor & Pozsgay (2021) on superintegrable brickwork cellular automata.
- **Claimed contribution (not independently reviewed):** the zero-`Prop` 5-level `FluxCert` continuity compiler across `Margolus4` and `SubCNOT`, the 256-gate 4-way `iff` and 3-vector width-8 completeness for the cubic non-Hamming charge $q _ {\mathrm{FT}}$, the 3D Double-Fredkin charge algebra, cubic-flux Dual-Fredkin, and non-Rule-54 chiral SubCNOT laws. No prior record was found by the authors; the search was not recorded.

## Scope of the formal statement

The lattices are the hand-written Margolus and SubCNOT brickwork steps in `Defs.lean` acting on `BitVec`; the charges, fluxes and the `IdealMask` condition are defined there. The theorems are about these definitions. The Fredkin-Toffoli, Double-Fredkin and SubCNOT conservation laws are universal in the ring width; the `iff` is a finite 256-case classification.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
