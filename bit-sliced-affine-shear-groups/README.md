# Bit-Sliced Affine Shear-Group & Commutator Engine (BSAS-CE) (`bit-sliced-affine-shear-groups`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): 2-lane Block-r Differential Bit-Slice Affine Engine over GL_2(F_2)^w unifying add-shears, XOR-shears, cross-lane and intra-lane bit-swaps into a finite-to-infinite group homomorphism, master order-bound lifter, derived-series collapse, wreath normal form, and strict 3-level hierarchy U_w < A_w^(0) < A_w^(2) < Sym, formalized in pure Lean 4 Init.*

## For Mathematicians

We introduce the **Bit-Sliced Affine Shear-Group & Commutator Engine (`BSAS-CE`)** for reversible 2-lane silicon circuits on $(\mathrm{BitVec}\; w)^2$ built from modular add-shears, masked add-shears, XOR-shears, cross-lane bit-swaps, and block-local intra-lane swaps. The core invariant `IsBitAffine r M f` — base-block causality below bit $r$ plus differential bit-slice linearity $(f(x)) _ k \oplus (f(y)) _ k = M(k) \cdot (x _ k \oplus y _ k)$ with $M(k) \in \mathrm{GL} _ 2(\mathbb{F} _ 2) \cong S _ 3$ — turns the bit-slice Jacobian profile into a group homomorphism $\Phi _ {w, r} : \mathcal{A} _ w^{(r)} \to (\mathrm{GL} _ 2(\mathbb{F} _ 2))^{[r, w)}$ whose kernel admits one-line squaring and commutator lifts.

This single finite-to-infinite engine establishes:
1. **Master Order Bound & Derived-Series Collapse (`bsasce_master_order_bound`, `bsasce_derived_series_collapse`):** Any $f \in \mathcal{A} _ w^{(r)}$ with base-block period $D$ and $M _ f(k)^D = I _ 2$ obeys $f^{D \cdot 2^{w-r}} = \mathrm{id}$, and the $(w+1)$-th derived subgroup $(\mathcal{A} _ w^{(0)})^{(w+1)}$ collapses identically to $\mathrm{id}$ (contrast: lower central series exceeds class $w$ at $w = 4$).
2. **Exact $3 \cdot 2^w$ Saturation & Non-Conjugacy (`theorem1_circuitE_exact_order`, `theorem2_circuitP_exact_order`, `theorem2_circuitFm_pairwise_non_conjugate`):** The masked shear $E = A _ R(0) \circ A _ {L, \{0\}}$ saturates the universal $\mathcal{A} _ w^{(0)}$ ceiling at exact order $3 \cdot 2^w$ (never a commutator and not conjugate even in $\mathrm{Sym}$ to any uniform-Jacobian circuit in $\mathcal{U} _ w$), $P = S _ {\{0\}} \circ A _ R(0)$ has exact order $3 \cdot 2^{w-1}$, and the $2^w$ circuits $F _ m = S _ m \circ A _ R(0) \circ X _ L(0)$ are pairwise non-conjugate in $\mathcal{A} _ w^{(0)}$.
3. **Add-XOR Commutator Tower & Wreath Normal Form (`theorem3_addXorShear_exact_order`, `theorem3_fiber1_wreath_normal_form`):** Both $A _ R(0) \circ X _ R(0)$ and $[A _ R(0), X _ R(0)]$ have exact order $2^{w-1}$, and the fiber-$1$ group $\langle +1, \oplus 1 \rangle$ is in exact canonical bijection with $C _ {2^{w-1}} \wr C _ 2$ of cardinality $2^{2w-1}$.
4. **Block-2 Prime-5 Symmetry-Breaking (`theorem4_circuitH_prime5_obstruction`):** Adding a single intra-lane bit-swap $B _ {0, 1}$ introduces prime factor $5$ ($H^{3 \cdot 2^w}(0, 1) \ne (0, 1)$ for all $w \ge 2$), proving the strict 3-level hierarchy $\mathcal{U} _ w \subsetneq \mathcal{A} _ w^{(0)} \subsetneq \mathcal{A} _ w^{(2)} \subsetneq \mathrm{Sym}((\mathrm{BitVec}\; w)^2)$.

## For Non-Mathematicians

Reversible binary circuits built from modular additions, XORs, and bit-swaps form enormous permutation groups of size $(2^{2w})!$. Even though binary carries couple every bit non-linearly, taking the XOR difference of two inputs that agree on lower bits cancels the carry cleanly, exposing a tiny $6$-element linear group $\mathrm{GL} _ 2(\mathbb{F} _ 2)$ at every bit slice. Using this finite-to-infinite lens, we prove exact formulas for circuit orders at **every** bit width $w \ge 2$, show that $2^w$ simple 3-gate circuits all live in distinct conjugacy classes, prove that repeated commutators collapse completely in $w+1$ steps, and demonstrate a sharp structural jump: a single swap of bits $0$ and $1$ immediately breaks out of the $2^a 3^b$ universe by introducing prime factor $5$.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of the **Bit-Sliced Affine Shear-Group & Commutator Engine (`BSAS-CE`)**, proving master order bounds, derived-series collapse, exact circuit orders, $2^w$ conjugacy classes, wreath normal forms, and the strict 3-level hierarchy $\mathcal{U} _ w \subsetneq \mathcal{A} _ w^{(0)} \subsetneq \mathcal{A} _ w^{(2)} \subsetneq \mathrm{Sym}$.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `bsasce_master_order_bound` | For any $f \in \mathcal{A} _ w^{(r)}$ ($w \ge r$) with base-block period $D$ and $M _ f(k)^D = I _ 2$ for $k \in [r, w)$, $f^{D \cdot 2^{w-r}}(x) = x$ for all $x \in (\mathrm{BitVec}\; w)^2$. |
| `bsasce_derived_series_collapse` | For every $w \ge 1$, every circuit in the $(w+1)$-th derived subgroup $(\mathcal{A} _ w^{(0)})^{(w+1)}$ is identically the identity map. |
| `theorem1_circuitE_exact_order` | For every $w \ge 2$, the masked add-shear $E = A _ R(0) \circ A _ {L, \{0\}}$ has exact order $3 \cdot 2^w$, saturating the universal $\mathcal{A} _ w^{(0)}$ ceiling. |
| `theorem2_circuitP_exact_order` | For every $w \ge 2$, the bit-0 cross-swap shear $P = S _ {\{0\}} \circ A _ R(0)$ has exact order $3 \cdot 2^{w-1}$. |
| `theorem2_circuitFm_pairwise_non_conjugate` | For every $w \ge 1$ and all $m _ 1 \ne m _ 2 \in \mathrm{BitVec}\; w$, the 3-gate circuits $F _ {m _ 1}, F _ {m _ 2}$ are pairwise non-conjugate in $\mathcal{A} _ w^{(0)}$ ($2^w$ distinct classes). |
| `theorem3_addXorShear_exact_order` | For every $w \ge 2$, the add-XOR shear $A _ R(0) \circ X _ R(0)$ has exact order $2^{w-1}$. |
| `theorem3_fiber1_wreath_normal_form` | For every $w \ge 2$, the fiber-$1$ group $\langle +1, \oplus 1 \rangle$ is in exact canonical bijection with $\mathrm{Bool} \times (\mathrm{BitVec}\; (w-1))^2 \cong C _ {2^{w-1}} \wr C _ 2$ (size $2^{2w-1}$). |
| `theorem4_circuitH_prime5_obstruction` | For every $w \ge 2$, the block-2 swap circuit $H = B _ {0, 1} \circ A _ R(0) \circ X _ L(0)$ satisfies $H^{3 \cdot 2^w}(0, 1) \ne (0, 1)$, separating $\mathcal{A} _ w^{(2)}$ from $\mathcal{A} _ w^{(0)}$ even in $\mathrm{Sym}$. |

## Proof Architecture

1. **Differential Bit-Slice Homomorphism (`IsBitAffine`, `bsasce_master_order_bound`):** XOR-differencing inputs that agree below bit $k$ cancels modular carries identically (`add_bit_diff`), yielding a group homomorphism $\Phi _ {w, r} : \mathcal{A} _ w^{(r)} \to (\mathrm{GL} _ 2(\mathbb{F} _ 2))^{[r, w)}$ and a one-line kernel squaring lift ($f \in \mathcal{K} _ s \implies f^2 \in \mathcal{K} _ {s+1}$).

2. **Derived-Series & Commutator Filtration (`bsasce_derived_series_collapse`):** Because $[\mathrm{GL} _ 2(\mathbb{F} _ 2), \mathrm{GL} _ 2(\mathbb{F} _ 2)] = A _ 3$ is abelian, double commutators land in $\mathcal{K} _ 1$, and iterative commutator lifting drives $(\mathcal{A} _ w^{(0)})^{(w+1)}$ to $\{\mathrm{id}\}$.

3. **Closed-Form Orbits & Wreath Normal Form (`theorem1_*`, `theorem2_*`, `theorem3_*`):** Explicit orbit invariants prove exact lower bounds matching the `BSAS-CE` upper bounds, establish $2^w$ conjugacy classes via Jacobian profiles, and construct the exact bijection with $C _ {2^{w-1}} \wr C _ 2$.

4. **Block-2 Symmetry-Breaking & Sharpness (`theorem4_circuitH_prime5_obstruction`):** Lifting a 16-state base table at $r = 2, D = 15$ proves $H^{15 \cdot 2^{w-2}} = \mathrm{id}$ while its prime-5 factor separates $\mathcal{A} _ w^{(2)}$ from $\mathcal{A} _ w^{(0)}$ even in $\mathrm{Sym}$, alongside a kernel-checked witness showing the lower central series exceeds class $w$ at $w = 4$.

## Prior-Art Context

- **1-lane T-functions & classical wreath products:** Klimov–Shamir (2002, 2004) and Anashin–Khrennikov (2009) study 1-lane T-functions via Mahler/van der Put coefficients, and $\langle +1, \oplus 1 \rangle \cong C _ {2^{w-1}} \wr C _ 2$ is a classical wreath product (formalized here with exact bijective normal form on fiber $a = 1$).
- **Novel contribution:** The 2-lane Block-$r$ Differential Bit-Slice Affine Engine `IsBitAffine r M f` over $\mathrm{GL} _ 2(\mathbb{F} _ 2)^w$, unifying add/XOR/masked shears and cross-/intra-lane bit-swaps into one finite-to-infinite homomorphism, conjugacy-profile invariant, derived-series collapse, and strict 3-level $\mathrm{Sym}$-conjugacy hierarchy $\mathcal{U} _ w \subsetneq \mathcal{A} _ w^{(0)} \subsetneq \mathcal{A} _ w^{(2)} \subsetneq \mathrm{Sym}$.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build logs and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. `scripts/explore_and_verify.py` replays the finite certificates and sharpness counterexamples in exact integer arithmetic (zero floats).
