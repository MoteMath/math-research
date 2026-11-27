# Hypercube Carry-Shadow Collapse (`hypercube-carry-shadow-collapse`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a compositional guarded carry-Mealy bisimulation compiler and base-$B$ coboundary lifter discharging stateful carry-mask laws and a universal $2^m$-operand hypercube Silicon-Hadamard collapse ($Q _ m^{k+1}(x) = 2^m Q _ m^k(x)$ for all $m \ge 1$ and $k \ge 2$) plus exact `BitVec w` modular nilpotency, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Let $C(x, y) := (x + y) \oplus x \oplus y$ be the binary carry mask of addition on unbounded $\mathbb{N}$, and let $\Phi(u, v) := (u + v,\; u \oplus v)$ be the nonlinear Silicon-Hadamard butterfly. On the $2^m$ vertices of the $m$-dimensional hypercube $\{0, 1\}^m$, let $S _ r$ apply $\Phi$ across every axis-$r$ edge, set $S _ r^2 := S _ r \circ S _ r$, and define the $2^m$-operand pass operator
```math
Q_m := S_{m-1}^2 \circ \dots \circ S_1^2 \circ S_0^2 : \mathbb{N}^{2^m} \to \mathbb{N}^{2^m}.
```
We build a verified guarded carry-Mealy bisimulation compiler (`checkGuardedBisimWitness_sound`, `compile_correct`) and a base-$B$ defect-automaton coboundary lifter, and use them to prove:

1. **1-step carry-chain collapse (`phi_carry_chain_collapse`):** $C(x + y,\; x \oplus y) = 2 ((x + y) \land (x \oplus y))$ for all $x, y \in \mathbb{N}$.
2. **Exact carry-mask eigenvalue sandwich (`carryMask_eigen_sandwich_iff`):** $C(A, v) = 2v \iff (A \land 2v) \subseteq v \subseteq (A \lor 2v)$ for all $A, v \in \mathbb{N}$ (strictly stronger than $v \subseteq A$).
3. **4-operand dominated carry-absorption (`carryMask_dominated_absorption`):** whenever $b \subseteq a$, $c \subseteq a$, $d \subseteq b$, and $d \subseteq c$ bitwise, both middle operands cancel identically: $C(C(a, b),\; C(c, d)) = 2 \cdot C(a, d)$, certified in one pass by a 32-bit reachable-state mask.
4. **Universal base-$B$ carry-defect law (`baseB_carry_defect`):** for every $B \in \mathbb{Z}$ and all $x, y \in \mathbb{N}$, $\mathrm{eval} _ B(x) + \mathrm{eval} _ B(y) - \mathrm{eval} _ B(x + y) = (2 - B) \cdot \mathrm{eval} _ B(\lfloor C(x, y) / 2 \rfloor)$, unifying Kummer's popcount carry identity ($B = 1$) and alternating mod-3 digit sums ($B = -1$).
5. **Exact closed form on dominated hypercubes (`Q_closed_form_on_dom`):** on any dominated $m$-cube $y$, all $2^m - 2$ intermediate vertices cancel: $(Q _ m(y)) _ {\mathbf{0}} = 2^m y _ {\mathbf{0}}$ and $(Q _ m(y)) _ I = 2^{m-1} C(y _ {\mathbf{0}}, y _ I)$ for every $I \ne \mathbf{0}$.
6. **Universal $2^m$-operand collapse (`Q_collapse_universal`):** for every dimension $m \ge 1$, every $x \in \mathbb{N}^{2^m}$, and every $k \ge 2$ (threshold $k _ 0 = 2$ independent of $m$ and bit-width!), $Q _ m^{k+1}(x) = 2^m \cdot Q _ m^k(x)$.
7. **Universal `BitVec w` modular nilpotency (`Q_bitvec_nilpotent`):** on $w$-bit machine words $(\mathrm{BitVec}\; w)^{2^m}$, whenever $w \le m k$, $(Q _ m^{\mathrm{BV}})^{k+2}(x) = \mathbf{0}$ for every $x$.

## For Non-Mathematicians

In a computer, adding two binary numbers creates carries that can ripple unpredictably across dozens of bits, while bitwise XOR combines bits with no carries at all. Take $2^m$ whole numbers arranged at the corners of an $m$-dimensional cube and repeatedly pair up neighbors along each axis, replacing each pair $(u, v)$ by $(u + v,\; u \oplus v)$ twice per axis. Even though the individual operations are nonlinear and do not commute, after just **two** full passes over the cube the entire chaotic carry interaction freezes: every further pass simply multiplies all $2^m$ numbers by $2^m$ (a pure bit shift with zero new carries), no matter how many dimensions $m$ or how many digits the numbers have. On fixed $w$-bit registers, this forces every cube to vanish completely to zero within $\lceil w / m \rceil + 2$ passes. Every theorem is checked by Lean 4's kernel for all dimensions and all bit-widths simultaneously.

## Prior Art & Credit

- **Bitwise handbooks & Kummer's identity:** Classical references such as Warren (*Hacker's Delight*) record column-wise 2- and 3-operand identities ($x + y = (x \oplus y) + 2(x \land y)$) and Kummer's $B = 1$ popcount carry identity.
- **Automata decision procedures:** Classical Presburger/WS1S automata (Büchi, Bruyère) decide fixed-arity arithmetic formulas without a verified Lean kernel compiler or guarded carry-Mealy certificate checker.
- **What we believe is new:** the exact bi-directional carry-mask eigenvalue sandwich theorem, the 4-operand dominated carry-absorption law, the unified base-$B$ carry-defect coboundary lifter, and the unbounded-arity $2^m$-operand hypercube Silicon-Hadamard collapse ($Q _ m^{k+1} = 2^m Q _ m^k$ for all $m \ge 1, k \ge 2$) with exact `BitVec w` modular nilpotency.

## Contents

| Theorem | Module |
| :--- | :--- |
| `checkGuardedBisimWitness_sound`, `phi_carry_chain_collapse`, `carryMask_eigen_sandwich_iff`, `carryMask_dominated_absorption`, `baseB_carry_defect`, `Q_closed_form_on_dom`, `Q_collapse_universal`, `Q_bitvec_nilpotent` | `HypercubeCarryShadowCollapse.Defs` and `HypercubeCarryShadowCollapse.Theorems` |

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
python scripts/explore_and_verify.py
```

See [`AUDIT.md`](AUDIT.md) for the verbatim `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. Finite computations in `scripts/explore_and_verify.py` are illustrative replay checks only; the infinite claims are the Lean theorems.
