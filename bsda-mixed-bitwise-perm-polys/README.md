# Bit-Slice Derivative Automaton (BSDA) Mixed Permutation-Polynomial Engine Mod 2^w (`bsda-mixed-bitwise-perm-polys`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): pure-data BSDA compiler with computable BFS finite-slice horizon 3-way iff equivalence, generalized bit-by-bit masked mixed-connective Rivest theorem, exact carry-coupled congruence iff, and universal MBA/Klimov-Shamir criteria on native BitVec w, formalized in pure Lean 4 Init.*

## For Mathematicians

Classical permutation-polynomial criteria modulo $2^w$ (Rivest 2001) collapse to width $w = 2$ (mod $4$), but introducing bitwise masks (`&`, `|`), shifts (`<< k`), carries (`+`, `-`), and XOR (`^`) pushes the first collision to arbitrarily high widths $w = k+1$. We introduce the **Bit-Slice Derivative Automaton (BSDA)** engine (`MixedPermEngine`) directly on native `BitVec w`:

1. **Universal Bit-Slice Lifting & 11-Rule Differential Calculus (`bijective_iff_forall_bitDeriv`):** A truncation-coherent family $f _ w$ is bijective on $\mathrm{BitVec}\; w$ iff its bit-$i$ flip-derivative $\partial _ i f(x) = \mathrm{msb}(f _ {i+1}(\mathrm{cons}\; 1\; x)) \oplus \mathrm{msb}(f _ {i+1}(\mathrm{cons}\; 0\; x))$ equals `true` for all $i < w$ and all $x : \mathrm{BitVec}\; i$. Across all 10 silicon operators plus composition, $\partial _ i$ obeys exact Boolean laws where nonlinear multiplication collapses its bit-$(i+1)$ derivative to a 1-bit dependence on $x _ 0$.
2. **Pure-Data BSDA Compiler & Computable Finite-Slice Horizon (`bsda_bijective_iff`, `bsda_finite_slice_iff`):** `compileBSDA` compiles mixed bitwise-arithmetic expressions into a pure-data finite-state automaton `DerivAuto` (zero `Prop` fields) and computes a tight BFS reachability-stabilization horizon $W^*(D)$, yielding an **exact three-way `iff`** between $(\forall w \ge 2,\; \mathrm{Bijective}(\mathrm{eval} _ w(e)))$, kernel `decide` reflection `D.checkBijective = true`, and finite-slice bijectivity at width $W^*(D)$.
3. **Generalized Masked Mixed-Connective Rivest & Carry-Coupled `iff` Theorems (`maskedPoly_bijective_iff`, `rivest_classical_mod4_iff`, `carryPair_bijective_iff`, `addXorCancel_bijective_iff`, `klimovShamir_general_iff`):** Establishes exact bit-by-bit necessary and sufficient conditions for arbitrary masked, shifted, mixed-connective polynomials (recovering Rivest 2001 at $W^* = 2$), proves $F _ {c,d}(x) = x + (x \mathbin{\&} (x+c)) + (x \mathbin{\&} (x+d))$ is bijective mod $2^w$ iff $c \equiv d \pmod{2^w}$, and proves general MBA cancellation and Klimov–Shamir criteria for arbitrary coherent T-functions.

## For Non-Mathematicians

In cryptography and hardware hashing, you want a fast formula mixing addition, multiplication, shifts, XOR, AND, and OR that is guaranteed to be a bijection (invertible with no collisions) on **every** word size $2^w$ — 8-bit, 32-bit, 64-bit, or a million-bit words. For ordinary polynomials, checking mod $4$ is enough (Rivest 2001), but adding a single bitwise mask can make a formula invertible up to 64 bits and suddenly collide at 65 bits! We build a verified compiler in Lean 4 that translates mixed bitwise-arithmetic expressions into a finite automaton, computes the exact finite bit-width horizon $W^*$ needed to test it, and proves a 3-way equivalence: invertible at every width $\iff$ invertible at width $W^*$ $\iff$ accepted by our fast kernel checker.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of the **Bit-Slice Derivative Automaton (BSDA)** compiler and finite-slice lifting engine for mixed bitwise-arithmetic permutation polynomials modulo $2^w$.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `bijective_iff_forall_bitDeriv` | For any truncation-coherent family $f$, $f _ w$ is bijective on $\mathrm{BitVec}\; w$ iff $\partial _ i f(x) = \mathrm{true}$ for all $i < w$ and $x : \mathrm{BitVec}\; i$. |
| `bsda_bijective_iff` | For any expression `e` compiled by `compileBSDA e = some D`, `eval_w e` is bijective for all $w \ge 2$ iff `D.checkBijective = true`. |
| `bsda_finite_slice_iff` | Computable BFS finite-slice horizon: for `compileBSDA e = some D`, bijectivity for all $w \ge 2$ holds iff `eval_{W*(D)} e` is bijective at the single finite width $W^*(D)$. |
| `maskedPoly_bijective_iff` | Generalized Rivest `iff`: exact bit-by-bit parity conditions characterizing bijectivity for all $w \ge 2$ of arbitrary masked, shifted, mixed-connective ($+, -, \oplus$) polynomials. |
| `rivest_classical_mod4_iff` | Classical Rivest (2001) recovered as a corollary: an ordinary integer polynomial is bijective mod $2^w$ for all $w \ge 2$ iff it is bijective mod $4$ ($W^* = 2$). |
| `carryPair_bijective_iff` | For all $c, d \in \mathbb{Z}$ and $w \in \mathbb{N}$, $x + (x \mathbin{\&} (x+c)) + (x \mathbin{\&} (x+d))$ is bijective on $\mathrm{BitVec}\; w$ iff $c \equiv d \pmod{2^w}$. |
| `addXorCancel_bijective_iff` | For any coherent $f, g$, $(f(x) + g(x)) \oplus g(x)$ is bijective on $\mathrm{BitVec}\; w$ iff $f(x)$ is bijective on $\mathrm{BitVec}\; w$. |
| `klimovShamir_general_iff` | For any coherent $g$ and $c \in \mathbb{Z}$, $x + (g(x)^2 \mathbin{|} c)$ is bijective for all $w \ge 2$ iff $c$ is odd or $\mathrm{bit} _ 0(g(0)) = \mathrm{bit} _ 0(g(1))$. |

## Proof Architecture

1. **Coherent Bit-Slice Differential Calculus (`bijective_iff_forall_bitDeriv`):** Fiberwise MSB/truncation induction establishes the exact `iff` equivalence with $\partial _ i f = 1$ and derives closed-form Boolean laws for all 10 silicon operators plus composition.

2. **Pure-Data BSDA Compiler & BFS Horizon (`compileBSDA`, `bsda_bijective_iff`, `bsda_finite_slice_iff`):** Fuses synchronous LSB-to-MSB carry/shift transducers with nonlinear polynomial multiplication via semantic zero-derivative gating, using a finite-pigeonhole BFS to compute the tight horizon $W^*(D)$.

3. **Generalized Masked Rivest & Carry-Coupled Families (`maskedPoly_bijective_iff`, `carryPair_bijective_iff`):** Derives exact bit-by-bit necessary and sufficient conditions for masked mixed-connective polynomials and proves exact mod-$2^w$ congruence rigidity for carry-coupled pairs.

4. **Sharpness & Outside-BSDA Boundary:** Proves sharp width-$k$ survival / width-$(k+1)$ collision families (`sharpCubic_*`, `carryPair_sharp_family`) and characterizes the outside-BSDA boundary $x + (x^2 \mathbin{\&} (x \oplus 1))$ (bijective mod $4$, fails mod $8$).

## Prior-Art Context

- **Classical permutation polynomials & T-functions:** Rivest (2001) characterizes ordinary polynomials mod $2^w$ via $w = 2$ (recovered as `rivest_classical_mod4_iff`); Anashin (1994, 2002), Anashin–Khrennikov (2009), and Klimov–Shamir (2002–2004) develop 2-adic measure-preserving T-functions.
- **Mixed Boolean-Arithmetic (MBA) permutations:** Zhou–Main–Gu–Johnson (2007) and Eyrolles (2017) study MBA identities and MBA permutations mod $2^w$, closely related to the algebraic bitwise-arithmetic cancellations (`complementBridge_bijective`, `addXorCancel_bijective_iff`).
- **Contribution (prior-art status not established; no search was recorded):** The unified pure-data BSDA compiler with computable BFS finite-slice horizon 3-way `iff`, the bit-by-bit generalized masked mixed-connective Rivest theorem, and the sharp carry-coupled congruence family.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build logs and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. `scripts/explore_and_verify.py` replays the finite certificates and sharpness counterexamples in exact integer arithmetic (zero floats).
