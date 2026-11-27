# Exact Carry-Presburger Residue-Transition Elimination & Skolem Compiler (CPRTE) (`carry-presburger-skolem-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): reusable pure-data Carry-Presburger reflection compiler and executable 2-pass Skolem transducer in Lean 4 Init unifying linear arithmetic, arbitrary-modulus congruences, 4-way bitwise relations, exact carry counts (Kummer defect), and modular popcount sums, discharging 20 theorem statements (universally quantified over the inputs, plus finite sharpness and mutation-rejection checks) including the bounded-carry ternary completion phase transition.*

## For Mathematicians

We build **Exact Carry-Presburger Residue-Transition Elimination (CPRTE)**, a standalone pure-Init Lean 4 reflection compiler that lifts finite pure-data residue-carry transition certificates (`Cert`, zero `Prop` fields) to universally quantified ($\forall \vec{x} \in \mathbb{N}^d$) and alternating ($\forall \vec{x} \in \mathbb{N}^d,\; \exists \vec{y} \in \mathbb{N}^e$) theorems mixing six atomic families under full Boolean connectives: linear inequalities/equalities, arbitrary-modulus congruences ($m \ge 1$), 4-way pointwise bitwise relations (`&`, `|`, `^`, disjointness, carry-word masks), exact binary carry-count bounds $\kappa(a, b, \gamma) \le K$ (proved equal to Kummer's popcount defect `carryCount_eq_popcount_defect`), and modular linear combinations of binary popcounts.

Under LSB-first bit-peeling, every atom admits an exact symbolic carry-residue derivative (`stepFormula`), and existential projection distributes across finite witness bit-sets inside the AST. Strong induction on $\sum x _ k$ yields three general soundness meta-theorems (`cert_sound`, `synthesizeY_sound`, `cert_sound_univ`), including an **executable 2-pass constructive Skolem transducer** `synthesizeY`. The compiler discharges 20 arithmetic-bitwise theorem statements (some of them finite sharpness checks) via kernel `decide` (zero `native_decide`), notably:
1. **Bounded-Carry Ternary Completion Phase Transition (`ternary_zero_carry_r0`, `ternary_carry1_r2`, `ternary_carry2_r0`):** Optimal asymptotic slope $\alpha(K, r)$ for $\kappa(x, y) \le K \land (x+y) \equiv r \pmod 3$ exhibits a double parity-inversion phase transition: at $K=0$ slopes are $(5/3, 5/3, 2)$; at $K=1$, $r=2$ collapses $4\times$ to $(1, 1, 1/2)$; at $K=2$, $r=0,1$ drop to $1/4$ while $r=2$ stays blocked at $1/2$ — with matching extremal lower bounds proved in the library (`Challenge.lean` states the upper-bound witnesses `ternary_*`).
2. **Mersenne-Collatz Affine Zero-Carry Rigidity (`mersenne_collatz_rigidity_15`):** For $a \in \{3, 7, 15\}$ and all $x \in \mathbb{N}$, $x \mathbin{\&} (ax+1) = 0 \iff (ax+1) \mathbin{\&} (ax) = 0$ (sharp: fails at non-Mersenne $a = 5$).

## For Non-Mathematicians

Standard automated arithmetic solvers like Lean's `omega` can reason about linear inequalities ($3y \le 5x + 5$), but break down the moment you mix them with bitwise operations (`&`, `^`), binary carries, and popcounts. We build a self-verifying Lean 4 proof compiler that peels off numbers one bit at a time from the least significant bit, tracks finite carry-and-remainder states, and even synthesizes an executable program that constructs the witness $y$ for any input $x$. Using this compiler, we prove a surprising phase transition for adding a number $y$ to $x$ with at most $K$ binary carries to hit a target remainder mod $3$: allowing $1$ carry makes remainder $2$ four times easier, while allowing $2$ carries makes remainders $0$ and $1$ easier than remainder $2$ again!

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of **CPRTE** (Exact Carry-Presburger Residue-Transition Elimination), combining a pure-data finite-certificate reflection engine, an executable 2-pass Skolem transducer, and 20 discharged arithmetic-bitwise theorem statements (the universally quantified ones plus finite sharpness items).

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `cert_sound` | General existential soundness meta-theorem: if `checkCert cert = true`, then $\forall \vec{x} \in \mathbb{N}^d,\; \exists \vec{y} \in \mathbb{N}^e,\; \Phi _ 0(\vec{x}, \vec{y})$. |
| `synthesizeY_sound` | Executable 2-pass Skolem transducer soundness: `synthesizeY cert x` constructs a valid witness $\vec{y}$ satisfying $\Phi _ 0(\vec{x}, \vec{y})$ for every $\vec{x} \in \mathbb{N}^d$. |
| `cert_sound_univ` | Universal soundness meta-theorem ($e = 0$): if `checkCert cert = true`, then $\forall \vec{x} \in \mathbb{N}^d,\; \Phi _ 0(\vec{x})$. |
| `carryCount_eq_popcount_defect` | Kummer's popcount defect bridge: $\kappa(a, b, \gamma) + s _ 2(a + b + \gamma) = s _ 2(a) + s _ 2(b) + \gamma$ for all $a, b \in \mathbb{N}$ and carry-in $\gamma$. |
| `ternary_zero_carry_r0` | For all $x \in \mathbb{N}$, there exists $y \in \mathbb{N}$ with $x \mathbin{\&} y = 0$, $3 \mid (x+y)$, and bound $3y \le 5x + 5$. |
| `ternary_carry1_r2` | At carry budget $K = 1, r = 2$: for all $x \in \mathbb{N}$, there exists $y$ with $\kappa(x, y) \le 1$, $(x+y) \equiv 2 \pmod 3$, and $2y \le x + 4$ ($4\times$ slope collapse). |
| `ternary_carry2_r0` | At carry budget $K = 2, r = 0$: for all $x \in \mathbb{N}$, there exists $y$ with $\kappa(x, y) \le 2$, $3 \mid (x+y)$, and $4y \le x + 7$ (parity-inversion phase transition). |
| `mersenne_collatz_rigidity_15` | Mersenne-Collatz zero-carry rigidity: for all $x \in \mathbb{N}$, $x \mathbin{\&} (15x+1) = 0 \iff (15x+1) \mathbin{\&} (15x) = 0$. |

## Proof Architecture

1. **6-Family Carry-Presburger AST & Symbolic Derivative (`stepFormula`):** Unifies linear inequalities/equalities, arbitrary-modulus congruences, 4-way bitwise truth tables, exact carry counts (bridged to Kummer's defect), and modular popcount sums under exact LSB-first bit-peeling.

2. **Pure-Data Certificate & Syntactic Entailment (`checkCert`, `entails_sound`):** Zero-`Prop` finite state tables verified by kernel `decide` (zero `native_decide`) check base satisfiability at $\vec{x} = \vec{0}$ and transition closure via sound syntactic entailment.

3. **Constructive 2-Pass Skolem Transducer (`synthesizeY_sound`, `cert_sound`):** Strong induction on $\sum x _ k$ turns any verified existential certificate into an executable Skolem function supporting unbounded bit-lookahead via formula-level disjunctive determinization.

4. **Sharpness & Mutation Rejection:** Discharges 20 theorem statements across 4 families (all 9 ternary carry-budget bounds + 4 matching extremal lower bounds + Mersenne-Collatz rigidity + carry-parity laws), backed by 9 sharpness counterexamples and 6 kernel-checked hostile certificate rejections.

## Prior-Art Context

- **Presburger & Büchi–Bruyère arithmetic:** Classical Presburger (1929) and Büchi–Bruyère arithmetic characterize automatic sets in base $2$, and Lean's built-in `omega` handles linear integer arithmetic only.
- **Contribution claimed here (not independently reviewed; no prior-art search was recorded):** CPRTE is a self-contained, kernel-verified Lean 4 reflection compiler mixing linear arithmetic, arbitrary-modulus congruences, 4-way bitwise relations, exact bounded carry counts, and modular popcount sums with an executable 2-pass Skolem transducer, discovering and certifying the bounded-carry ternary completion phase transition and Mersenne-Collatz rigidity.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build logs and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. `scripts/explore_and_verify.py` replays the finite certificates and sharpness counterexamples in exact integer arithmetic (zero floats).
