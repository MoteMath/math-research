# Feistel Aff(F_2^2) Monodromy Locks & Universal 2^a 3^b Spectra (`feistel-aff2-monodromy-locks`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): bit-slice Aff(F_2^2)-monodromy tower engine proving every triangular XOR-Feistel network has periods strictly 2^a 3^b across all widths w, plus universal period-12 locks, sharp R+1 vs R-1 dichotomy, binomial 3^w spectrum with ctz(tau) phase transition, and universal 2^(w+1) isoperiodicity, formalized in pure Lean 4 Init.*

## For Mathematicians

For any balanced XOR-Feistel network $F _ w(L, R) = (R, L \oplus f _ w(R))$ on $(\mathrm{BitVec}\; w)^2$ whose round function family $\{f _ w\}$ is triangular (2-adic 1-Lipschitz), we formalize the **Bit-Slice $\mathrm{Aff}(\mathbb{F} _ 2^2)$-Monodromy Tower Engine** (`FeistelMonodromy`). Because top-bit evolution factors through the 24-element affine group $\mathrm{Aff}(\mathbb{F} _ 2^2) \cong S _ 4$ (whose cycle lengths lie in $\{1, 2, 3, 4\}$), every state at every bit-width $w$ has exact minimal period $2^a 3^b$ (`feistel_universal_2_3_period`). Finite cancellation identities inside $\mathrm{Aff}(\mathbb{F} _ 2^2)$ lift to four universal infinite-width theorems across eight concrete hardware circuits (`R+1`, `R-1`, `R|(R±1)`, `R^(R±1)`, `R&(-R)`, `R&~(R+1)`):

1. **Universal Trigger-Independent Period-12 Lock (`theorem_I_universal_period12_lock`):** For every 2-adic trigger stream $\tau$, Rule-$(1,0,0,1)$ locks globally to period $12$ (covering both $R \mathbin{|} (R+1)$ and $R \mathbin{|} (R-1)$ for all $w \ge 1$).
2. **Sharp `+1` Period-6 Lock vs `-1` Exponential Escape (`theorem_IIa_add_one_period6_lock`, `theorem_IIb_sub_one_exponential_escape`):** $R+1$ locks universally to period $6$, whereas replacing $+1$ by $-1$ shatters the lock so $(0, 0)$ has exact minimal period $3 \cdot 2^{w-1}$ for all $w \ge 1$.
3. **Exact Binomial Power-of-3 Spectrum & $\mathrm{ctz}(\tau)$ Phase Transition (`theorem_IIIa_lsb_binomial_spectrum`, `theorem_IIIb_ctz_period_lock`):** For $R \mathbin{\&} (-R)$, exactly $\binom{w}{j} 3^j$ states have exact minimal period $3^j$ (maximum $3^w$), whereas any trigger $\tau$ with first `true` bit at $m$ collapses universally to constant global period $2 \cdot 3^{m+1}$ (locking $R \mathbin{\&} \sim(R+1)$ to period $6$).
4. **Universal Isoperiodic $2^{w+1}$ Law (`theorem_IV_universal_isoperiodic`):** Rule-$(0,0,0,1)$ (including $R \oplus (R+1)$ and $R \oplus (R-1)$) satisfies universal exact period bounds across all $w \ge 1$.

## For Non-Mathematicians

Feistel networks are the workhorse structure behind modern block ciphers: split a register into left and right halves $(L, R)$ and update $(L, R) \to (R, L \oplus f(R))$. We prove that whenever $f$ is built from standard binary hardware operations (addition, subtraction, AND, OR, XOR, NOT, left-shifts), the period of **every** state at **every** bit width $w$ can only ever be a product of powers of $2$ and $3$ ($2^a 3^b$) — no prime factor $5, 7, 11, \dots$ can ever appear! Even more strikingly, tiny sign flips trigger sharp phase transitions: $R+1$ snaps every state back in at most $6$ steps regardless of bit width, while $R-1$ explodes to period $3 \cdot 2^{w-1}$; $R \mathbin{\&} (-R)$ produces an exact Pascal-triangle spectrum of periods $3^j$, while $R \mathbin{\&} \sim(R+1)$ collapses to period $6$ forever.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of the **Bit-Slice $\mathrm{Aff}(\mathbb{F} _ 2^2)$-Monodromy Tower Engine**, proving the universal $2^a 3^b$ period law for all triangular XOR-Feistel networks and four infinite-width hardware period-lock and phase-transition theorems.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `feistel_universal_2_3_period` | For every `TriangularRoundFn` $f$, bit-width $w \in \mathbb{N}$, and state $s \in (\mathrm{BitVec}\; w)^2$, $s$ has exact minimal period $2^a 3^b$ ($a \le 2w, b \le w$). |
| `theorem_I_universal_period12_lock` | For every 2-adic trigger stream $\tau$ and $w \ge 1$, Rule-$(1,0,0,1)$ Feistel locks universally to period $12$ (every state has exact period $4$ or $12$). |
| `theorem_IIa_add_one_period6_lock` | For every $w \ge 1$ and $(L, R) \in (\mathrm{BitVec}\; w)^2$, $(L, R) \mapsto (R, L \oplus (R+1))$ has exact minimal period in $\{1, 3, 6\}$ and satisfies $F _ w^6(L, R) = (L, R)$. |
| `theorem_IIb_sub_one_exponential_escape` | For every $w \ge 1$, $(0, 0)$ under $(L, R) \mapsto (R, L \oplus (R-1))$ has exact minimal period $3 \cdot 2^{w-1}$. |
| `theorem_IIIa_lsb_binomial_spectrum` | For every $w, j \in \mathbb{N}$, $(L, R) \mapsto (R, L \oplus (R \mathbin{\&} (-R)))$ has exactly $\binom{w}{j} 3^j$ states of exact minimal period $3^j$ and maximum period $3^w$. |
| `theorem_IIIb_ctz_period_lock` | If trigger stream $\tau$ has its first `true` bit at index $m$, Rule-$(0,0,1,0)$ Feistel locks universally to constant period $2 \cdot 3^{m+1}$ for all $w \ge 1$. |
| `theorem_IV_universal_isoperiodic` | Universal isoperiodic law for Rule-$(0,0,0,1)$ Feistel (covering $R \oplus (R+1)$ and $R \oplus (R-1)$) across all $w \ge 1$. |

## Proof Architecture

1. **Truncation Semiconjugacy & Top-Bit Monodromy (`feistelIter_truncate`, `feistelIter_topBit`):** Every triangular round function lifts from width $k$ to $k+1$ via an affine monodromy product $\Phi _ k(s, p) \in \mathrm{Aff}(\mathbb{F} _ 2^2) \cong S _ 4$.

2. **Universal $2^a 3^b$ Period Lift (`feistel_period_lift`, `feistel_universal_2_3_period`):** Since every element of $\mathrm{Aff}(\mathbb{F} _ 2^2)$ has orbit lengths in $\{1, 2, 3, 4\}$, induction on $w$ forces every exact minimal period to be of the form $2^a 3^b$.

3. **Finite-Group Cancellation Certificates & Hardware Bridges:** Kernel-checked identities in $\mathrm{Aff}(\mathbb{F} _ 2^2)$ prove hit-pairing cancellation (period 12), carry cancellation (period 6), `ctz` even-hit cancellation ($2 \cdot 3^{m+1}$), and double-hit shift ($3 \cdot 2^{w-1}$), bridged bit-for-bit to eight concrete `BitVec w` hardware circuits.

4. **Non-Vacuity & Sharpness:** Five non-vacuity witnesses and four sharpness theorems (`R|(R+3)` period 36, `R&(R-1)` period 16, `R^(R+2)` period 4, non-triangular `R+(R>>1)` prime period 5) confirm every hypothesis is tight.

## Prior-Art Context

- **Classical Feistel & T-function literature:** Luby–Rackoff (1988) and Patarin study cryptographic security of Feistel networks over random round functions, while Klimov–Shamir (2002, 2004) and Anashin–Khrennikov (2009) study 1-lane T-functions.
- **Distinct from `binary-lyness-periods`:** While `binary-lyness-periods` proves period-6/12 laws for $y + 2^r$ and $y \mathbin{|} (y + 2^r)$ on unbounded $\mathbb{N}^2$, `FeistelMonodromy` establishes the general $\mathrm{Aff}(\mathbb{F} _ 2^2)$ monodromy tower for all triangular round functions on $(\mathrm{BitVec}\; w)^2$, the universal $2^a 3^b$ period law, the sharp $R+1$ vs $R-1$ dichotomy, the exact $\binom{w}{j} 3^j$ binomial spectrum for $R \mathbin{\&} (-R)$, and the $\mathrm{ctz}(\tau)$ phase transition.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build logs and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest. `scripts/explore_and_verify.py` replays the finite certificates and sharpness counterexamples in exact integer arithmetic (zero floats).
