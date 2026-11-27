# Carry-Defect Weight Spectra of Constant Multiplication (`carry-defect-weight-spectra`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **10 / 10** | **9 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **90 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): exact Hamming-weight spectra $\mathcal{W}(c)$ of the defect between carried integer multiplication and carry-less polynomial multiplication, including a complete classification for $c \equiv 1 \pmod 4$, the Mersenne gap law $\mathcal{W}(2 ^ m - 1) = \mathbb{N} \setminus \{1\}$, and a finite certificate compiler, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

For a multiplier $c$ and input $x$ define the carry defect $\Delta(c, x) = (c x) \oplus \mathrm{clmul}(c, x)$ between integer multiplication and carry-less multiplication in $\mathbb{F} _ 2 [x]$, its weight $W _ c (x) = \mathrm{popcount}(\Delta(c, x))$ and the spectrum $\mathcal{W}(c) = \{ W _ c (x) : x \in \mathbb{N} \}$. We prove: $\mathcal{W}(c) = \mathbb{N}$ for every $c \ge 5$ with $c \equiv 1 \pmod 4$; $\mathcal{W}(2 ^ m - 1) = \mathbb{N} \setminus \{1\}$ for every $m \ge 2$, together with an exact zero-defect criterion for $2 ^ m - 1$; and the sporadic spectra $\mathcal{W}(23) = \mathbb{N} \setminus \{1\}$, $\mathcal{W}(175) = \{0\} \cup [3, \infty)$ (the smallest multiplier with minimum nonzero weight $3$) and $\mathcal{W}(211) = \mathbb{N}$, the last via a weight-one defect at the single input $x = 17125$ that no short input reveals.

The engine is a residual Moore transducer on pending integer and carry-less tails $(u, v)$ with $0 \le v \le u < c$, so the infinite family of inputs is governed by finitely many states. A pure-data binary trie of Bellman inequalities is checked by kernel evaluation and `PotentialCert.sound` compiles it into the universal bound $\forall x,\ \Delta(c, x) \ne 0 \implies \mu \le W _ c (x)$. Shift separation $W _ c (x + 2 ^ K y) = W _ c (x) + W _ c (y)$ makes $\mathcal{W}(c)$ an additive submonoid, so a certificate plus $\mu$ witnesses yields the exact spectrum.

## For Non-Mathematicians

Computers can multiply two ways: the usual way where carries ripple from column to column, and a "carry-less" way used in cryptography and error-correcting codes where each column is added with XOR and nothing carries. The two answers agree for some inputs and differ in others. We count, exactly and for every input however large, how many binary digits can differ. For some multipliers every count appears; for others, such as $2 ^ m - 1$, a difference of exactly one digit is impossible, and for one multiplier ($211$) it is possible but only at an input as large as $17125$, which is why a finite search of small inputs would be fooled.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `CarryDefectWeightSpectra/Theorems.lean`, definitions in `CarryDefectWeightSpectra/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `spectrum_one_mod_four` | For every $c \ge 5$ with $c \bmod 4 = 1$ and every $w \in \mathbb{N}$ there is an $x$ with $W _ c (x) = w$, i.e. $\mathcal{W}(c) = \mathbb{N}$. |
| `mersenne_zero_defect_iff` | For $m \ge 1$ and every $x$, $\Delta(2 ^ m - 1, x) = 0$ if and only if $x$ is $m$-sparse (the $m$-fold generalization of Fibbinary numbers). |
| `mersenne_spectrum_classify` | For $m \ge 2$ and every $w$, a weight-$w$ defect exists if and only if $w \ne 1$. |
| `defectWeight_shift_add` | If $x < 2 ^ K$ and $c x < 2 ^ K$ then $W _ c (x + 2 ^ K y) = W _ c (x) + W _ c (y)$ for every $y$. |
| `potentialCert_sound` | If a finite state-table certificate passes the executable check and its root has pending tails $(0, 0)$, then $\Delta(c, x) \ne 0$ implies $\mu \le W _ c (x)$ for every $x \in \mathbb{N}$, where $\mu$ is the certified bound. |
| `spectrum_23` | A defect of weight $w$ exists for $c = 23$ if and only if $w \ne 1$. |
| `spectrum_175` | A defect of weight $w$ exists for $c = 175$ if and only if $w = 0$ or $w \ge 3$. |
| `spectrum_211` | Every weight $w \in \mathbb{N}$ is attained for $c = 211$, including weight $1$. |

## Proof Architecture

1. **Residual transducer (`popcount_genDefect_step`, `genDefect_eq_zero_imp_eq`):** peeling the low bit of $x$ gives an exact recurrence for the popcount of the generalized defect with $O(1)$ state per multiplier; from any state with $v \le u$ a zero defect forces $u = v$.
2. **Certificate compiler (`PotentialCert.sound`):** a pure-data binary trie stores Bellman lower bounds per reachable state; one Boolean pass checks all local inequalities and strong induction on $x$ lifts them to every input.
3. **Additivity and spectrum lifting (`defectWeight_shift_add`, `spectrum_classify_of_cert`):** shift separation turns the spectrum into a submonoid, so $\mu$ consecutive witnesses give $\{0\} \cup [\mu, \infty)$.
4. **Parametric families (`spectrum_one_mod_four`, `mersenne_*`):** the bit-length-$L$ input $1 + 2 ^ {L - 1}$ realizes defect $2 ^ L$ for $c \equiv 1 \pmod 4$; for $2 ^ m - 1$ every diagonal state is $(2 ^ r - 1, 2 ^ r - 1)$ and leaving it forces a second defect bit, with closed-form witnesses of weights $2$ and $3$.
5. **Sharpness (`sharpness_*`, `stealth_211_weight_one`):** kernel-checked boundary cases show each hypothesis is needed.

## Prior-Art Context

- **Classical background:** zero-carry addition ($x + y = x \oplus y \iff x \mathbin{\&} y = 0$), Fibbinary numbers (OEIS A003714, the $c = 3$ zero-defect baseline), carry Markov chains for integer addition (Holte 1997, Diaconis-Fulman 2009), and finite-state automatic sequences (Allouche-Shallit).
- **Referee audit (referee-6, 9.5/10 flagship S-Tier; recorded in `TOP_MECHANISMS.md`):** only the $c = 3$ Fibbinary zero-defect baseline is classical; the weight-spectrum submonoid classification, the residual Moore transducer with pure-data Bellman trie compiler, $\mathcal{W}(2 ^ m - 1) = \mathbb{N} \setminus \{1\}$, the minimal-$\mu$ multiplier $175$ and the $211$ stealth counterexample are new.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
