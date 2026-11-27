# Binary SRS Matrix/Critical-Pair Compiler: Certified Termination & Confluence, Euler–Fermat Dichotomy, Infinite Residue Normalizers (`binary-srs-matrix-cp-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **7 / 10** | **8 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **81 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a zero-dependency, pure Lean 4 `Init` reflection compiler that turns a finite pure-data certificate (layered natural-number matrix weights plus a complete critical-pair trace replay) into termination, global confluence, unique normal forms and a verified Church–Rosser normalizer for binary string rewriting over bit-strings of arbitrary length, together with an exact Euler–Fermat confluence dichotomy for a 5-parameter length-increasing family and infinite Mersenne/Fermat residue normalizer families. Classical foundations are credited below.*

## For Mathematicians

A binary string rewriting system (SRS) $R \subset \{0,1\}^* \times \{0,1\}^*$ induces an infinite rewrite graph over all bit-strings. We prove a finite-certificate-to-infinite-theorem bridge. A pure-data `ConfluenceCert` consists of

1. **Layered matrix weights.** Each layer $t$ assigns two $d _ t \times d _ t$ natural-number matrices $M _ {t,0}, M _ {t,1}$ with positive corners $(M _ {t,b}) _ {0,0} \ge 1$ and $(M _ {t,b}) _ {d _ t - 1, d _ t - 1} \ge 1$. Extending homomorphically by $\mu _ t(b \cdot w) = M _ {t,b} \, \mu _ t(w)$, the top-right entry $(\mu _ t(w)) _ {0, d _ t - 1}$ is monotone in every context. Stacking layers lexicographically (a constructively well-founded order on fixed-length vectors in $\mathbb{N}^k$) certifies global termination even for length-preserving and exponentially length-increasing systems.
2. **Complete critical-pair enumeration with deterministic trace replay.** `criticalPairs R` enumerates every inclusion and suffix–prefix overlap, and each pair carries an explicit finite pair of `(ruleIdx, pos)` rewrite traces replayed by the kernel.

The master theorem `cert_sound` proves that an accepted certificate yields $\mathrm{Terminating}(R) \land \mathrm{Confluent}(R) \land \mathrm{UniqueNormalForms}(R)$ via a constructive Newman lemma, and `convertible_iff_normalize_eq` gives the Church–Rosser word-problem decision $\mathrm{Convertible}(R, u, v) \iff \mathrm{normalize}(u) = \mathrm{normalize}(v)$ for all bit-strings $u, v$.

For the 5-parameter family $\mathcal{S}(b, r, s, k, d) = \{10 \to 0^b 1,\; 0^{k+d} \to 0^k,\; 1^r \to 1^s\}$ with $b \ge 2$, $s < r$, $k, d \ge 1$, one $2 \times 2$ matrix layer $M _ 0 = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$, $M _ 1 = \begin{pmatrix} b+1 & 1 \\ 0 & 1 \end{pmatrix}$ proves termination despite derivations of length $\Omega(b^n)$, and we prove the exact Euler–Fermat dichotomy

```math
\mathrm{Confluent}(\mathcal{S}(b, r, s, k, d)) \iff \big(k \le b^s \;\land\; d \mid b^r - b^s\big).
```

When it fails, the single word $1^r 0$ splits into two distinct normal forms. A general semantic-invariant meta-theorem (`confluent_of_term_invariant`) shows that a terminating SRS preserving an invariant injective on normal forms is confluent with $\mathrm{Convertible}(u, v) \iff \mathrm{inv}(u) = \mathrm{inv}(v)$. Applying it to length-preserving binary systems with the value invariant $\mathrm{binVal}$ yields the infinite families: for every $m \ge 2$ the $(2^m - 1)$-rule Mersenne system `mersenneSRS m`, and for every $m \ge 1$ the $(2^m + 1)$-rule Fermat system `fermatModSRS m`, are terminating, confluent, have unique normal forms, and are convertible exactly when the lengths agree and the residues modulo $2^m \mp 1$ agree. The 4-rule system `mod3SRS` (which needs a 2-layer $2 \times 2$ plus $3 \times 3$ matrix stack) is shown semantically complete for residues modulo $3$ on all bit-strings. Sharpness is kernel-checked: dropping any single `mod3SRS` rule, perturbing $d$ or $k$ across the dichotomy boundary, or adding the reverse rule $01 \to 10$ breaks the corresponding property, and ten certificate mutations are rejected by `decide`.

## For Non-Mathematicians

Imagine a machine that rewrites a string of $0$s and $1$s using a short list of find-and-replace rules, and you want to be sure of two things for **every** string, however long: that it always stops, and that no matter which rule you apply first you always end at the same final string. Normally you would have to test infinitely many strings. This project shows that a small checkable "certificate" (a few little tables of whole numbers that act like a score that must go down each step, plus a finite list of how every possible rule clash resolves) is enough: if the computer's finite check passes, the guarantee holds for every bit-string on Earth. As a showpiece it produces a tiny set of local rules that computes remainders after dividing by $3$, by $2^m - 1$ and by $2^m + 1$ for any size $m$, and it pins down exactly when a family of growing rules stays well behaved: precisely when a divisibility condition on powers of $b$ holds.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of a matrix-weight and critical-pair reflection engine for binary string rewriting, with an exact confluence dichotomy and infinite residue-normalizer families.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `cert_sound` | If the finite checker accepts a `ConfluenceCert` for a binary SRS $R$, then $R$ is terminating, confluent and has unique normal forms on all bit-strings. |
| `convertible_iff_normalize_eq` | For a certified $R$ and every $u, v \in \{0,1\}^*$: $\mathrm{Convertible}(R, u, v) \iff \mathrm{normalize}(R, u) = \mathrm{normalize}(R, v)$. |
| `confluent_of_term_invariant` | A terminating SRS preserving an invariant that is injective on normal forms is confluent, has unique normal forms, and $\mathrm{Convertible}(u, v) \iff \mathrm{inv}(u) = \mathrm{inv}(v)$. |
| `ampSys_terminating` | For $b \ge 2$, $s < r$, $k, d \ge 1$, the system $\{10 \to 0^b 1,\; 0^{k+d} \to 0^k,\; 1^r \to 1^s\}$ is terminating. |
| `ampSys_confluent_iff` | For the same parameters, the system is confluent if and only if $k \le b^s$ and $d \mid b^r - b^s$. |
| `mod3_convertible_iff` | For all bit-strings $u, v$, $u$ and $v$ are convertible under the 4-rule system `mod3SRS` iff $\lvert u \rvert = \lvert v \rvert$ and $\mathrm{binVal}(u) \equiv \mathrm{binVal}(v) \pmod 3$. |
| `mersenneSRS_master` | For every $m \ge 2$, the $(2^m - 1)$-rule system is terminating, confluent, has unique normal forms, and $\mathrm{Convertible}(u, v) \iff \lvert u \rvert = \lvert v \rvert \land \mathrm{binVal}(u) \equiv \mathrm{binVal}(v) \pmod{2^m - 1}$. |
| `fermatModSRS_master` | For every $m \ge 1$, the $(2^m + 1)$-rule system is terminating, confluent, has unique normal forms, and $\mathrm{Convertible}(u, v) \iff \lvert u \rvert = \lvert v \rvert \land \mathrm{binVal}(u) \equiv \mathrm{binVal}(v) \pmod{2^m + 1}$. |

Note: in `Challenge.lean` the normalizer is stated with an explicit termination proof argument `hTerm : Terminating R` (a proof, so any two choices are equal); the internal theorem derives it from `cert_sound`.

## Proof Architecture

1. **Layered matrix termination.** Materialized `List (List Nat)` matrices with explicit well-formedness; `matEval_append` (matrix multiplication is associative and compatible with concatenation), corner positivity (`matEval_tl_pos`, `matEval_br_pos`) and strict top-right decrease (`matMul_strict_tr`) give a per-layer measure; `LexLt` on fixed-length vectors is shown well-founded by nested induction (`wf_lexLt`), so `checkTermination_sound` yields `Terminating R`.
2. **Critical pairs.** `peak_joinable_of_le` splits every peak into a disjoint-redex case (one-step join) or an inclusion / suffix–prefix overlap that is literally a member of `criticalPairs R`; `locallyConfluent_of_criticalPairs` and the trace-replay soundness (`replayTrace_sound`) yield `checkJoinability_sound`.
3. **Constructive Newman and normalizer.** `newman` (termination plus local confluence gives confluence) is proved by well-founded induction without axioms; `normalize` runs `findStep` by `WellFounded.fix`, and `normalize_spec` shows it returns a normal form reachable from the input. `cert_sound` combines these and `convertible_iff_normalize_eq` follows from Church–Rosser.
4. **Euler–Fermat dichotomy.** One $2 \times 2$ layer proves `ampSys_terminating`; sufficiency of $k \le b^s \land d \mid b^r - b^s$ pushes ones through zeros and compresses zero blocks modulo $d$ (`ampSys_confluent_of_cond`); necessity compares two normal-form derivations of $1^r 0$ (`ampSys_confluent_iff`).
5. **Infinite residue families.** `binValLayer` (the $2 \times 2$ matrix $\begin{pmatrix} 1 & \mathrm{binVal}(w) \\ 0 & 2^{\lvert w \rvert} \end{pmatrix}$) proves termination of any length-preserving value-decreasing system; `confluent_of_term_invariant` plus normal-form injectivity of $(\lvert w \rvert, \mathrm{binVal}(w) \bmod M)$ gives the master theorems, with concrete `decide` certificates for `mod3SRS`, `mod5SRS`, `mod7SRS` and others.

## Prior-Art Context

- **Matrix interpretations and critical pairs.** Matrix interpretations for string-rewriting termination are due to Hofbauer and Waldmann (*Termination of string rewriting with matrix interpretations*, RTA 2006) and Endrullis, Waldmann and Zantema (*Matrix interpretations for proving termination of term rewriting*, 2008); critical-pair confluence is Knuth and Bendix (1970), with Newman's Lemma (1942). Certified termination/confluence checkers exist in Isabelle/HOL (`IsaFoR/CeTA`) and Coq (`CoLoR/Rainbow`). The referee noted that the rule $\{101 \to 010, 11 \to 00, 100 \to 001, 0101 \to 0010\}$ for `mod3SRS` contains one redundant rule; the package includes the kernel-checked sharpness results for dropping each rule (`mod3_drop0_incomplete`, `mod3_drop1_not_confluent`, `mod3_drop2_not_confluent`).
- **What is new here (as far as the referee's search found).** A zero-dependency pure-`Init` Lean 4 reflection compiler combining materialized arbitrary-dimension lexicographic matrix stacks, a complete critical-pair trace verifier and a computable normalizer; the exact 5-parameter Euler–Fermat confluence dichotomy $k \le b^s \land d \mid b^r - b^s$; the semantic completeness of the length-preserving binary mod-3 normalizer; and the parametric Mersenne/Fermat local normalizer families. Referee verdict: PASS, novelty Tier A (3.8/5) with honest classical credit.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

`scripts/explore_and_verify.py` independently replays the certificates and the dichotomy in pure integer arithmetic. See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
