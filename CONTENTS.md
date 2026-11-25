# Contents

Theorem-by-theorem index of the verified formalizations in this repository.

## 1. [`carry-determinants/`](carry-determinants/)

All statements are in [`carry-determinants/Challenge.lean`](carry-determinants/Challenge.lean) against pure-Mathlib definitions in [`carry-determinants/CarryDeterminants/Defs.lean`](carry-determinants/CarryDeterminants/Defs.lean).

| Theorem | Module | Statement |
|---|---|---|
| `carryMatrix_det_eq_zero_of_non_extremal` | `CarryDeterminants.CantorNonVanishing` | If $n - 1$ has any mixed-radix digit strictly between $0$ and $b _ r - 1$, then $\det(\mathrm{carryMatrix}(b, k, n, x)) = 0$ for every weight vector $x$. |
| `existsUnique_placeValue_perm` | `CarryDeterminants.CantorNonVanishing` | Under the Cantor extremal-digit condition on $n - 1$, there is a unique permutation $\pi \in S _ n$ fixing $0$ such that $i + \pi(i) = P _ r$ for every $1 \le i < n$. |
| `mixedCarryPolyMatrix_det_ne_zero_iff` | `CarryDeterminants.CantorNonVanishing` | Over any nontrivial commutative ring $R$, the mixed-radix polynomial carry determinant is nonzero iff every digit of $n - 1$ lies in $\{0, b _ r - 1\}$. |
| `baseCarryPolyMatrix_det_ne_zero_iff` | `CarryDeterminants.CantorNonVanishing` | Uniform base-$B$ specialization of the Cantor non-vanishing characterization. |
| `binaryCarryPolyMatrix_det_ne_zero` | `CarryDeterminants.CantorNonVanishing` | In base $2$, every $1 \le n \le 2^k$ has nonzero polynomial carry determinant over every nontrivial commutative ring. |
| `det_mixedHankelMatrix` | `CarryDeterminants.CarryFactorization` | Exact closed-form multivariate determinant factorization of the $N \times N$ mixed-radix Hankel matrix over any commutative ring. |
| `det_carryMatrix_full` | `CarryDeterminants.CarryFactorization` | Exact closed-form multivariate determinant factorization of the full $N \times N$ mixed-radix carry matrix over any commutative ring. |
| `det_weightedLinearCarryMatrix` | `CarryDeterminants.CarryFactorization` | Exact closed-form determinant for arbitrarily weighted linear carry matrices. |
| `det_kummer_padicValNat_choose` | `CarryDeterminants.CarryFactorization` | Exact determinant of the $(p^k - 1) \times (p^k - 1)$ Kummer $p$-adic valuation matrix $v _ p\binom{i+j}{i}$. |
| `det_binary_carry_word` | `CarryDeterminants.CarryFactorization` | Exact determinant of the $(2^k - 1) \times (2^k - 1)$ binary carry-word matrix $(i + j) \oplus i \oplus j$. |
| `det_thueMorse_pow_two` | `CarryDeterminants.CarryFactorization` | Exact determinant $\det((-1)^{s _ 2(i+j)}) _ {0 \le i,j < 2^k} = 2^{2^k - 1}$ for all $k \ge 2$. |

## 2. [`combinatorial-inequalities/`](combinatorial-inequalities/)

Headline statements are in [`combinatorial-inequalities/Challenge.lean`](combinatorial-inequalities/Challenge.lean) against pure-`Std` definitions in [`combinatorial-inequalities/CombInequalities/CombDefs.lean`](combinatorial-inequalities/CombInequalities/CombDefs.lean). Full 23-cluster library is in `CombInequalities.ProvedDiscoveries` and `CombInequalities.OpenConjectures`.

| Theorem | Carrier | Statement |
|---|---|---|
| `stackInv_le_popInv` | Permutations | $\mathrm{inv}(S(p)) \le \mathrm{inv}(P(p))$ for all $p \in S _ n$ (West stack vs. pop-stack inversion dominance). |
| `avoids321_three_stack2Inv_le_pat231` | Permutations | $3\,\mathrm{inv}(S^2(p)) \le \mathrm{pat231}(p)$ for all $p \in \mathrm{Av} _ n(321)$. |
| `stackDes_le_peaksCnt` | Permutations | $\mathrm{des}(S(p)) \le \mathrm{peaks}(p)$ for all $p \in S _ n$. |
| `stackInv_le_pat231` | Permutations | $\mathrm{inv}(S(p)) \le \mathrm{pat231}(p)$ for all $p \in S _ n$. |
| `avoids231_two_inv_le_disp2_add_des` | Permutations | $2\,\mathrm{inv}(p) \le \mathrm{disp2}(p) + \mathrm{des}(p)(\mathrm{des}(p) + 1)$ for all $p \in \mathrm{Av} _ n(231)$. |
| `sidon_sym_defect_eq` | Additive sets | $\mathrm{symDefect}(A) + 4 = 2|A|$ for every non-trivial finite Sidon set $A$. |
| `two_card_add_symDefect_le_diffset_add_one` | Additive sets | $2|A| + \mathrm{symDefect}(A) \le |A - A| + 1$ for normalized $A \subseteq [0, N - 1]$. |
| `three_diffset_le_two_sum2Diff1_add_one` | Additive sets | $3|A - A| \le 2|2A - A| + 1$ for normalized $A \subseteq [0, N - 1]$. |
| `connected_diam_le_indP4_add_two` | Graphs | $\mathrm{diam}(G) \le \mathrm{indP4}(G) + 2$ for every finite connected graph $G$. |
| `albertson_le_orderedIndP3` | Graphs | $\mathrm{albertson}(G) \le \mathrm{orderedIndP3}(G)$ for every finite simple graph $G$. |
| `disproof_avoids231_inv_disp_lds` | Permutations | Explicit $n = 9$ counterexample disproving $2\,\mathrm{inv}(p) \le \mathrm{disp2}(p) + \mathrm{lds}(\mathrm{lds} - 1)$ on $\mathrm{Av}(231)$. |
| `disproof_bipartite_dom_indNu_diam` | Graphs | Explicit $25$-vertex tree (`tree25`) disproving $\gamma + 1 \le \nu _ {\mathrm{ind}} + \mathrm{diam}$ on connected bipartite graphs. |

## 3. [`bit-circuit-synthesis/`](bit-circuit-synthesis/)

Headline statements are in [`bit-circuit-synthesis/Challenge.lean`](bit-circuit-synthesis/Challenge.lean) against pure-`Init` definitions in [`bit-circuit-synthesis/BitCircuitSynthesis/CarryDefs.lean`](bit-circuit-synthesis/BitCircuitSynthesis/CarryDefs.lean). The library also includes the complete `1,799`-theorem universal bit-circuit suite in `BitCircuitSynthesis.AutoEpoch6Complete1799Verify`.

| Theorem | Module | Statement |
|---|---|---|
| `bpos_clmul_deg_additive` | `BitCircuitSynthesis.Apex3CarryDictionaryF2xVerify` | Universal carry-less degree additivity $\deg(p \otimes q) = \deg(p) + \deg(q)$ on `BPos`. |
| `bf2x_integral_domain` | `BitCircuitSynthesis.Apex3CarryDictionaryF2xVerify` | Carry-less multiplication on `BBin` has no zero divisors ($\mathbb{F} _ 2[x]$ is an integral domain). |
| `bcarried_vs_carryless_deg_jump_witness` | `BitCircuitSynthesis.Apex3CarryDictionaryF2xVerify` | Exact degree-jump contrast between carry-less $3 \otimes 3 = 5$ (degree $2$) and carried $3 \cdot 3 = 9$ (degree $3$). |
| `bartin_schreier_add_hom` | `BitCircuitSynthesis.Apex3CarryDictionaryF2xVerify` | Additivity of the Artin-Schreier operator $\wp(x) = x^2 \oplus x$ over all `BBin`. |
| `bartin_schreier_shift_one_inv` | `BitCircuitSynthesis.Apex3CarryDictionaryF2xVerify` | Exact 2-to-1 fiber invariance $\wp(x \oplus 1) = \wp(x)$. |
| `bfrob2_xor_hom` | `BitCircuitSynthesis.Apex3CarryDictionaryF2xVerify` | Frobenius squaring homomorphism $(x \oplus y)^2 = x^2 \oplus y^2$. |
| `bfrob_trace_artin_schreier_telescope` | `BitCircuitSynthesis.Apex3CarryDictionaryF2xVerify` | Iterated Frobenius trace telescoping $\mathrm{Tr} _ m(x^2 \oplus x) = x^{2^m} \oplus x$ for all heights $m$. |
| `bhilbert90_additive_trace_zero_mod` | `BitCircuitSynthesis.Apex3CarryDictionaryF2xVerify` | Additive Hilbert's Theorem 90 modulo any $P _ m$ fixing $x^{2^m}$. |
