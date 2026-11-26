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

## 2. [`carry-blocks-determinants/`](carry-blocks-determinants/)

All statements are in [`carry-blocks-determinants/Challenge.lean`](carry-blocks-determinants/Challenge.lean) against pure-Mathlib definitions in [`carry-blocks-determinants/CarryBlocksDeterminants/Defs.lean`](carry-blocks-determinants/CarryBlocksDeterminants/Defs.lean).

| Theorem | Module | Statement |
|---|---|---|
| `det_mixedCarryBlocks_exp` | `CarryBlocksDeterminants.CarryBlocks` | $\det(x^{\mathrm{carryBlocks} _ b(k, i, j)}) _ {0 \le i, j < P _ k} = (-1)^{\binom{P _ k - 1}{2}} (x - 1)^{P _ k - 1}$ over any commutative ring $R$. |
| `det_mixedCarryBlocks_linear` | `CarryBlocksDeterminants.CarryBlocks` | Unimodularity $\det(\mathrm{carryBlocks} _ b(k, i, j)) _ {1 \le i, j < P _ k} = (-1)^{\binom{P _ k - 1}{2}}$ over any commutative ring $R$. |
| `det_binaryCarryBlocks` | `CarryBlocksDeterminants.CarryBlocks` | Binary specialization $\det(\mathrm{carryBlocks} _ 2(k, i, j)) _ {1 \le i, j < 2^k} = (-1)^{\binom{2^k - 1}{2}}$. |
| `det_grayCarryTransitions` | `CarryBlocksDeterminants.CarryBlocks` | Binary Gray-code carry-transition determinant $\det(\mathrm{popcnt}(g(i+j) \oplus g(i) \oplus g(j))) _ {1 \le i, j < 2^k} = (-1)^{\binom{2^k - 1}{2}} 2^{2^k - 1}$. |
| `det_plateauHankel_one` | `CarryBlocksDeterminants.PlateauHankel` | Universal 1-based plateau Hankel determinant $(-1)^{\binom{N-1}{2}} d^{N-2}(a+d)$, independent of $f(0), \dots, f(N-2)$. |
| `det_plateauHankel_zero` | `CarryBlocksDeterminants.PlateauHankel` | Universal 0-based plateau Hankel determinant $(-1)^{\binom{N-1}{2}} d^{N-2}(f(0)(a+d) - a^2)$ for $2M \le N$, independent of $f(1), \dots, f(M-1)$. |
| `det_mixedDigitLen_one` | `CarryBlocksDeterminants.PlateauHankel` | 1-based mixed-radix digit-length Hankel determinant $(-1)^{\binom{P _ k - 1}{2}}(k + 1)$ for any $b _ r \ge 2$. |
| `det_mixedDigitLen_zero` | `CarryBlocksDeterminants.PlateauHankel` | 0-based mixed-radix digit-length Hankel determinant $(-1)^{\binom{P _ k - 1}{2} + 1} k^2$ for any $b _ r \ge 2$. |
| `det_bitlen_xor_add_const` | `CarryBlocksDeterminants.UltrametricXor` | Exact shifted ultrametric XOR bit-length determinant $\det(\mathrm{bitlen}(i \oplus j) + t) _ {0 \le i, j < 2^k}$ over any commutative ring $R$. |
| `det_bitlen_xor` | `CarryBlocksDeterminants.UltrametricXor` | Unshifted specialization ($t = 0$) of the ultrametric XOR bit-length determinant. |

## 3. [`combinatorial-inequalities/`](combinatorial-inequalities/)

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

## 4. [`sorting-operators/`](sorting-operators/)

All statements are in [`sorting-operators/Challenge.lean`](sorting-operators/Challenge.lean) against pure-`Init` definitions in [`sorting-operators/SortingOperators/Defs.lean`](sorting-operators/SortingOperators/Defs.lean).

| Theorem | Module | Statement |
|---|---|---|
| `inv_bubble_add_des_le_inv` | `SortingOperators.Theorems` | $\mathrm{inv}(B(xs)) + \mathrm{des}(xs) \le \mathrm{inv}(xs)$ for every list $xs$. |
| `des_bubble_le_des` | `SortingOperators.Theorems` | $\mathrm{des}(B(xs)) \le \mathrm{des}(xs)$ for every list $xs$. |
| `westSort_split_max` | `SortingOperators.Theorems` | Exact maximum-splitting recurrence $S(L \mathbin{+\!\!+} [m] \mathbin{+\!\!+} R) = S(L) \mathbin{+\!\!+} S(R) \mathbin{+\!\!+} [m]$. |
| `bubblePass_split_max` | `SortingOperators.Theorems` | Exact maximum-splitting recurrence $B(L \mathbin{+\!\!+} [m] \mathbin{+\!\!+} R) = B(L) \mathbin{+\!\!+} R \mathbin{+\!\!+} [m]$. |
| `inv_westSort_le_bubble` | `SortingOperators.Theorems` | $\mathrm{inv}(S(xs)) \le \mathrm{inv}(B(xs))$ for every duplicate-free list $xs$. |
| `des_westSort_le_bubble` | `SortingOperators.Theorems` | $\mathrm{des}(S(xs)) \le \mathrm{des}(B(xs))$ for every duplicate-free list $xs$. |
| `westSort_eq_bubble_of_avoids321` | `SortingOperators.Theorems` | $S(xs) = B(xs)$ on every duplicate-free `321`-avoiding list $xs$. |
| `exists_not_avoids321_westSort_eq_bubble` | `SortingOperators.Theorems` | Strictness witness `xs = [2, 1, 3, 0]` containing `321` with $S(xs) = B(xs)$. |
| `inv_bubble_le_pat321_add_pat231` | `SortingOperators.Theorems` | $\mathrm{inv}(B(xs)) \le \mathrm{pat} _ {321}(xs) + \mathrm{pat} _ {231}(xs)$ for every duplicate-free list $xs$. |

## 5. [`bitwise-carry-algebra/`](bitwise-carry-algebra/)

All statements are in [`bitwise-carry-algebra/Challenge.lean`](bitwise-carry-algebra/Challenge.lean) against pure-`Init` definitions in [`bitwise-carry-algebra/BitwiseCarryAlgebra/Defs.lean`](bitwise-carry-algebra/BitwiseCarryAlgebra/Defs.lean).

| Theorem | Module | Statement |
|---|---|---|
| `carryWord_cocycle` | `BitwiseCarryAlgebra.Theorems` | Binary carry-word 2-cocycle $c(x, y) \oplus c(x + y, z) \oplus c(y, z) \oplus c(x, y + z) = 0$. |
| `carryPop_cocycle` | `BitwiseCarryAlgebra.Theorems` | Carry-popcount 2-cocycle $\mathrm{popcnt}(c(x, y)) + \mathrm{popcnt}(c(x + y, z)) = \mathrm{popcnt}(c(y, z)) + \mathrm{popcnt}(c(x, y + z))$. |
| `gray_add_xor_eq_gray_carryWord` | `BitwiseCarryAlgebra.Theorems` | Gray-code additivity defect $g(x + y) \oplus g(x) \oplus g(y) = g(c(x, y))$. |
| `popcnt_gray_carryWord` | `BitwiseCarryAlgebra.Theorems` | Gray-carry transition law $\mathrm{popcnt}(g(x + y) \oplus g(x) \oplus g(y)) = 2 \cdot \mathrm{carryBlocks}(x, y)$. |
| `borrowWord_eq_carryWord` | `BitwiseCarryAlgebra.Theorems` | Borrow-carry duality $b(x, y) = c(\min(x, y), \max(x, y) - \min(x, y))$. |
| `sumSquare_carryPop` | `BitwiseCarryAlgebra.Theorems` | Exact total carry count $2 \sum _ {0 \le i, j < 2^k} \mathrm{popcnt}(c(i, j)) + 4^k = k \cdot 4^k + 2^k$. |
| `sumSquare_carryBlocks` | `BitwiseCarryAlgebra.Theorems` | Exact total carry-block count $8 \sum _ {0 \le i, j < 2^k} \mathrm{carryBlocks}(i, j) + 2 \cdot 2^k = (k + 2) \cdot 4^k$. |
| `count_zero_and_one_carryBlock` | `BitwiseCarryAlgebra.Theorems` | Exact pair counts: $3^k$ zero-carry pairs over $[0, 2^k)^2$ and $(k + 2)(k + 7) \cdot 3^k / 2$ single-carry-block pairs over $[0, 2^{k+2})^2$. |

## 6. [`bit-circuit-synthesis/`](bit-circuit-synthesis/)

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
