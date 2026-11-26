# Contents

Theorem-by-theorem index of the verified formalizations in this repository.

## 1. [`carry-determinants/`](carry-determinants/)

All statements are in [`carry-determinants/Challenge.lean`](carry-determinants/Challenge.lean) against pure-Mathlib definitions in [`carry-determinants/CarryDeterminants/Defs.lean`](carry-determinants/CarryDeterminants/Defs.lean). See [`carry-determinants/README.md`](carry-determinants/README.md) for detailed prior-art citations (Sobolewski–Ulas 2026, Bacher–Chapman 2004, Bacher 2007, APWW 1998).

| Theorem | Module | Statement |
|---|---|---|
| `carryMatrix_det_eq_zero_of_non_extremal` | `CarryDeterminants.CantorNonVanishing` | If $n - 1$ has any mixed-radix digit strictly between $0$ and $b _ r - 1$, then $\det(\mathrm{carryMatrix}(b, k, n, x)) = 0$ for every weight vector $x$. |
| `existsUnique_placeValue_perm` | `CarryDeterminants.CantorNonVanishing` | Under the Cantor extremal-digit condition on $n - 1$, there is a unique permutation $\pi \in S _ n$ fixing $0$ such that $i + \pi(i) = P _ r$ for every $1 \le i < n$. |
| `mixedCarryPolyMatrix_det_ne_zero_iff` | `CarryDeterminants.CantorNonVanishing` | Over any nontrivial commutative ring $R$, the mixed-radix polynomial carry determinant is nonzero iff every digit of $n - 1$ lies in $\{0, b _ r - 1\}$. |
| `baseCarryPolyMatrix_det_ne_zero_iff` | `CarryDeterminants.CantorNonVanishing` | Uniform base-$B$ specialization of the Cantor non-vanishing characterization. |
| `binaryCarryPolyMatrix_det_ne_zero` | `CarryDeterminants.CantorNonVanishing` | Base-$2$ specialization: every $1 \le n \le 2^k$ has nonzero polynomial carry determinant over every nontrivial commutative ring (also implied at $X = 0$ by Bacher & Chapman 2004). |
| `det_mixedHankelMatrix` | `CarryDeterminants.CarryFactorization` | Exact closed-form multivariate determinant factorization of the $N \times N$ mixed-radix multiplicative Hankel matrix over any commutative ring. |
| `det_carryMatrix_full` | `CarryDeterminants.CarryFactorization` | Exact closed-form multivariate determinant factorization of the full $N \times N$ mixed-radix carry matrix over any commutative ring. |
| `det_weightedLinearCarryMatrix` | `CarryDeterminants.CarryFactorization` | Exact closed-form determinant for arbitrarily weighted linear mixed-radix carry matrices (base-$2$ case algebraically equivalent to Sobolewski & Ulas 2026, `arXiv:2607.09376`). |
| `det_kummer_padicValNat_choose` | `CarryDeterminants.CarryFactorization` | Exact determinant of the $(p^k - 1) \times (p^k - 1)$ Kummer $p$-adic valuation matrix $v _ p\binom{i+j}{i}$ ($p = 2$ case matches Sobolewski & Ulas 2026). |
| `det_binary_carry_word` | `CarryDeterminants.CarryFactorization` | Exact determinant of the $(2^k - 1) \times (2^k - 1)$ binary carry-word matrix $(i + j) \oplus i \oplus j$. |
| `det_thueMorse_pow_two` | `CarryDeterminants.CarryFactorization` | Exact determinant $\det((-1)^{s _ 2(i+j)}) _ {0 \le i,j < 2^k} = 2^{2^k - 1}$ for all $k \ge 2$ (cf. APWW 1998, OEIS A186026). |

## 2. [`carry-blocks-determinants/`](carry-blocks-determinants/)

All statements are in [`carry-blocks-determinants/Challenge.lean`](carry-blocks-determinants/Challenge.lean) against pure-Mathlib definitions in [`carry-blocks-determinants/CarryBlocksDeterminants/Defs.lean`](carry-blocks-determinants/CarryBlocksDeterminants/Defs.lean). See [`carry-blocks-determinants/README.md`](carry-blocks-determinants/README.md) for prior-art context.

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

Headline statements are in [`combinatorial-inequalities/Challenge.lean`](combinatorial-inequalities/Challenge.lean) against pure-`Std` definitions in [`combinatorial-inequalities/CombInequalities/CombDefs.lean`](combinatorial-inequalities/CombInequalities/CombDefs.lean). See [`combinatorial-inequalities/README.md`](combinatorial-inequalities/README.md) for prior-art citations.

| Theorem | Carrier | Statement |
|---|---|---|
| `avoids321_three_stack2Inv_le_pat231` | Permutations | $3\,\mathrm{inv}(S^2(p)) \le \mathrm{pat} _ {231}(p)$ for all $p \in \mathrm{Av} _ n(321)$. |
| `stackDes_le_peaksCnt` | Permutations | $\mathrm{des}(S(p)) \le \mathrm{peaks}(p)$ for all $p \in S _ n$. |
| `avoids231_two_inv_le_disp2_add_des` | Permutations | $2\,\mathrm{inv}(p) \le \mathrm{disp2}(p) + \mathrm{des}(p)(\mathrm{des}(p) + 1)$ for all $p \in \mathrm{Av} _ n(231)$. |
| `three_diffset_le_two_sum2Diff1_add_one` | Additive sets | $3|A - A| \le 2|2A - A| + 1$ for normalized $A \subseteq [0, N - 1]$. |

## 4. [`sorting-operators/`](sorting-operators/)

All statements are in [`sorting-operators/Challenge.lean`](sorting-operators/Challenge.lean) against pure-`Init` definitions in [`sorting-operators/SortingOperators/Defs.lean`](sorting-operators/SortingOperators/Defs.lean). See [`sorting-operators/README.md`](sorting-operators/README.md) for prior-art citations.

| Theorem | Module | Statement |
|---|---|---|
| `inv_westSort_le_bubble` | `SortingOperators.Theorems` | $\mathrm{inv}(S(xs)) \le \mathrm{inv}(B(xs))$ for every duplicate-free list $xs$. |
| `des_westSort_le_bubble` | `SortingOperators.Theorems` | $\mathrm{des}(S(xs)) \le \mathrm{des}(B(xs))$ for every duplicate-free list $xs$. |
| `westSort_eq_bubble_of_avoids321` | `SortingOperators.Theorems` | $S(xs) = B(xs)$ on every duplicate-free `321`-avoiding list $xs$. |
| `exists_not_avoids321_westSort_eq_bubble` | `SortingOperators.Theorems` | Strictness witness `xs = [2, 1, 3, 0]` containing `321` with $S(xs) = B(xs)$. |
| `inv_bubble_le_pat321_add_pat231` | `SortingOperators.Theorems` | $\mathrm{inv}(B(xs)) \le \mathrm{pat} _ {321}(xs) + \mathrm{pat} _ {231}(xs)$ for every duplicate-free list $xs$. |

## 5. [`zero-carry-spanning-trees/`](zero-carry-spanning-trees/)

All statements are in [`zero-carry-spanning-trees/Challenge.lean`](zero-carry-spanning-trees/Challenge.lean) against pure-Mathlib definitions in [`zero-carry-spanning-trees/ZeroCarrySpanningTrees/Defs.lean`](zero-carry-spanning-trees/ZeroCarrySpanningTrees/Defs.lean). See [`zero-carry-spanning-trees/README.md`](zero-carry-spanning-trees/README.md) for proof overview and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `det_zeroCarryWalk_charpoly` | `ZeroCarrySpanningTrees.SpanningTrees` | Exact alternating-harmonic characteristic polynomial $\det(x I - W _ {b,k}) = \prod _ {j < P _ k} \bigl(x - \prod _ {r < k} (-1)^{d _ r(j)} / (d _ r(j) + 1)\bigr)$ over $\mathbb{Q}$. |
| `det_zeroCarryCofactor_mixed` | `ZeroCarrySpanningTrees.SpanningTrees` | Exact mixed-radix Kirchhoff spanning-tree formula $\bigl(\prod _ {r < k} \binom{b _ r + 1}{2}\bigr) \det(L _ {b,k}^{(0,0)}) = \prod _ {j=1}^{P _ k - 1} \bigl(\prod _ {r < k} (d _ r(j) + 1) - \prod _ {r < k} (-1)^{d _ r(j)}\bigr)$ over any commutative ring $R$. |
| `det_zeroCarryCofactor_base` | `ZeroCarrySpanningTrees.SpanningTrees` | Uniform base-$B$ specialization of the mixed-radix spanning-tree formula over any commutative ring $R$. |
| `det_binaryZeroCarryCofactor` | `ZeroCarrySpanningTrees.SpanningTrees` | Exact binary zero-carry (`i &&& j = 0`) spanning-tree count $\tau(G _ {2^k}) = \prod _ {m=2}^k (2^m - (-1)^m)^{\binom{k}{m}}$ over any commutative ring $R$. |
| `det_singleRadixZeroCarryCofactor` | `ZeroCarrySpanningTrees.SpanningTrees` | Single-radix $k = 1$ threshold half-graph specialization over any commutative ring $R$. |

## 6. [`bitrev-increment-cycles/`](bitrev-increment-cycles/)

All statements are in [`bitrev-increment-cycles/Challenge.lean`](bitrev-increment-cycles/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`bitrev-increment-cycles/BitrevIncrementCycles/Defs.lean`](bitrev-increment-cycles/BitrevIncrementCycles/Defs.lean). See [`bitrev-increment-cycles/README.md`](bitrev-increment-cycles/README.md) for the $k \to k + 2$ return-map proof and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `bitrevInc_odd_single_cycle` | `BitrevIncrementCycles.Theorems` | For every odd bit-width $k = 2t + 1$, $f _ k(x) = (\mathrm{bitrev} _ k(x) + 1) \bmod 2^k$ is a single Hamiltonian cycle of length $2^{2t+1}$. |
| `bitrevInc_even_zero_period` | `BitrevIncrementCycles.Theorems` | For every even bit-width $k = 2(m + 1)$, the orbit of $0$ under $f _ {2(m+1)}$ has exact minimal period $2^{m+2} - 1$. |
| `bitrevInc_single_cycle_iff_odd` | `BitrevIncrementCycles.Theorems` | For every $k \ge 1$, $f _ k$ acts as a single cycle on $\{0, \dots, 2^k - 1\}$ iff $k$ is odd. |
| `bitrevInc_return_map` | `BitrevIncrementCycles.Theorems` | Exact $3/4/5$-step $k \to k + 2$ return-map law on the embedded slice $2m = (0, m, 0)$. |

## 7. [`skew-thue-morse-pfaffian/`](skew-thue-morse-pfaffian/)

All statements are in [`skew-thue-morse-pfaffian/Challenge.lean`](skew-thue-morse-pfaffian/Challenge.lean) against pure-Mathlib definitions in [`skew-thue-morse-pfaffian/SkewThueMorsePfaffian/Defs.lean`](skew-thue-morse-pfaffian/SkewThueMorsePfaffian/Defs.lean). See [`skew-thue-morse-pfaffian/README.md`](skew-thue-morse-pfaffian/README.md) for the half-swap Schur annihilation proof and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `det_skewThueMorse_even` | `SkewThueMorsePfaffian.Theorems` | Unimodularity $\det(A _ {2m}^{(0)}) = 1$ for all $m \in \mathbb{N}$ over any commutative ring $R$. |
| `det_skewThueMorse_shift1_even` | `SkewThueMorsePfaffian.Theorems` | Unimodularity $\det(A _ {2m}^{(1)}) = 1$ for all $m \in \mathbb{N}$ over any commutative ring $R$. |
| `det_skewThueMorse_shift2_even` | `SkewThueMorsePfaffian.Theorems` | Unimodularity $\det(A _ {2m}^{(2)}) = 1$ for all $m \in \mathbb{N}$ over any commutative ring $R$. |
| `det_skewThueMorse_odd` | `SkewThueMorsePfaffian.Theorems` | Odd-size vanishing $\det(A _ {2m+1}^{(s)}) = 0$ for all $s, m \in \mathbb{N}$ over any commutative ring $R$ (including char $2$). |

## 8. [`clmul-lift-determinants/`](clmul-lift-determinants/)

All statements are in [`clmul-lift-determinants/Challenge.lean`](clmul-lift-determinants/Challenge.lean) against pure-Mathlib definitions in [`clmul-lift-determinants/ClmulLiftDeterminants/Defs.lean`](clmul-lift-determinants/ClmulLiftDeterminants/Defs.lean). See [`clmul-lift-determinants/README.md`](clmul-lift-determinants/README.md) for the polynomial Schur reduction to bit-reversed Hadamard matrices and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `det_oddClmulMatrix_pow_two` | `ClmulLiftDeterminants.Theorems` | Exact monomial determinant $\det(M _ {2^k}(t)) = (\text{if } k = 2 \text{ then } 1 \text{ else } -1) \cdot 2^{k \cdot 2^{k-1}} \cdot t^{(k-1) 2^k + 1}$ for all $k \ge 1$ over any commutative ring $R$. |
| `det_oddClmulMatrix_pow_two_add_one` | `ClmulLiftDeterminants.Theorems` | Exact recurrence $\det(M _ {2^k + 1}(t)) = (-2 t^{k+1}) \det(M _ {2^k}(t))$ for all $k \in \mathbb{N}$ over any commutative ring $R$. |
| `det_oddClmulMatrix_pow_two_sub_one` | `ClmulLiftDeterminants.Theorems` | Exact monomial determinant $\det(M _ {2^k - 1}(t)) = (\text{if } k \le 3 \text{ then } 1 \text{ else } (-1)^{k-1}) \cdot 2^{k \cdot 2^{k-1} - k} \cdot t^{(k-1) 2^k + 1 - k}$ for all $k \ge 1$ over any commutative ring $R$. |
| `det_oddClmulMatrix_eq_zero_of_gap` | `ClmulLiftDeterminants.Theorems` | Identical vanishing $\det(M _ n(t)) = 0$ for every $2^k + 2 \le n \le 2^{k+1} - 2$ over any commutative ring $R$. |
| `det_oddClmulMatrix_ne_zero_iff` | `ClmulLiftDeterminants.Theorems` | Complete non-vanishing locus over any integral domain $R$ with $2 \ne 0, t \ne 0$: $\det(M _ n(t)) \ne 0 \iff \exists k,\, n \in \{2^k - 1, 2^k, 2^k + 1\}$. |

## 9. [`weak-bruhat-commutators/`](weak-bruhat-commutators/)

All statements are in [`weak-bruhat-commutators/Challenge.lean`](weak-bruhat-commutators/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`weak-bruhat-commutators/WeakBruhatCommutators/Defs.lean`](weak-bruhat-commutators/WeakBruhatCommutators/Defs.lean). See [`weak-bruhat-commutators/README.md`](weak-bruhat-commutators/README.md) for the Bubble-Refined Order architecture and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `desBot_bubblePass_iff` | `WeakBruhatCommutators.Commutators` | Exact descent-bottom characterization of single-pass bubble sort: $b \in \mathrm{DesBot}(B(xs)) \iff b \in \mathrm{DesBot}(xs) \wedge \mathrm{leftInv}(xs, b) \ge 2$. |
| `bubbleOrder_bubblePass_mono` | `WeakBruhatCommutators.Commutators` | Monotonicity of bubble sort $B$ in the Bubble-Refined Order $\preceq _ B$. |
| `iterBubble_west_commutator` | `WeakBruhatCommutators.Commutators` | All-$k$ Bubble–West commutator inclusion $B^k(S(xs)) \preceq _ B S(B^k(xs))$. |
| `iterBubble_pop_commutator` | `WeakBruhatCommutators.Commutators` | All-$k$ Bubble–Pop commutator inclusion $B^k(P(xs)) \preceq _ B P(B^k(xs))$. |
| `invCnt_iterBubble_west_le` | `WeakBruhatCommutators.Commutators` | All-$k$ inversion commutator inequality $\mathrm{inv}(B^k(S(xs))) \le \mathrm{inv}(S(B^k(xs)))$. |
| `desCnt_iterBubble_west_le` | `WeakBruhatCommutators.Commutators` | All-$k$ descent commutator inequality $\mathrm{des}(B^k(S(xs))) \le \mathrm{des}(S(B^k(xs)))$. |
| `invCnt_iterBubble_pop_le` | `WeakBruhatCommutators.Commutators` | All-$k$ inversion commutator inequality $\mathrm{inv}(B^k(P(xs))) \le \mathrm{inv}(P(B^k(xs)))$. |
| `desCnt_iterBubble_pop_le` | `WeakBruhatCommutators.Commutators` | All-$k$ descent commutator inequality $\mathrm{des}(B^k(P(xs))) \le \mathrm{des}(P(B^k(xs)))$. |

## 10. [`binary-lyness-periods/`](binary-lyness-periods/)

All statements are in [`binary-lyness-periods/Challenge.lean`](binary-lyness-periods/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`binary-lyness-periods/BinaryLynessPeriods/Defs.lean`](binary-lyness-periods/BinaryLynessPeriods/Defs.lean). See [`binary-lyness-periods/README.md`](binary-lyness-periods/README.md) for the carry-renormalization proofs and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `feistelStep_iter_six_of_even_parity` | `BinaryLynessPeriods.Theorems` | If $f(2k) = 2k + 1$ and $f(2k + 1) = 2h(k)$ for any $h : \mathbb{N} \to \mathbb{N}$, then $F _ f^6(x, y) = (x, y)$ whenever $x \% 2 = 0 \lor y \% 2 = 0$. |
| `feistelStep_iter_twelve_of_odd_parity` | `BinaryLynessPeriods.Theorems` | If $f(2k) = 2k + 1$ and $f(2k + 1) = 2g(k) + 1$ for any $g : \mathbb{N} \to \mathbb{N}$, then $F _ f^{12}(x, y) = (x, y)$ for all $(x, y) \in \mathbb{N} \times \mathbb{N}$. |
| `lynessStep_pow_two_period_six` | `BinaryLynessPeriods.Theorems` | Universal period $6$ of $F _ {2^r}(x, y) = (y,\; x \oplus (y + 2^r))$ for all $r, x, y \in \mathbb{N}$. |
| `lynessStep_period_six_iff` | `BinaryLynessPeriods.Theorems` | Exact power-of-two dichotomy: $(\forall x, y,\; F _ c^6(x, y) = (x, y)) \iff (c = 0 \lor \exists r,\; c = 2^r)$. |
| `orLynessStep_pow_two_period_twelve` | `BinaryLynessPeriods.Theorems` | Universal period $12$ of the bitwise-OR twin $H _ {2^r}(x, y) = (y,\; x \oplus (y \mathbin{|} (y + 2^r)))$ for all $r, x, y \in \mathbb{N}$. |

## 11. [`arx-fibonacci-isospectrality/`](arx-fibonacci-isospectrality/)

All statements are in [`arx-fibonacci-isospectrality/Challenge.lean`](arx-fibonacci-isospectrality/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`arx-fibonacci-isospectrality/ArxFibonacciIsospectrality/Defs.lean`](arx-fibonacci-isospectrality/ArxFibonacciIsospectrality/Defs.lean). See [`arx-fibonacci-isospectrality/README.md`](arx-fibonacci-isospectrality/README.md) for the 2-adic Jacobian lifting proof and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `xor_add_pow_two_mod` | `ArxFibonacciIsospectrality.Theorems` | Exact 2-adic perturbation law $((y + 2^r) \oplus c) \equiv (y \oplus c) + \sigma _ r \cdot 2^r \pmod{2^{r+2}}$ where $\sigma _ r = 3$ if bit $r$ of $c$ is $1$ else $1$. |
| `arxFibStep_fixed_point_iff` | `ArxFibonacciIsospectrality.Theorems` | Unique fixed point characterization: $G _ {c,m}(x, y) = (x, y) \iff (x = c \bmod 2^m \land y = c \bmod 2^m)$ for $m \ge 1, x, y < 2^m$. |
| `arxFibStep_exact_minPeriod` | `ArxFibonacciIsospectrality.Theorems` | Exact minimal period $3 \cdot 2^{m - 1 - r _ 0}$ for every non-fixed $(x, y)$ first differing from $(c, c)$ at bit $r _ 0 < m$. |
| `arxFibStep_isospectral_bijection` | `ArxFibonacciIsospectrality.Theorems` | Exact key-invariant cycle spectrum: $(x, y) \mapsto (x \oplus (c \bmod 2^m),\; y \oplus (c \bmod 2^m))$ preserves exact minimal periods between $G _ {c,m}$ and $G _ {0,m}$. |
| `arxFibStep3_breaks_isospectrality` | `ArxFibonacciIsospectrality.Theorems` | Contrast witness for $3x + (y \oplus c)$ at $m = 2$: $H _ {1,2}^3 = \mathrm{id}$ on $\{0..3\}^2$ while $(0, 1)$ has exact minimal period $6$ under $H _ {0,2}$. |
