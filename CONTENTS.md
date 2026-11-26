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

## 12. [`grh-ultra-compact-lean/`](grh-ultra-compact-lean/)

All five headline statements are fixed in [`grh-ultra-compact-lean/src/Statements.lean`](grh-ultra-compact-lean/src/Statements.lean) (importing only Mathlib) and [`grh-ultra-compact-lean/Challenge.lean`](grh-ultra-compact-lean/Challenge.lean), and proved in [`grh-ultra-compact-lean/src/Main.lean`](grh-ultra-compact-lean/src/Main.lean) (derived from `lsernau/grh-lean/grh-compact`; see [`grh-ultra-compact-lean/NOTICE`](grh-ultra-compact-lean/NOTICE) and [`grh-ultra-compact-lean/README.md`](grh-ultra-compact-lean/README.md)).

| Theorem | Module | Statement |
|---|---|---|
| `riemannHypothesis` | `Main` | Mathlib's `RiemannHypothesis`: every nontrivial zero of $\zeta(s)$ satisfies $\mathrm{Re}(s) = 1/2$. |
| `riemannZeta_eq_zero_re` | `Main` | Every zero $s \neq 1$ of `riemannZeta` outside the trivial negative even integers satisfies $\mathrm{Re}(s) = 1/2$. |
| `LFunction_ne_zero_of_half_lt_re` | `Main` | For every modulus $N \ge 1$ and Dirichlet character $\chi \pmod N$, $L(s, \chi) \neq 0$ for $\mathrm{Re}(s) > 1/2$ (excluding $s = 1$ for principal $\chi$). |
| `LFunction_eq_zero_re` | `Main` | Every zero of $L(s, \chi)$ in the critical strip $0 < \mathrm{Re}(s) < 1$ satisfies $\mathrm{Re}(s) = 1/2$. |
| `LFunction_eq_zero_re_of_isPrimitive` | `Main` | Critical-strip zero localization $\mathrm{Re}(s) = 1/2$ specialized to primitive Dirichlet characters $\chi$. |

## 13. [`sparse-e2m1-rotations/`](sparse-e2m1-rotations/)

All statements are in [`sparse-e2m1-rotations/Challenge.lean`](sparse-e2m1-rotations/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`sparse-e2m1-rotations/SparseE2M1Rotations/Defs.lean`](sparse-e2m1-rotations/SparseE2M1Rotations/Defs.lean). See [`sparse-e2m1-rotations/README.md`](sparse-e2m1-rotations/README.md) for the Kronecker algebraic proofs, GPU SNR benchmarks, and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `walshHadamard_doubly24_factorization` | `SparseE2M1Rotations.Theorems` | Universal 2-factor doubly-2:4-sparse $\{-1, 0, 1\}$ orthogonal factorization $(H _ {2^k} \otimes B _ 1)(I _ {2^k} \otimes B _ 2) = H _ {4 \cdot 2^k}$ for all $k \in \mathbb{N}$. |
| `single24_coherence_lower_bound` | `SparseE2M1Rotations.Theorems` | Universal single-2:4-sparse coherence lower bound $2c \le (4m) M^2$ for every row-2:4-sparse orthogonal $(4m) \times (4m)$ integer matrix. |
| `walsh_weighing_attains_coherence_bound` | `SparseE2M1Rotations.Theorems` | Exact attainment of the single-2:4 coherence bound for all $k \in \mathbb{N}$ by $W _ {4 \cdot 2^k} = H _ {2^k} \otimes B _ 1$. |
| `skewConference_e2m1_orthogonal` | `SparseE2M1Rotations.Theorems` | Universal skew-conference orthogonality $(a I + C)^T (a I + C) = (a^2 + n - 1) I$ with doubled-E2M1 entry preservation. |
| `q32_pow2_e2m1_exact` | `SparseE2M1Rotations.Theorems` | Exact power-of-2 dense E2M1-native $32 \times 32$ rotation $Q _ {32} = H _ 4 \otimes (I _ 8 + 3 C _ 8)$ with $Q _ {32}^T Q _ {32} = 16^2 I _ {32}$. |
| `q16_skew41_e2m1_exact` | `SparseE2M1Rotations.Theorems` | Exact NVFP4 winner $Q _ {16} = 4 I _ {16} + C _ {16}$ with $Q _ {16}^T Q _ {16} = 31 I _ {16}$ and entries in $\{-1, 1, 4\} \subset 2\cdot\mathrm{E2M1}$. |
| `g4k_doubly24_e2m1_orthogonal` | `SparseE2M1Rotations.Theorems` | Universal single doubly-2:4-sparse E2M1-native orthogonal family $G _ {4 \cdot 2^k}(1, 2) = H _ {2^k} \otimes G _ 4(1, 2)$ with $Q^T Q = (5 \cdot 2^k) I$. |

## 14. [`muon-vertex-polar/`](muon-vertex-polar/)

All statements are in [`muon-vertex-polar/Challenge.lean`](muon-vertex-polar/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`muon-vertex-polar/MuonVertexPolar/Defs.lean`](muon-vertex-polar/MuonVertexPolar/Defs.lean). See [`muon-vertex-polar/README.md`](muon-vertex-polar/README.md) for the Bernstein polynomial certification engine and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `shifted_square_equiv_monomial` | `MuonVertexPolar.Algebra` | Exact algebraic vertex-form identity $a x + b x^3 + c x^5 = x(\alpha + c(x^2 - \mu)^2)$ over $\mathbb{Q}$ for $c \ne 0$. |
| `shifted_square_quadratic_error_at_one` | `MuonVertexPolar.Algebra` | Exact quadratic Gram rounding-error annihilation $\beta(a - 1)^2 = \beta\delta _ 1^2 \le \beta u^2$ vs monomial linear error $(b + 2c)\delta _ 1 + c\delta _ 1^2$. |
| `noisyShiftedStep_envelope` | `MuonVertexPolar.Algebra` | Exact pointwise degree-5 upper and lower envelopes for the 6-rounding-point `NoisyShiftedStep` model. |
| `bf16_stationary_shifted_certified` | `MuonVertexPolar.Certificates` | Certified 5-step confinement of $[1/100, 1]$ into $[942/1000, 1052/1000]$ for drop-in BF16 stationary $(31/32, 199/128, 135/128)$ at $u = 1/256$. |
| `bf16_dp5_shifted_certified` | `MuonVertexPolar.Certificates` | Certified 5-step confinement of $[1/100, 1]$ into $[987/1000, 1013/1000]$ ($\delta \le 0.013$) for BF16 shifted-square DP at $u = 1/256$. |
| `fp8_pure_dp5_shifted_certified` | `MuonVertexPolar.Certificates` | Certified 5-step confinement of $[1/100, 1]$ into $[31/100, 165/100]$ for pure FP8 E4M3 ($u = 1/16$) shifted-square DP. |
| `fp8_hybrid_dp5_shifted_certified` | `MuonVertexPolar.Certificates` | Certified 5-step confinement of $[1/100, 1]$ into $[824/1000, 1163/1000]$ ($\delta \le 0.176$) for hybrid FP8 ($u = 1/32$) shifted-square DP. |

## 15. [`ternary-lop3-circuits/`](ternary-lop3-circuits/)

All statements are in [`ternary-lop3-circuits/Challenge.lean`](ternary-lop3-circuits/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`ternary-lop3-circuits/TernaryLop3Circuits/Defs.lean`](ternary-lop3-circuits/TernaryLop3Circuits/Defs.lean). See [`ternary-lop3-circuits/README.md`](ternary-lop3-circuits/README.md) for gate-count lower bounds, RX 7900 XTX throughput benchmarks, and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `unpack_3t5b_sound_and_surjective` | `TernaryLop3Circuits.Theorems` | Disjointness on `Fin 32` and 27/27 surjectivity outside the 4-codeword escape cube for the 6-`LOP3` depth-2 3-trit/5-bit unpacker. |
| `unpack_3t5b_six_gate_lower_bound` | `TernaryLop3Circuits.Theorems` | Exact pigeonhole lower bound: every surjective disjoint 3-trit/5-bit decoder has $\ge 9$ true and $\ge 18$ false inputs per lane, barring any direct input literal ($18 > 16$). |
| `unpack_5t8b_sound_and_surjective` | `TernaryLop3Circuits.Theorems` | Disjointness on `Fin 256` and 243/243 surjectivity via explicit right-inverse encoder for the 14-`LOP3` depth-4 5-trit/8-bit unpacker. |
| `unpack_5t8b_four_var_impossibility` | `TernaryLop3Circuits.Theorems` | Exact lower bound: no output bit of any surjective disjoint 5-trit/8-bit decoder can depend on $\le 4$ input bits (weight $\in [81, 94]$ vs $16 \mid w$). |
| `ternary_int4_exact5_sound` | `TernaryLop3Circuits.Theorems` | Soundness of the 9-`LOP3` ternary $\times$ signed INT4 $[-8, 7]$ offset product ($+ 8$), plus $Y _ 4 = 0$ identically on symmetric $[-7, 7]$. |
| `ternary_fp4_exact5_sound` | `TernaryLop3Circuits.Theorems` | Soundness of the 4+10-`LOP3` zero-FP-op, zero-offset ternary $\times$ FP4 (E2M1) product over all 16 E2M1 codes. |
| `csa32_popcnt_conservation` | `TernaryLop3Circuits.Theorems` | Universal 3:2 Carry-Save-Adder `popcnt` conservation for all $a, b, c \in \mathbb{N}$. |

## 16. [`ef21-ternary-contraction/`](ef21-ternary-contraction/)

All statements are in [`ef21-ternary-contraction/Challenge.lean`](ef21-ternary-contraction/Challenge.lean) against Mathlib definitions in [`ef21-ternary-contraction/EF21Ternary/Defs.lean`](ef21-ternary-contraction/EF21Ternary/Defs.lean). See [`ef21-ternary-contraction/README.md`](ef21-ternary-contraction/README.md) for the Abel-summation proofs, multi-regime MXFP4/NVFP4 phase diagrams, and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `ternary_ef21_contraction_exact` | `EF21Ternary.Ternary` | Universal optimal ternary EF21 contraction law $\alpha _ {\mathrm{tern}}(d) = (\sum _ {i=0}^{d-1} (\sqrt{i+1} - \sqrt{i})^2)^{-1}$ and exact tightness at $w _ i = \sqrt{i+1} - \sqrt{i}$ for all $d \ge 1$. |
| `alphaTern_harmonic_sandwich` | `EF21Ternary.Ternary` | Exact harmonic sandwich $4 / (4 + H _ {d-1}) \le \alpha _ {\mathrm{tern}}(d) \le 4 / (3 + H _ d)$ for all $d \ge 1$. |
| `mxfp4_nvfp4_ef21_contraction_universal` | `EF21Ternary.FP4` | Exact universal multi-regime EF21 contraction laws and tightness/attainment for OCP E2M1 MXFP4 (3 regimes) and NVFP4 (2 regimes) for all $B \ge 1$. |
| `symmetric_2bit_no_zero_collapse` | `EF21Ternary.TwoBitAndSR` | Exact zero-omission EF21 collapse $\alpha \le 9 / (d + 8)$ and attainment at $\gamma = 3 / (d + 8)$ on $e _ 0$ for symmetric 2-bit $\{\pm\mu, \pm 3\mu\}$ for all $d \ge 1$. |
| `mantissa_sr_variance_law` | `EF21Ternary.TwoBitAndSR` | Exact worst-case relative variance $1 / (4 \cdot 2^m (2^m + 1))$ and attainment at $t^* = 2^m / (2 \cdot 2^m + 1)$ for $m$-bit mantissa stochastic rounding for all $m \in \mathbb{N}$. |

## 17. [`subbyte-e2m1-lop3/`](subbyte-e2m1-lop3/)

All statements are in [`subbyte-e2m1-lop3/Challenge.lean`](subbyte-e2m1-lop3/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`subbyte-e2m1-lop3/SubbyteE2M1Lop3/Defs.lean`](subbyte-e2m1-lop3/SubbyteE2M1Lop3/Defs.lean). See [`subbyte-e2m1-lop3/README.md`](subbyte-e2m1-lop3/README.md) for the circuit constructions, Hamming-weight lower bounds, and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `unpack_2t4b_to_e2m1_zero_lop3` | `SubbyteE2M1Lop3.Theorems` | Exact 0-`LOP3` pure bit-wire 2-trit/4-bit $\to$ E2M1 unpacker covering all $9$ ternary pairs. |
| `unpack_3t5b_to_e2m1_four_lop3` | `SubbyteE2M1Lop3.Theorems` | Exact 4-`LOP3` (`0x73`, `0xC7`, `0x3B`, `0x71`) 3-trit/5-bit $\to$ E2M1 unpacker covering all $27$ ternary triples. |
| `unpack_3t5b_to_e2m1_three_gate_lower_bound` | `SubbyteE2M1Lop3.Theorems` | General $\ge 3$-`LOP3` lower bound for any surjective 3-trit/5-bit $\to$ E2M1 decoder ($w(f _ i) \in [18, 23]$ vs $8 \mid w(g)$). |
| `quinary_3w7b_five_var_impossibility` | `SubbyteE2M1Lop3.Theorems` | General $\ge 5$-variable support barrier (`LOP3` depth $\ge 2$) for any surjective 3-quinary/7-bit decoder ($w \in [25k, 25k + 3] \implies 8 \nmid w$). |
| `asymmetric_2bit_polarity_flip_exact` | `SubbyteE2M1Lop3.Theorems` | Bijective 2-bit asymmetric `{-2, -1, 0, +1}` $\leftrightarrow$ `{-1, 0, +1, +2}` signed-scale duality and universal 2-plane dot-product identity. |
| `compressor_4to2_lop3_depth_inversion` | `SubbyteE2M1Lop3.Theorems` | 5-input parity of any 4:2 compressor requires `LOP3` depth $\ge 2$, while 3:2 CSA (`0x96`, `0xE8`) is exact in 2 `LOP3` gates at depth $1$. |

## 18. [`soap-vertex-fourth-root/`](soap-vertex-fourth-root/)

All statements are in [`soap-vertex-fourth-root/Challenge.lean`](soap-vertex-fourth-root/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`soap-vertex-fourth-root/SoapVertexFourthRoot/Defs.lean`](soap-vertex-fourth-root/SoapVertexFourthRoot/Defs.lean). See [`soap-vertex-fourth-root/README.md`](soap-vertex-fourth-root/README.md) for the cleared-denominator `Int` interval verification engine and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `vertex_fourth_root_equiv_monomial` | `SoapVertexFourthRoot.Algebra` | Exact completed-square identity $a + b m + c m^2 = (a - b^2/(4c)) + c(m + b/(2c))^2$ over $\mathbb{Q}$ ($c \ne 0$) and global positivity $\beta \ge 0 \implies \alpha \le \alpha + \beta(m - \mu)^2$. |
| `taylor2_fourth_root_vertex_exact` | `SoapVertexFourthRoot.Algebra` | Exact Taylor-2 vertex form $9/10 + (5/32)(m - 9/5)^2 \ge 9/10$ and cubic coupled residual $m P(m)^4 - 1 = (m - 1)^3 R(m)$. |
| `noisyFourthRootStep_envelope` | `SoapVertexFourthRoot.Algebra` | Exact pointwise adversarial upper and lower envelopes for 7-rounding-point `NoisyVertexStep4` and 5-rounding-point `NoisyLinearStep4`. |
| `bf16_fourth_root_dp5_certified` | `SoapVertexFourthRoot.Certificates` | Certified 5-step confinement of $[1/100, 1]$ into $[965/1000, 1039/1000]$ for BF16 (`u = 1/256`) vertex DP `inv4_vertex_bf16_e2`. |
| `bf16_fourth_root_eps1e4_certified` | `SoapVertexFourthRoot.Certificates` | Certified 5-step confinement of $[1/10000, 1]$ into $[935/1000, 1049/1000]$ for BF16 (`u = 1/256`) vertex DP `inv4_vertex_bf16_e4`. |
| `fp8_hybrid_fourth_root_dp5_certified` | `SoapVertexFourthRoot.Certificates` | Certified 5-step confinement of $[1/100, 1]$ into $[652/1000, 1329/1000]$ for hybrid FP8 (`u = 1/32`) vertex DP `inv4_vertex_fp8hyb_e2`. |
| `fp8_pure_fourth_root_linear_dp5_certified` | `SoapVertexFourthRoot.Certificates` | Certified 5-step confinement of $[1/100, 1]$ into $[257/1000, 1654/1000]$ for pure FP8 E4M3 (`u = 1/16`) linear crossover `inv4_linear_fp8_e2`. |

## 19. [`universal-vertex-invroot/`](universal-vertex-invroot/)

All statements are in [`universal-vertex-invroot/Challenge.lean`](universal-vertex-invroot/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`universal-vertex-invroot/UniversalVertexInvroot/Defs.lean`](universal-vertex-invroot/UniversalVertexInvroot/Defs.lean). See [`universal-vertex-invroot/README.md`](universal-vertex-invroot/README.md) for the universal all-$p$ proofs, BF16 certificates, and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `universal_invroot_vertex_identity_and_positivity` | `UniversalVertexInvroot.Algebra` | Universal all-$p$ ($\forall p \ge 1, m \in \mathbb{Q}$) vertex identity $T _ {2,p}(m) = P _ p(m) \ge \frac{2p+1}{2p+2} \ge \frac{3}{4}$, exact monomial expansion, $\kappa _ {\mathrm{mono}}(p) = 1 + 4/p + 2/p^2$, and $\kappa _ {\mathrm{sum}} = 1$. |
| `universal_invroot_cubic_convergence` | `UniversalVertexInvroot.Algebra` | Universal all-$p$ cubic convergence $m P _ p(m)^p - 1 = (m - 1)^3 R _ p(m - 1)$ with exact leading constant $R _ p(0) = (p+1)(2p+1)/(6p^2)$. |
| `deg9_shared_square_and_rounding_floor_dominance` | `UniversalVertexInvroot.Algebra` | Exact 4-matmul degree-9 shared-square identity, $5^4 < 9^3$, universal $(1+u)^6 < (1+u)^{10}$, and $> 1.65\times$ degree-9 rounding-floor penalty across BF16 and FP8. |
| `bf16_inv_sqrt_vertex_certified` | `UniversalVertexInvroot.Certificates` | Certified 6-step BF16 (`u = 1/256`) stationary confinement of $[85/100, 115/100]$ into $[982/1000, 1018/1000]$ for $G^{-1/2}$. |
| `bf16_inv_cbrt_vertex_certified` | `UniversalVertexInvroot.Certificates` | Certified 6-step BF16 (`u = 1/256`) stationary confinement of $[85/100, 115/100]$ into $[974/1000, 1026/1000]$ for $G^{-1/3}$. |
| `bf16_inv_eighth_vertex_certified` | `UniversalVertexInvroot.Certificates` | Certified 6-step BF16 (`u = 1/256`) stationary confinement of $[85/100, 115/100]$ into $[932/1000, 1068/1000]$ for $G^{-1/8}$. |

## 20. [`sparse24-e2m1-lop3/`](sparse24-e2m1-lop3/)

All statements are in [`sparse24-e2m1-lop3/Challenge.lean`](sparse24-e2m1-lop3/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`sparse24-e2m1-lop3/Sparse24E2M1Lop3/Defs.lean`](sparse24-e2m1-lop3/Sparse24E2M1Lop3/Defs.lean). See [`sparse24-e2m1-lop3/README.md`](sparse24-e2m1-lop3/README.md) for the GPU-synthesized `LOP3` circuits, lower bounds, and prior-art context.

| Theorem | Module | Statement |
|---|---|---|
| `unpack_5t8b_to_e2m1_ten_lop3_and_lower_bound` | `Sparse24E2M1Lop3.Theorems` | Exact 10-`LOP3` direct-sign `5t8b → 5×E2M1` (`243/243`) + general Hamming-weight barrier $162 \le w(f _ i) \le 175$ vs $16 \mid w(g)$ ($\ge 5$ essential vars, depth $\ge 2$). |
| `sparse24_3bit_single_lop3_tight` | `Sparse24E2M1Lop3.Theorems` | Tight 1-`LOP3` (`0x17`) `3b → 4b` 2:4 mask bijection + 0-`LOP3` impossibility, and 1-`LOP3` (`0x63`) `3b → unordered {idx0, idx1}`. |
| `sparse24_3bit_ordered_three_lop3_tight` | `Sparse24E2M1Lop3.Theorems` | Tight 3-`LOP3` (`0x08`, `0x2D`, `0x3E`) `3b → ordered (idx0 < idx1)` bijection + $\le 1$-wire impossibility ($\ge 3$ `LOP3`). |
| `sparse24_8bit_triple_twelve_lop3_and_wire_bound` | `Sparse24E2M1Lop3.Theorems` | Exact 12-`LOP3` `8b → 3×4b` 2:4 mask unpacker (`216/216`) + unique $(1, 1, 1)$ fiber-product direct-wire theorem ($6^3 = 2^3 \times 3^3$). |
| `e2m1_mag_mul_25lop3_exact` | `Sparse24E2M1Lop3.Theorems` | Exact 25-`LOP3` zero-FP `E2M1 × E2M1` magnitude multiplier (`64/64` exact products in `[0, 144]`). |
| `quinary_2w5b_to_e2m1_four_lop3_and_wire_bound` | `Sparse24E2M1Lop3.Theorems` | Exact 4-`LOP3` depth-2 `2q5b → 2×E2M1` (`25/25`) + 4-wire impossibility theorem ($\ge 3$ `LOP3`). |

## 21. [`octonion-rope-welch-frames/`](octonion-rope-welch-frames/)

All statements are in [`octonion-rope-welch-frames/Challenge.lean`](octonion-rope-welch-frames/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`octonion-rope-welch-frames/OctonionRopeWelch/Defs.lean`](octonion-rope-welch-frames/OctonionRopeWelch/Defs.lean). See [`octonion-rope-welch-frames/README.md`](octonion-rope-welch-frames/README.md) for the 4D rigidity descent, octonion RoPE, Welch-tight ternary frames, and Softmax $\ell _ 1$ proofs.

| Theorem | Module | Statement |
|---|---|---|
| `quaternion_pow2_rigidity_obstruction` | `OctonionRopeWelch.Rigidity` | Universal mod-8 4-square descent ($r \ge 3 \implies 0$ primitive solutions) + exact $r _ 4(2^r) = 24$ Hurwitz classification for all $r \ge 1$. |
| `pythagorean_and_octonion_rope_exact_orthogonal` | `OctonionRopeWelch.RoPE` | Universal exact orthogonality of 2D Pythagorean, 4D Hamilton quaternion, and 8D Cayley–Dickson octonion RoPE + `>> 16` Llama-2 witness ($\sum x _ i^2 = 2^{32}$). |
| `welch_frame_energy_lower_bound` | `OctonionRopeWelch.Welch` | Universal integer Welch Frobenius lower bound $m(d s^2 + \Phi(S)) \ge (d s)^2$ and $m\,\Phi(S) \ge d s^2 (d - m)$. |
| `welch_tight_sparse_ternary_frames_exact` | `OctonionRopeWelch.Welch` | Exact certification of 5 GPU-discovered sparse ternary frames (`(8,16) s∈{3,4,5}`, `(12,24) s∈{3,4}`) attaining exact Welch equality (`ratio = 1.00000`, zero muls). |
| `softmax_topk_gap_l1_exact` | `OctonionRopeWelch.Softmax` | Exact tight Softmax Top-$K$ (Gap-$\Delta$) $\ell _ 1$ bound $\|p - q\| _ 1 = \frac{2T}{H+T} \le \frac{2(N-K)}{K E + (N-K)}$ + exact sharpness witness. |
| `softmax_quantized_logit_l1_exact` | `OctonionRopeWelch.Softmax` | Exact tight quantized-logit ($\pm\epsilon$) Softmax $\ell _ 1$ bound $\|p - p'\| _ 1 \le \frac{2(R-1)}{R+1}$ + exact sharpness witness for all $N \ge 2$. |

## 22. [`moe-bias-placement-codes/`](moe-bias-placement-codes/)

All statements are in [`moe-bias-placement-codes/Challenge.lean`](moe-bias-placement-codes/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`moe-bias-placement-codes/MoeBiasPlacement/Defs.lean`](moe-bias-placement-codes/MoeBiasPlacement/Defs.lean). See [`moe-bias-placement-codes/README.md`](moe-bias-placement-codes/README.md) for the bias-drift, dead-zone, BIBD placement, EPLB, and router-quantization proofs.

| Theorem | Module | Statement |
|---|---|---|
| `aux_loss_free_mean_bias_drift_exact` | `MoeBiasPlacement.BiasDynamics` | Exact aux-loss-free sign-bias drift bound $|\frac{1}{E}\sum \delta _ i| \le \frac{E-2}{E}\gamma$ and exact mean-centered zero-drift invariance. |
| `dead_zone_fixed_point_threshold_exact` | `MoeBiasPlacement.BiasDynamics` | Sharp dead-zone fixed-point phase transition at $\tau _ {\min} = \max(r, E - r)/E$: zero fixed points for $\tau < \tau _ {\min}$, balanced attainment at $\tau = \tau _ {\min}$. |
| `fanout_intra_gpu_dispersion_duality` | `MoeBiasPlacement.PlacementCodes` | Universal discrete-convexity duality linking cross-GPU routing fanout and intra-GPU pair dispersion. |
| `affine_plane_ag2_zero_hotspot_placement` | `MoeBiasPlacement.PlacementCodes` | Explicit resolvable affine-plane BIBD placement codes $AG(2, 4)$ ($E = 16, G = 4$) and $AG(2, 8)$ ($E = 64, G = 8$) with zero pair-collision hotspots. |
| `eplb_redundant_expert_pigeonhole_bound` | `MoeBiasPlacement.PlacementCodes` | Universal EPLB redundant-expert pigeonhole capacity lower bound for all expert counts and replication budgets. |
| `quantized_router_zero_flip_thresholds` | `MoeBiasPlacement.QuantizedRouter` | Exact uniform and floating-point quantized-router zero-flip margin thresholds preserving top-$K$ expert selection. |

## 23. [`mxfp6-ef21-rotations/`](mxfp6-ef21-rotations/)

All statements are in [`mxfp6-ef21-rotations/Challenge.lean`](mxfp6-ef21-rotations/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`mxfp6-ef21-rotations/Mxfp6Ef21Rotations/Defs.lean`](mxfp6-ef21-rotations/Mxfp6Ef21Rotations/Defs.lean). See [`mxfp6-ef21-rotations/README.md`](mxfp6-ef21-rotations/README.md) for the universal MXFP6/NVFP6 EF21 phase diagrams, crossovers, and E2M1-native Goethals–Seidel rotations.

| Theorem | Module | Statement |
|---|---|---|
| `mxfp6_e3m2_nvfp6_ef21_universal` | `Mxfp6Ef21Rotations.EF21Universal` | Universal all-$B$ ($\forall B \ge 1$) EF21 contraction bounds with exact tightness for `MXFP6-E3M2` and exact attainment for `NVFP6-E3M2`. |
| `mxfp6_e2m3_nvfp6_ef21_universal` | `Mxfp6Ef21Rotations.EF21Universal` | Universal all-$B$ ($\forall B \ge 1$) EF21 contraction bounds with exact tightness for `MXFP6-E2M3` and exact attainment for `NVFP6-E2M3`. |
| `mxfp6_e2m3_vs_e3m2_exact_crossover` | `Mxfp6Ef21Rotations.EF21Universal` | Sharp hardware crossover: `E2M3 > E3M2` for $1 \le B \le 43$ vs `E3M2 > E2M3` for $B \ge 44$ (OCP MXFP6), and $2 \le B \le 178$ vs $B \ge 179$ (NVFP6). |
| `hadamard_weight_quantization_defect_and_min_dyadic_coherence` | `Mxfp6Ef21Rotations.Rotations` | Exact quantized Hadamard defects $9/8$ ($n = 8$) and $121/128$ ($n = 32$) + sharp minimum dyadic coherence bounds. |
| `goethals_seidel_native_e2m1_orthonormal_exact` | `Mxfp6Ef21Rotations.Rotations` | Exact `G^T G = 64 I` for `16 × 16` and zero-free `32 × 32` Goethals–Seidel matrices with every entry exact in `E2M1 ∩ E3M2 ∩ E2M3`. |
| `quaternion_4of8_sparse_orthogonality_universal` | `Mxfp6Ef21Rotations.Rotations` | Universal Hamilton 4-square orthogonality and multi-stage 4:8-sparse orthogonal closure in arbitrary $4m$ dimensions. |

## 24. [`bitnet-contraction-hierarchy/`](bitnet-contraction-hierarchy/)

All statements are in [`bitnet-contraction-hierarchy/Challenge.lean`](bitnet-contraction-hierarchy/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`bitnet-contraction-hierarchy/BitnetContraction/Defs.lean`](bitnet-contraction-hierarchy/BitnetContraction/Defs.lean). See [`bitnet-contraction-hierarchy/README.md`](bitnet-contraction-hierarchy/README.md) for the three-tier BitNet contraction hierarchy, multi-level $d _ {\mathrm{crit}}$ phase transition, and 2-stage crossover.

| Theorem | Module | Statement |
|---|---|---|
| `ternary_nearest_nonneg_contraction` | `BitnetContraction.TernaryNonneg` | Universal nonnegative ternary contraction $\|x - Q _ \gamma(x)\| _ 2^2 \le \|x\| _ 2^2$ and exact tie-break invariance (`≥` vs `>`) for all $d, \gamma \ge 0, x$. |
| `bitnet_absmean_contraction_exact` | `BitnetContraction.BitnetHierarchy` | Exact `AbsMean` contraction $(2d - 1)/d^2$ for all $d \ge 1$ with exact attainment on `unitE0 d`. |
| `bitnet_absmax_and_half_contraction_exact` | `BitnetContraction.BitnetHierarchy` | Exact `AbsMax` ($4/(d + 3)$) and `AbsMax/2` ($12/(d + 15)$) contraction bounds for all $d \ge 1$ with exact attainment. |
| `bitnet_rms_contraction_exact_algebraic` | `BitnetContraction.BitnetHierarchy` | Universal `RMS` algebraic contraction law $3d + 1 \le (d\alpha + 1)^2$ ($\Theta(1/\sqrt{d})$) with exact rational attainment at $d = 8, 16$. |
| `multilevel_shifted_sqrt_dcrit_exact` | `BitnetContraction.MultilevelDCrit` | Universal integer sandwich $(4M^2 + 1)^2 < 16M^2(M^2 + 1) < (4M^2 + 2)^2$ and exact critical dimension $d _ {\mathrm{crit}}(M) = 8M^2 + 4$ (`36`, `76`, `396`). |
| `two_stage_ternary_greedy_vs_disjoint_crossover` | `BitnetContraction.TwoStageCrossover` | Exact $d = 3$ vs $d = 4$ 2-stage ternary crossover where Greedy beats Joint Disjoint at $d = 3$ and reverses at $d = 4$. |

## 25. [`spec-decoding-ot-bounds/`](spec-decoding-ot-bounds/)

All statements are in [`spec-decoding-ot-bounds/Challenge.lean`](spec-decoding-ot-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`spec-decoding-ot-bounds/SpecDecodingOt/Defs.lean`](spec-decoding-ot-bounds/SpecDecodingOt/Defs.lean). See [`spec-decoding-ot-bounds/README.md`](spec-decoding-ot-bounds/README.md) for the multi-draft OT gaps, Cyclic Madow refutation, quantized-draft loss laws, and reversible Transformer proofs.

| Theorem | Module | Statement |
|---|---|---|
| `multidraft_corr_vs_iid_exact_gaps` | `SpecDecodingOt.MultidraftOT` | Universal correlated-vs-i.i.d. multi-draft OT multiplicative gap $K^K / (K^K - (K - 1)^K)$ and additive gap $((K - 1)/K)^K$ for all $K \ge 1, V$ with attainment. |
| `cyclic_madow_optimality_refutation_exact` | `SpecDecodingOt.MultidraftOT` | Exact $K = 2, V = 4$ counterexamples refuting both default-order ($1/2 < 3/4 < 1$) and oracle descending-$p / q$-sorted ($17/20 < 91/100 < 1$) Cyclic Madow optimality. |
| `quantized_draft_loss_k1_exact` | `SpecDecodingOt.QuantizedDraft` | Universal tight single-draft ($K = 1$) quantized-draft acceptance loss $|\alpha _ 1(p, q) - \alpha _ 1(p, q')| \le (R - 1)/(R + 1)$ for all $V \ge 2, R \ge 1$. |
| `quantized_draft_loss_multidraft_exact` | `SpecDecodingOt.QuantizedDraft` | Universal tight correlated multi-draft ($K \ge 2$) quantized-draft acceptance loss $\alpha _ K^{\mathrm{corr}}(p, q) - \alpha _ K^{\mathrm{corr}}(p, q') \le \frac{(K - 1)(R^2 - 1)}{1 + (K - 1)R^2}$. |
| `modular_bitvec_reversible_exact_inverse` | `SpecDecodingOt.ReversibleBitVec` | Exact bidirectional invertibility `revPass ∘ fwdPass = id ∧ fwdPass ∘ revPass = id` of modular `BitVec b` reversible Transformers for all $b, L$. |
| `symplectic_float_reversible_unimodular` | `SpecDecodingOt.ReversibleBitVec` | Exact unimodularity $\det M(\gamma)^n = 1$ and exponential growth $(M(\gamma)^n) _ {0,0} + (M(\gamma)^n) _ {0,1} \ge (1 + \gamma)^n$ for floating-point reversible coupling. |

## 26. [`deltanet-wy-stability/`](deltanet-wy-stability/)

All statements are in [`deltanet-wy-stability/Challenge.lean`](deltanet-wy-stability/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`deltanet-wy-stability/DeltanetWyStability/Defs.lean`](deltanet-wy-stability/DeltanetWyStability/Defs.lean). See [`deltanet-wy-stability/README.md`](deltanet-wy-stability/README.md) for the spectral stability, MXFP4 blowup, WY inverse, Euler binomial explosion, and Block-Schur proofs.

| Theorem | Module | Statement |
|---|---|---|
| `deltanet_spectral_stability_iff` | `DeltanetWyStability.SpectralStability` | Universal rational spectral stability `iff` law: `∀ v, ‖T(v)‖² ≤ ‖v‖² ↔ β‖k‖² ≤ (1 + α)/α`. |
| `mxfp4_mxfp6_fp8_bf16_norm_blowup_and_beta_safe` | `DeltanetWyStability.QuantNormBlowup` | Exact subnormal-inclusive OCP MXFP4 (`700/431`, `β _ {\mathrm{safe}} = 431/350`), max-fit MXFP4 (`380/227`), and universal $m$-bit normal-range squared-norm blowup laws. |
| `wy_inverse_closed_form_and_aligned_contraction` | `DeltanetWyStability.WyInverse` | Universal chunkwise WY inverse $(I + L) T = I$, aligned contraction `|T _ {ij}| ≤ β r`, and exact quantized blowup $2r(2r - 1)^{C-2}$. |
| `euler_product_binomial_peak_explosion` | `DeltanetWyStability.EulerBinomial` | Exact binomial power law $(L _ C^k) _ {i,j} = \beta^k \binom{i - j - 1}{k - 1}$ certifying Euler-product intermediate peaks $> 10^{27}$ at $C = 64, \beta = 2$. |
| `block_schur_wy_exact_inverse` | `DeltanetWyStability.BlockSchur` | Universal two-sided exact 2×2 Block-Schur inverse for all $(n + m) \times (n + m)$ block lower-triangular matrices. |

## 27. [`muonclip-adamw-sr-bounds/`](muonclip-adamw-sr-bounds/)

All statements are in [`muonclip-adamw-sr-bounds/Challenge.lean`](muonclip-adamw-sr-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`muonclip-adamw-sr-bounds/MuonclipAdamwSr/Defs.lean`](muonclip-adamw-sr-bounds/MuonclipAdamwSr/Defs.lean). See [`muonclip-adamw-sr-bounds/README.md`](muonclip-adamw-sr-bounds/README.md) for the MuonClip pitchfork phase transition, AdamW freeze radii, SR-EMA Markov chain, and Jensen bias proofs.

| Theorem | Module | Statement |
|---|---|---|
| `muonclip_pitchfork_symmetry_breaking_exact` | `MuonclipAdamwSr.MuonClip` | Exact $r = 1$ quartic factorization, SOS identity, unique optimality of $x = \sqrt{\gamma}$ for $\gamma \ge 1/4$, and strict local maximality + saving $A(1 - 2\sqrt{\gamma})^2$ for $0 < \gamma < 1/4$. |
| `muonclip_rtn_overshoot_vs_rtz_safety` | `MuonclipAdamwSr.MuonClip` | Exact RTN scale overshoot $(1 + 2^{-(m+1)})^2$ (`289/256` FP8, `66049/65536` BF16) vs universal RTZ safety $s' _ Q s' _ K S _ {\max} \le \tau$. |
| `adamw_weight_decay_freeze_radii_exact` | `MuonclipAdamwSr.AdamWFreeze` | Universal $m \ge 1$ RNE weight-decay freeze iff $\rho \le 2^{-(m+2)}$, pow2-only gap, and universal decay iff $\rho \ge 1/(2^{m+1} + 2)$. |
| `sr_ema_two_state_markov_exact` | `MuonclipAdamwSr.SrEmaJensen` | Exact 2-state SR-EMA Markov chain: zero bias, $\beta$-independent variance $r(\Delta - r)$, $\lambda _ 2 = \beta$, and time-average variance inflation $(1 + \beta)/(1 - \beta)$. |
| `preconditioner_jensen_bias_exact_sqrt_vs_v` | `MuonclipAdamwSr.SrEmaJensen` | Exact zero bias for `SR(1/√v)`, exact `9/8` max for `SR(√v)` on E4M0, and universal cubic SOS bound $27 r^2 (r + 1)^2 J _ v^2 \le 4(r^2 + r + 1)^3$ (`> 2.7x` smaller bias on E4M0). |
| `asymmetric_muonclip_ratio_limit_exact` | `MuonclipAdamwSr.MuonClip` | Universal small-clipping optimal split $\alpha^* = B / (A + B)$ with saving $((r - 1)/(r + 1))^2$ (`225/289` at $r = 16$) and strong-clipping ratio $(1 + s)^2 / (r + 1)$. |

## 28. [`fp8-e4m3-lop3-circuits/`](fp8-e4m3-lop3-circuits/)

All statements are in [`fp8-e4m3-lop3-circuits/Challenge.lean`](fp8-e4m3-lop3-circuits/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`fp8-e4m3-lop3-circuits/Fp8E4m3Lop3/Defs.lean`](fp8-e4m3-lop3-circuits/Fp8E4m3Lop3/Defs.lean). See [`fp8-e4m3-lop3-circuits/README.md`](fp8-e4m3-lop3-circuits/README.md) for the exact 0-ULP `LOP3` circuits, fan-in lower bounds, and RX 7900 XTX speedups.

| Theorem | Module | Statement |
|---|---|---|
| `fp8_e4m3_rsqrt_15_lop3_exact` | `Fp8E4m3Lop3.BitSlicedCircuits` | Exact 15-`LOP3` depth-8 positive `e4m3RsqrtPosDag` certified directly against the pure-integer RNE Voronoi law on all 126 positive finite codes. |
| `fp8_e4m3_rsqrt_full_33_lop3_exact` | `Fp8E4m3Lop3.BitSlicedCircuits` | Exact 33-`LOP3` full-domain `e4m3RsqrtFullDag` matching RNE on all 126 positive codes and returning `0x7F` on all 130 non-positive/NaN codes. |
| `fp8_e4m3_activations_lop3_exact` | `Fp8E4m3Lop3.BitSlicedCircuits` | Exact 0-ULP `LOP3` circuits over all 254 finite FP8-E4M3FN codes for `exp` (67 `LOP3`), `gelu` (82 `LOP3`, tight 1-`LOP3` $y _ 6$), and `silu` (93 `LOP3`, tight 0-`LOP3` $y _ 7$). |
| `fp8_e4m3_times_e2m1_28_lop3_exact` | `Fp8E4m3Lop3.E4m3E2m1Mul` | Exact 28-`LOP3` zero-FP `FP8-E4M3FN × FP4-E2M1` aligned product verified exhaustively over all `4,096` input pairs. |
| `fp8_e4m3_lop3_fanin_lower_bound` | `Fp8E4m3Lop3.LowerBounds` | Universal `LOP3` DAG gate-count and depth lower bounds $k \le 2g + 1$ and $k \le 3^d$, instantiated on `rsqrt`, `gelu`, and `silu`. |
| `fp8_e4m3_exact_dyadic_value_law` | `Fp8E4m3Lop3.Dyadic` | Universal OCP FP8-E4M3FN dyadic characterization (`448` max normal, $2^{-9}$ min subnormal, sign symmetry, strict monotonicity, exact 256-code partition). |

## 29. [`ternary-lop3-kulisch/`](ternary-lop3-kulisch/)

All statements are in [`ternary-lop3-kulisch/Challenge.lean`](ternary-lop3-kulisch/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`ternary-lop3-kulisch/TernaryLop3Kulisch/Defs.lean`](ternary-lop3-kulisch/TernaryLop3Kulisch/Defs.lean). See [`ternary-lop3-kulisch/README.md`](ternary-lop3-kulisch/README.md) for the minimal-`LOP3` counters, SWAR64 packing, and exact FP8 Kulisch theorems.

| Theorem | Module | Statement |
|---|---|---|
| `ternary_k2_4_lop3_exact_and_lb` | `TernaryLop3Kulisch.Lop3Circuits` | Exact 4-`LOP3` depth-3 $K = 2$ balanced-ternary counter (`9/9` valid states) + tight general-DAG lower bound `dag.length ≥ 4`. |
| `ternary_k3_7_lop3_exact` | `TernaryLop3Kulisch.Lop3Circuits` | Exact 7-`LOP3` depth-3 $K = 3$ balanced-ternary counter (`27/27` valid states) + general-DAG fan-in lower bound `dag.length ≥ 5`. |
| `harley_seal_n7_8_lop3_exact_and_lb` | `TernaryLop3Kulisch.Lop3Circuits` | Exact 8-`LOP3` depth-3 $N = 7$ Harley–Seal 7→3 compressor (`128/128` inputs) + general-DAG fan-in lower bound `dag.length ≥ 5`. |
| `fp8_e4m3_exact_kulisch_49bit_int64_theorem` | `TernaryLop3Kulisch.Kulisch` | Exact OCP FP8-E4M3 Kulisch law: 37-bit product span, exact `int64` accumulation for all $K \le 175{,}304{,}787$ (tight at `175,304,788`), 49 signed bits at $K = 4096$. |
| `swar64_ternary_int2_dot_zero_overflow` | `TernaryLop3Kulisch.Swar` | Universal SWAR64 lane-isolation and operand-offset unbiasing for ternary (`P = 6, S = 10, L ≤ 255`) and INT2 (`P = 5, S = 12, L ≤ 455`) with tightness counterexamples. |
| `fp8_e5m2_vs_e4m3_kulisch_width_gap` | `TernaryLop3Kulisch.Kulisch` | Exact 28-bit Kulisch width gap proving a single finite FP8-E5M2 product (`0x7B * 0x7B ≥ 2^{63}`) overflows `int64` at $K = 1$ (65 vs 37 bits). |

## 30. [`xor-vdc-fp4-dither/`](xor-vdc-fp4-dither/)

All statements are in [`xor-vdc-fp4-dither/Challenge.lean`](xor-vdc-fp4-dither/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`xor-vdc-fp4-dither/XorVdcFp4Dither/Defs.lean`](xor-vdc-fp4-dither/XorVdcFp4Dither/Defs.lean). See [`xor-vdc-fp4-dither/README.md`](xor-vdc-fp4-dither/README.md) for the Walsh–Hadamard diagonalization, E2M1 harmonic-mean variance, and double-GEMM proofs.

| Theorem | Module | Statement |
|---|---|---|
| `xor_vdc_sr_unbiased_and_covariance_exact` | `XorVdcFp4Dither.XorVdcCore` | Universal all-$b \le m$ unbiasedness and exact closed-form discrete pairwise covariance of zero-carry XOR-VDC dithering. |
| `xor_vdc_walsh_spectrum_and_trace_conservation` | `XorVdcFp4Dither.WalshSpectrum` | Universal all-$b$ Walsh–Hadamard diagonalization (`popcount ≥ 2` exact $1/12 < 1/6$), trace conservation $B/6$, `14/16` & `29/32` mode counts, and `61/96` & `359/576` E2M1 ratios. |
| `e2m1_harmonic_mean_worst_case_sr_variance` | `XorVdcFp4Dither.E2M1AndAntithetic` | Universal $(r - \ell)^2 / (4 \ell r)$ relative SR variance law attained at harmonic mean $2\ell r / (\ell + r)$ across all 6 OCP E2M1 intervals (`1/8, 1/24, 1/48`). |
| `antithetic_pair_sr_variance_halving` | `XorVdcFp4Dither.E2M1AndAntithetic` | Universal antithetic pair variance halving ($\le 1/4$ vs $1/2$) and exact `0` variance on complementary/midpoint pairs. |
| `double_quant_gemm_bias_obstruction_and_hammersley` | `XorVdcFp4Dither.DoubleGemm` | Exact `max |bias| = 1/4` obstruction for `same`, `antithetic`, and `msb_1bit_xor` vs exact `3527/1048576` (`> 74x` lower) for `bitrev_10` Hammersley. |
| `split_32bit_word_xor_vdc_zero_bias_double_gemm` | `XorVdcFp4Dither.DoubleGemm` | Universal exact zero bias + preserved negative intra-block covariance for 32-bit split-word XOR-VDC double GEMM (`64x` PRNG reduction). |

## 31. [`mhc-sinkhorn-fp8-bounds/`](mhc-sinkhorn-fp8-bounds/)

All statements are in [`mhc-sinkhorn-fp8-bounds/Challenge.lean`](mhc-sinkhorn-fp8-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`mhc-sinkhorn-fp8-bounds/MhcSinkhornFp8/Defs.lean`](mhc-sinkhorn-fp8-bounds/MhcSinkhornFp8/Defs.lean). See [`mhc-sinkhorn-fp8-bounds/README.md`](mhc-sinkhorn-fp8-bounds/README.md) for the BF16/FP8 Sinkhorn fixed points, $\sqrt{n-1}$ support collapse, and dyadic-orthogonal mixer proofs.

| Theorem | Module | Statement |
|---|---|---|
| `sinkhorn_diagonal_scaling_invariance` | `MhcSinkhornFp8.ScalingAndContraction` | Universal exact rational Sinkhorn scaling invariance $R(D _ 1 A D _ 2) = R(A D _ 2)$ and $C(A D _ 2) = C(A)$. |
| `antidiagonal_swamping_bf16_fp8_fixed_point` | `MhcSinkhornFp8.FloatFixedPoints` | Bit-exact RNE BF16 & FP8-E4M3FN permanent Mode-A fixed points for all $2 \le n \le 16$ with true row sums `259/256..271/256` / `19/16..31/16` and $L$-layer blowup. |
| `fp8_support_collapse_sqrt_n_minus_1_fixed_point` | `MhcSinkhornFp8.SupportCollapse` | GPU-discovered $n = 4$ exact rational fixed point ($\|H\| _ 2^2 = 2$) + universal $n \ge 3$ family attaining $\|H\| _ 2^2 = n - 1$. |
| `mode_b_exact_sum_symmetric_overshoot_fixed_point` | `MhcSinkhornFp8.FloatFixedPoints` | Mode-B exact-sum permanent RNE fixed points achieving exact spectral norms `527/512` (FP8) and `131327/131072` (BF16). |
| `sinkhorn_interstream_contraction_bound` | `MhcSinkhornFp8.ScalingAndContraction` | Universal doubly-stochastic contraction $\|H v\| _ 2^2 \le (1 - n\varepsilon)^2 \|v\| _ 2^2$ and $L$-layer decay on $V _ \perp$. |
| `dyadic_orthogonal_zero_division_mixers_exact` | `MhcSinkhornFp8.DyadicMixers` | Universal exact orthogonality and arbitrary-depth energy preservation for $n = 4$ Quaternion/Hadamard and $n = 8$ dyadic Householder mixers. |

## 32. [`loftq-cycles-rank1-ef21/`](loftq-cycles-rank1-ef21/)

All statements are in [`loftq-cycles-rank1-ef21/Challenge.lean`](loftq-cycles-rank1-ef21/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`loftq-cycles-rank1-ef21/LoftqCyclesRank1/Defs.lean`](loftq-cycles-rank1-ef21/LoftqCyclesRank1/Defs.lean). See [`loftq-cycles-rank1-ef21/README.md`](loftq-cycles-rank1-ef21/README.md) for the rank-1 EF21 laws, coupled orthogonal matrices, and LoftQ 2-cycle/3-cycle proofs.

| Theorem | Module | Statement |
|---|---|---|
| `rank1_onebit_ef21_contraction_exact` | `LoftqCyclesRank1.Rank1OneBit` | Universal all-$(m, n)$ exact $1/(mn)$ rank-1 1-bit sign EF21 contraction over `RatMat m n` + attainment on $e _ 0 e _ 0^T$. |
| `rank1_ternary_2x2_contraction_exact` | `LoftqCyclesRank1.Rank1Ternary2x2` | Exact $(2 + \sqrt{2})/8$ rank-1 ternary EF21 contraction at $(2, 2)$ over $\mathbb{Q}(\sqrt{2})$ + attainment. |
| `coupled_orthogonal_beats_block_2x2_rotations` | `LoftqCyclesRank1.CoupledOrthogonal` | Kernel-checked $3 \times 3$ and exact-orthogonal $4 \times 4$ ($W^T W = 16680999 I _ 4$) matrices strictly beating $I _ k \otimes R(\pi/8)$. |
| `loftq_alternating_monotone_energy_and_4m2_saturation` | `LoftqCyclesRank1.LoftqEnergySaturation` | Universal Euclidean-projection LoftQ Lyapunov descent, exact $(d - 2)(k - 1)^2$ spiked separation, and exact $4 M^2$ saturation barrier. |
| `loftq_explicit_3x3_symmetric_2cycle_witness` | `LoftqCyclesRank1.LoftqCycles` | Constructive (`[propext, Quot.sound]`) permanent period-2 LoftQ limit cycle on `W_cyc2` (`> 13%` odd-step jump). |
| `loftq_explicit_3x3_symmetric_3cycle_witness` | `LoftqCyclesRank1.LoftqCycles` | Constructive (`[propext, Quot.sound]`) permanent period-3 LoftQ limit cycle on `W_cyc3` (`> 6%` jump, 3 distinct states). |

## 33. [`ring-attention-kulisch-bounds/`](ring-attention-kulisch-bounds/)

All statements are in [`ring-attention-kulisch-bounds/Challenge.lean`](ring-attention-kulisch-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`ring-attention-kulisch-bounds/RingAttnKulisch/Defs.lean`](ring-attention-kulisch-bounds/RingAttnKulisch/Defs.lean). See [`ring-attention-kulisch-bounds/README.md`](ring-attention-kulisch-bounds/README.md) for the sink-vanishing, descending-$m _ i$ paradox, and Kulisch invariance proofs.

| Theorem | Module | Statement |
|---|---|---|
| `online_softmax_merge_exact_associativity` | `RingAttnKulisch.Monoid` | Universal exact rational associativity and commutativity of the online-softmax merge monoid. |
| `attention_sink_l2r_desc_vanishing_law` | `RingAttnKulisch.SinkVanishing` | Exact $p$-bit RNE bulk-vanishing law at $\Delta \ge p$: sequential L2R/DESC drops 100% of all $P - 1$ bulk chunks (`(P - 1)/(2^p + P - 1)` error). |
| `binary_tree_vs_l2r_sink_survival_separation` | `RingAttnKulisch.SinkVanishing` | Balanced binary-tree reduction pushes bulk survival to $\Delta _ {\mathrm{vanish}}^{\mathrm{TREE}} = p + \log _ 2 P - 1$ (with FP8 subnormal cap $\Delta = 10$). |
| `descending_mi_phase_transition_paradox` | `RingAttnKulisch.DescParadox` | Constructive separation showing `DESC` beats `L2R` on narrow spans (0 rescales) yet suffers catastrophic swamping worse than `ASC`/`TREE` on sinks. |
| `fixed_point_kulisch_topology_partition_invariance` | `RingAttnKulisch.KulischInvariance` | Universal permutation/tree/partition invariance of fixed-point Kulisch accumulation + exact width $W _ {\mathrm{inv}}(P, p) = p + 2\lceil\log _ 2 P\rceil + 4$ (`int32` FP8, `int64` FP16). |
| `fixed_point_sink_cliff_elimination` | `RingAttnKulisch.KulischInvariance` | Exact `F = p + log _ 2 P` fractional bit threshold eliminating the bulk-vanishing cliff across all $P = 2^k$. |
