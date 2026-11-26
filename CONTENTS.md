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

## 34. [`mxfp8-e2m5-e3m4-frontier/`](mxfp8-e2m5-e3m4-frontier/)

All statements are in [`mxfp8-e2m5-e3m4-frontier/Challenge.lean`](mxfp8-e2m5-e3m4-frontier/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`mxfp8-e2m5-e3m4-frontier/Mxfp8Frontier/Defs.lean`](mxfp8-e2m5-e3m4-frontier/Mxfp8Frontier/Defs.lean). See [`mxfp8-e2m5-e3m4-frontier/README.md`](mxfp8-e2m5-e3m4-frontier/README.md) for the complete 5-regime `E _ a M _ b` microscaling frontiers and delayed-scaling crossovers.

| Theorem | Module | Statement |
|---|---|---|
| `fp8_e1m6_collapse_to_int8_exact` | `Mxfp8Frontier.GridCollapse` | Universal `E1 M _ m ≡ E0 M _ {m+1}` grid collapse specializing to `E1M6_FN ≡ INT8` and the strict 5-format chain. |
| `mxfp8_e4m3_vs_e5m2_all_b_crossover_exact` | `Mxfp8Frontier.E4M3vsE5M2` | Exact all-$B$ `E4M3_OCP` vs `E5M2_IEEE` crossovers: $B^* = 637{,}534{,}211$ (E8M0) and $B^* = 2{,}630{,}667{,}468$ (DeepSeek-V3 FP32). |
| `mxfp8_e8m0_complete_five_regime_frontier` | `Mxfp8Frontier.FiveRegimes` | Complete OCP E8M0 frontier: `INT8 [1..4] → E2M5 [5..47] → E3M4 [48..11,379] → E4M3 [11,380..637M] → E5M2`. |
| `deepseek_fp32_scale_complete_five_regime_frontier` | `Mxfp8Frontier.FiveRegimes` | Complete DeepSeek-V3 FP32-scale frontier: `INT8 [2..12] → E2M5 [13..230]` (`> 6.77x` at `1×128`) `→ E3M4 [231..54,668]` (`> 3.32x` at `128×128`). |
| `delayed_scaling_spike_clipping_crossover_exact` | `Mxfp8Frontier.DelayedScaling` | Universal delayed-scaling spike crossover $\rho^*(M, m) = \frac{2^{m+1} + 1}{2^{m+1}} \cdot 2^M$, exact `(9/8) * 2^M` for `E4M3` vs `E5M2`. |
| `fp8_block_scaling_bias_invariance_exact` | `Mxfp8Frontier.DelayedScaling` | Exact list-level block-scaled exponent-bias invariance vs `4×` per-bit delayed-scaling headroom capacity tax. |

## 35. [`kronecker-cyclic-frustration/`](kronecker-cyclic-frustration/)

All statements are in [`kronecker-cyclic-frustration/Challenge.lean`](kronecker-cyclic-frustration/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`kronecker-cyclic-frustration/KroneckerCyclicFrustration/Defs.lean`](kronecker-cyclic-frustration/KroneckerCyclicFrustration/Defs.lean). See [`kronecker-cyclic-frustration/README.md`](kronecker-cyclic-frustration/README.md) for the Sum-of-2-Kronecker, Karp cyclic frustration, and Octonion Monarch proofs.

| Theorem | Module | Statement |
|---|---|---|
| `sum_of_two_kronecker_optimal_cond_exact` | `KroneckerCyclicFrustration.SumTwoKronecker` | Universal Sum-of-2-Kronecker lower bound $\kappa^2 \ge \frac{(1 + \alpha _ {\max}\beta _ {\max})(1 + \alpha _ {\min}\beta _ {\min})}{(1 + \alpha _ {\max}\beta _ {\min})(1 + \alpha _ {\min}\beta _ {\max})}$ attained by Corner-Geometric-Mean. |
| `multihead_two_head_zero_frustration_and_kfac_gap` | `KroneckerCyclicFrustration.MultiHeadFrustration` | Universal 2-head zero-frustration ($\sqrt{M}$) vs K-FAC quadratic penalty $(1 + M)^2 / (4M)$. |
| `multihead_cyclic_frustration_karp_cycle_bound` | `KroneckerCyclicFrustration.MultiHeadFrustration` | Universal Karp multiplicative cycle-product lower bound $\le \kappa^L$ and sharp $2(H - 1)/H \in \{1, 4/3, 3/2, 7/4\}$ cyclic frustration separation. |
| `monarch_coherence_factorization_and_lower_bound` | `KroneckerCyclicFrustration.MonarchCoherence` | Universal 2-stage Monarch coherence factorization $\mu^2(L P R) = \mu^2(A)\mu^2(B) \ge (\mathrm{nnz}(A)\mathrm{nnz}(B))^{-1}$. |
| `octonion_sparse_e2m1_monarch_blocks_exact` | `KroneckerCyclicFrustration.MonarchCoherence` | Exact orthogonality, row sparsity, optimal coherence, and zero-E2M1-error membership for sparse Quaternion ($4 \times 4$) and Octonion ($8 \times 8$) Monarch blocks. |
| `kfac_cross_scale_suboptimality_witness` | `KroneckerCyclicFrustration.SumTwoKronecker` | Explicit exact rational cross-scale witness proving `> 1,000x` $\kappa^2$ suboptimality of K-FAC vs Corner-Geometric-Mean. |

## 36. [`mla-kantorovich-rope-bounds/`](mla-kantorovich-rope-bounds/)

All statements are in [`mla-kantorovich-rope-bounds/Challenge.lean`](mla-kantorovich-rope-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`mla-kantorovich-rope-bounds/MlaKantorovichRope/Defs.lean`](mla-kantorovich-rope-bounds/MlaKantorovichRope/Defs.lean). See [`mla-kantorovich-rope-bounds/README.md`](mla-kantorovich-rope-bounds/README.md) for the Kantorovich-Hadamard, NoPE+RoPE crossover, Parseval multi-head, and $R = 1105$ RoPE proofs.

| Theorem | Module | Statement |
|---|---|---|
| `kantorovich_bilinear_spectral_leakage_exact` | `MlaKantorovichRope.KantorovichGL` | Universal bilinear Kantorovich leakage bound $(\kappa + \kappa^{-1})^2 / 4$ with exact 2-level attainment and optimal diagonal balancing $D _ j^2 = w _ j / \gamma _ j$. |
| `absorbed_kv_gl_invariance_exact` | `MlaKantorovichRope.KantorovichGL` | Universal zero-FLOP $\mathrm{GL}(d _ c)$ absorbed-KV attention logit invariance including orthogonal-diagonal $M = U D$. |
| `decoupled_nope_rope_256_85_crossover_exact` | `MlaKantorovichRope.NopeRopeMemory` | Exact DeepSeek `(3, 8)` (`2048 b/tok`, `-11.1%`) vs `(4, 4)` crossover iff $\alpha _ R / \alpha _ c > 256/85$ plus universal $(d _ c, d _ R, b _ c, b _ R)$ law. |
| `parseval_tight_frame_multihead_interference_cap` | `MlaKantorovichRope.ParsevalMultihead` | Universal Parseval / row-orthogonal Bessel $H$-head cap ($d _ c^2$ vs $H d _ c^2$) with inductive $2^k$ Walsh–Hadamard witnesses for $H \in \{8, 16, 32, 64\}$. |
| `pythagorean_1105_multi_angle_rope_exact` | `MlaKantorovichRope.PythagoreanRoPE` | Brahmagupta–Fibonacci $R = 1105 = 5 \cdot 13 \cdot 17$ exact integer RoPE pairs with orthogonality, norm conservation, and relative-position composition. |
| `subbyte_mla_memory_compression_ratios_exact` | `MlaKantorovichRope.NopeRopeMemory` | Exact `1024/3x` (`341.33x`) compression vs BF16 MHA-128 and `6x` vs BF16 MLA for fused `Tern512 + RoPE64_INT8`. |

## 37. [`rmsnorm-hybrid-linf-l1/`](rmsnorm-hybrid-linf-l1/)

All statements are in [`rmsnorm-hybrid-linf-l1/Challenge.lean`](rmsnorm-hybrid-linf-l1/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`rmsnorm-hybrid-linf-l1/RmsnormHybridLinfL1/Defs.lean`](rmsnorm-hybrid-linf-l1/RmsnormHybridLinfL1/Defs.lean). See [`rmsnorm-hybrid-linf-l1/README.md`](rmsnorm-hybrid-linf-l1/README.md) for the $\Theta(d^{1/4})$ hybrid norm minimax law, swamping horizons, and negative-variance proofs.

| Theorem | Module | Statement |
|---|---|---|
| `hybrid_linf_l1_exact_upper_and_lower_envelopes` | `RmsnormHybridLinfL1.HybridNorm` | Universal sharp rational upper/lower envelopes for $\alpha\|x\| _ \infty + \frac{\beta}{d}\|x\| _ 1$ relative to $\mathrm{RMS}(x)$ with exact attainment. |
| `hybrid_linf_l1_minimax_d_quarter_law` | `RmsnormHybridLinfL1.HybridNorm` | Universal minimax identity $(2\kappa^2 - 1)^2 - d \ge 0$, unique square-dim optimum $\kappa^2 = (s + 1)/2$ iff $\beta = s\alpha$, and no-$O(1)$ lower bound. |
| `dyadic_llama3_d4096_hybrid_norm_exact` | `RmsnormHybridLinfL1.HybridNorm` | Pure-bitshift Llama-3 8B ($d = 4096, \kappa^2 = 65/2$, `> 126x` vs `L1`) and 70B ($d = 8192, \kappa^2 = 97/2$, `> 168x` vs `L1`) witnesses. |
| `bf16_fp16_fp8_sumsq_swamping_horizon_exact` | `RmsnormHybridLinfL1.SwampingAndNegVar` | Universal $S _ {\mathrm{swamp}}(p) = 2^p$ IEEE-754 RNE swamping threshold + exact minimal outlier witnesses across BF16, FP16, FP8-E4M3, FP8-E5M2, MXFP4. |
| `bf16_fp16_onepass_layernorm_negative_variance_exact` | `RmsnormHybridLinfL1.SwampingAndNegVar` | Bit-exact 1-pass LayerNorm negative-variance (`NaN`) witnesses for BF16 (`0x4173`), FP16 (`0x5417`), FP8-E4M3 (`0x55`), and FP8-E5M2 (`0x48`). |
| `twopass_shifted_mean_variance_nonneg_universal` | `RmsnormHybridLinfL1.SwampingAndNegVar` | Universal non-negativity of 2-pass shifted-mean variance in exact `Rat` and every monotonic non-negative rounding arithmetic. |

## 38. [`paley32-mxfp4-outliers/`](paley32-mxfp4-outliers/)

All statements are in [`paley32-mxfp4-outliers/Challenge.lean`](paley32-mxfp4-outliers/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`paley32-mxfp4-outliers/Paley32Mxfp4/Defs.lean`](paley32-mxfp4-outliers/Paley32Mxfp4/Defs.lean). See [`paley32-mxfp4-outliers/README.md`](paley32-mxfp4-outliers/README.md) for the universal PAPR bound, `AGL(1, 31)` Paley-32 proof, Hall-16 duality, and E8M0 bulk-crush proofs.

| Theorem | Module | Statement |
|---|---|---|
| `universal_orthogonal_k_sparse_papr_lower_bound` | `Paley32Mxfp4.UniversalBounds` | Universal real-orthogonal $k$-sparse PAPR lower bound $\ge k/n$ with Hadamard flatness `iff` ($1 \le k < n$). |
| `paley32_orthogonality_and_zero_k4_collapse` | `Paley32Mxfp4.Paley32` | Exact `P32^T P32 = 32 I`, `1,240` Sylvester-32 `c _ 4 = 8` planes, vs exhaustive Paley-32 `maxC4 ≤ 5` over all `35,960` 4-subsets via `AGL(1, 31)`. |
| `paley32_vs_sylvester32_k8_l4_reduction` | `Paley32Mxfp4.Paley32` | Universal Paley-32 `c _ 8 ≤ 3` and exact `49/64` fourth-moment cut (`12,544` vs `16,384`) over all `1.346B` signed 8-sparse vectors via transpose duality. |
| `hall16_five_classes_orthogonality_and_k4_k8_duality` | `Paley32Mxfp4.Hall16Bent` | Complete Hall-16 Classes I–V exact `k = 4` (`140, 76, 44, 28, 28`) vs `k = 8` (`30, 54, 90, 114, 156`) duality separation. |
| `bent_diagonal_n16_anti_resonance_exact` | `Paley32Mxfp4.Hall16Bent` | Explicit 4-variable bent diagonal (`0x356`) orthogonality + flattening `80 / 140` Sylvester-16 affine 2-planes to exact PAPR `= 1`. |
| `mxfp4_e8m0_bulk_crush_threshold_exact` | `Paley32Mxfp4.UniversalBounds` | Universal OCP MXFP4 E8M0 bulk-crush threshold $k^2 M^2 > 576(B - k)$ and Hybrid $k$-Split bit-budget dominance over MXFP6. |

## 39. [`mxfp4-nvfp4-opt-clipping/`](mxfp4-nvfp4-opt-clipping/)

All statements are in [`mxfp4-nvfp4-opt-clipping/Challenge.lean`](mxfp4-nvfp4-opt-clipping/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`mxfp4-nvfp4-opt-clipping/Mxfp4OptClipping/Defs.lean`](mxfp4-nvfp4-opt-clipping/Mxfp4OptClipping/Defs.lean). See [`mxfp4-nvfp4-opt-clipping/README.md`](mxfp4-nvfp4-opt-clipping/README.md) for the optimal `E8M0`/`E4M3` clipping, never-drop-two-exponents, and `-0.0` repurposing proofs.

| Theorem | Module | Statement |
|---|---|---|
| `mxfp4_e8m0_scale_down_piecewise_linear_crossover` | `Mxfp4OptClipping.Mxfp4E8M0` | Exact piecewise-linear `E8M0` scale-down gain $\Phi(M) \in \{0, 2M - 7, 6M - 27\}$ and universal block `iff`. |
| `mxfp4_opt_e8m0_all_b_ef21_three_regime_law` | `Mxfp4OptClipping.Mxfp4E8M0` | Universal all-$B$ 3-regime optimal-`E8M0` EF21 law with tight witnesses (`47/431` at $B = 32$, `23/151` at $B = 64$, `1/5` at $B = 145$). |
| `nvfp4_ceil_vs_nearest_e4m3_all_b_ef21_exact` | `Mxfp4OptClipping.Nvfp4E4M3` | Exact all-$B$ `NVFP4` ceil-vs-nearest `E4M3` EF21 laws (`199/4231` vs `151/4759` at $B = 16$, $u = 5$ transitions at $B = 12, 20$). |
| `nvfp4_opt_e4m3_b16_and_b1_synergy_exact` | `Mxfp4OptClipping.Nvfp4E4M3` | Optimal `NVFP4` `E4M3` contraction `23/887` at $B = 16$ ($\lambda = 428/887$) and `1/625` at $B = 1$ ($s = 13/8$ synergy). |
| `mxfp4_opt_e8m0_never_drops_two_exponents` | `Mxfp4OptClipping.Mxfp4E8M0` | Exact inequality $(3 - 6s)(2M - 3 - 6s) \ge 3M - 27/4 > 9/4$ proving optimal `E8M0` never drops two exponents. |
| `e2m1_neg_zero_repurposing_exact_gain` | `Mxfp4OptClipping.E2M1NegZero` | Exact `-0.0` repurposing laws ($c = 8 \to 47/431$, $c = 1/4 \to 95/1631$ with $B = 33, 49$ transitions, $c = 5 \to 1/49$ at $B = 1$). |

## 40. [`smoothquant-dyadic-minimax/`](smoothquant-dyadic-minimax/)

All statements are in [`smoothquant-dyadic-minimax/Challenge.lean`](smoothquant-dyadic-minimax/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`smoothquant-dyadic-minimax/SmoothquantDyadic/Defs.lean`](smoothquant-dyadic-minimax/SmoothquantDyadic/Defs.lean). See [`smoothquant-dyadic-minimax/README.md`](smoothquant-dyadic-minimax/README.md) for the asymmetric AM-GM, dyadic minimax, and SmoothQuant–Hadamard proofs.

| Theorem | Module | Statement |
|---|---|---|
| `smoothquant_asymmetric_amgm_optimal_scale` | `SmoothquantDyadic.AmGmScale` | Exact asymmetric AM-GM optimal SmoothQuant migration scale over $\mathbb{Q}$. |
| `dyadic_smoothquant_perchannel_l2_5_over_4_sharp` | `SmoothquantDyadic.DyadicMinimax` | Sharp `5/4` ($+25\%$) per-channel dyadic power-of-two rounding penalty in $L _ 2$ with exact attainment. |
| `dyadic_smoothquant_perchannel_l1_9_over_8_sharp` | `SmoothquantDyadic.DyadicMinimax` | Sharp `9/8` ($+12.5\%$) per-channel dyadic power-of-two rounding penalty in $L _ 1$ with exact attainment. |
| `dyadic_smoothquant_pertensor_5_2_vs_phase_shift_3_2` | `SmoothquantDyadic.DyadicMinimax` | Exact per-tensor dyadic penalty reduction from `5/2` (naive) to `3/2` (phase-shifted). |
| `smoothquant_hadamard_noncommutation_separation` | `SmoothquantDyadic.NonCommutation` | Exact order-of-operations separation proving SmoothQuant and Hadamard rotations fail to commute. |
| `channel_outlier_coupling_paradox_exact` | `SmoothquantDyadic.NonCommutation` | Exact channel-outlier coupling paradox showing simultaneous weight/activation spike tradeoffs. |

## 41. [`flashattn-bwd-signflip/`](flashattn-bwd-signflip/)

All statements are in [`flashattn-bwd-signflip/Challenge.lean`](flashattn-bwd-signflip/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`flashattn-bwd-signflip/FlashAttnBwdSignflip/Defs.lean`](flashattn-bwd-signflip/FlashAttnBwdSignflip/Defs.lean). See [`flashattn-bwd-signflip/README.md`](flashattn-bwd-signflip/README.md) for the spurious sign-flip, `dO · fl(O)` divergence, key-centering, and `U-E3M1` proofs.

| Theorem | Module | Statement |
|---|---|---|
| `softmax_jacobian_zero_sum_and_cancellation_free_identity` | `FlashAttnBwdSignflip.SoftmaxJacobian` | Exact Softmax-Jacobian zero-sum conservation and cancellation-free backward identity. |
| `peaked_softmax_half_spurious_signflip_threshold` | `FlashAttnBwdSignflip.SignflipCliff` | Razor-sharp `50%` spurious sign-flip phase transition at tail mass $\varepsilon \le 2^{-(m+2)}$ (`1/512` BF16, `1/32` FP8-E4M3, `1/16` FP8-E5M2, `1/8` U-E3M1). |
| `direct_p_dp_midpoint_dc_leakage_exact` | `FlashAttnBwdSignflip.SignflipCliff` | Exact direct $P \cdot dP$ midpoint DC-leakage law $1/(2^{m+1} + 1)$. |
| `flashattn_do_o_orthogonal_divergence_amplification` | `FlashAttnBwdSignflip.OrthogonalDivergence` | Exact FlashAttention $D _ i = dO \cdot \mathrm{fl}(O)$ orthogonal divergence amplification $u _ {\mathrm{fwd}} \cdot \kappa _ {\mathrm{orth}}$. |
| `key_centering_dq_invariance_exact` | `FlashAttnBwdSignflip.OrthogonalDivergence` | Exact key-centering invariance $dQ = dS(K - \bar{K})$ and backward bias elimination. |
| `unsigned_ue3m1_vs_mxfp4_dynamic_range_16x_exact` | `FlashAttnBwdSignflip.UnsignedRange` | Exact `16×` dynamic-range advantage of unsigned `U-E3M1` over signed `MXFP4-E2M1` on nonnegative probabilities. |

## 42. [`unsigned-fp4-softmax-v/`](unsigned-fp4-softmax-v/)

All statements are in [`unsigned-fp4-softmax-v/Challenge.lean`](unsigned-fp4-softmax-v/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`unsigned-fp4-softmax-v/UnsignedFp4SoftmaxV/Defs.lean`](unsigned-fp4-softmax-v/UnsignedFp4SoftmaxV/Defs.lean). See [`unsigned-fp4-softmax-v/README.md`](unsigned-fp4-softmax-v/README.md) for the unsigned FP4 regime classification, XOR-VDC zero simplex drift, and `V`-centering proofs.

| Theorem | Module | Statement |
|---|---|---|
| `unsigned_fp4_e1m3_collapse_to_uint4` | `UnsignedFp4SoftmaxV.UnsignedFormats` | Exact collapse of unsigned `U-E1M3` onto uniform `UINT4`. |
| `unsigned_fp4_all_b_ef21_regime_classification` | `UnsignedFp4SoftmaxV.UnsignedFormats` | Complete all-$B$ unsigned FP4 EF21 contraction regime classification. |
| `softmax_simplex_rtn_drift_exact` | `UnsignedFp4SoftmaxV.SimplexDriftSr` | Exact RTN simplex-sum drift bounds across `U-E3M1`, `U-E2M2` (`< 25%`), and OCP `FP8-E4M3` (`127/2187 < 6%`). |
| `stratified_xor_vdc_simplex_zero_drift` | `UnsignedFp4SoftmaxV.SimplexDriftSr` | Exact zero simplex-sum drift for pair-antithetic and zero-carry stratified XOR-VDC SR across all dyadic residues. |
| `attention_v_centering_simplex_drift_annihilation` | `UnsignedFp4SoftmaxV.VCentering` | Exact algebraic identity annihilating first-order simplex-drift bias $\delta _ P \mu _ V \equiv 0$ via `V`-centering. |
| `raw_v_e2m1_level_collapse_vs_centered_invariance` | `UnsignedFp4SoftmaxV.VCentering` | Raw `V` collapses to `≤ 2` signed `E2M1` levels at $|\mu|/R \ge 4$ (`15, 12, 8, 4, 2, 1`), while centered `V _ c` retains `15/15`. |

## 43. [`mxfp-doublelog-ftz-law/`](mxfp-doublelog-ftz-law/)

All statements are in [`mxfp-doublelog-ftz-law/Challenge.lean`](mxfp-doublelog-ftz-law/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`mxfp-doublelog-ftz-law/MxfpDoublelogFtz/Defs.lean`](mxfp-doublelog-ftz-law/MxfpDoublelogFtz/Defs.lean). See [`mxfp-doublelog-ftz-law/README.md`](mxfp-doublelog-ftz-law/README.md) for the universal `4^b`-cancellation double-logarithmic exponent law and FTZ hardware bifurcation proofs.

| Theorem | Module | Statement |
|---|---|---|
| `mxfp_e1_equals_e0_and_signed_unsigned_duality` | `MxfpDoublelogFtz.GridDuality` | Universal `E1 ≡ E0` collapse and signed–unsigned duality across all bit-widths $b$ and exponent widths $e$. |
| `mxfp_universal_ef21_closed_form` | `MxfpDoublelogFtz.Ef21Envelopes` | Exact universal all-$(b, e, B)$ MXFP EF21 contraction closed form. |
| `mxfp_doublelog_crossover_4b_cancellation_law` | `MxfpDoublelogFtz.DoubleLogLaw` | Exact `4^b`-cancellation crossover theorem proving optimal exponent width $e^*(B) \sim \log _ 2 \log _ 2 B$ is independent of $b$. |
| `mxfp_e8m0_doublelog_shift_law` | `MxfpDoublelogFtz.DoubleLogLaw` | Exact OCP `E8M0` double-logarithmic shift law across all bit-widths. |
| `mxfp_ftz_four_to_the_b_underflow_penalty` | `MxfpDoublelogFtz.FtzBifurcation` | Universal `4^b` Flush-to-Zero underflow penalty on worst-case block MSE. |
| `mxfp_ftz_hardware_bifurcation_e4m3_vs_e2mb` | `MxfpDoublelogFtz.FtzBifurcation` | Exact hardware FTZ bifurcation separating `FP8-E4M3` from `E2M _ b` formats. |

## 44. [`ssm-decay-collapse-bounds/`](ssm-decay-collapse-bounds/)

All statements are in [`ssm-decay-collapse-bounds/Challenge.lean`](ssm-decay-collapse-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`ssm-decay-collapse-bounds/SsmDecayCollapse/Defs.lean`](ssm-decay-collapse-bounds/SsmDecayCollapse/Defs.lean). See [`ssm-decay-collapse-bounds/README.md`](ssm-decay-collapse-bounds/README.md) for the one-ULP-per-step sequential collapse, additive swamping, and zero-multiplier shift-subtract proofs.

| Theorem | Module | Statement |
|---|---|---|
| `ieee_decay_stall_midpoint_exact` | `SsmDecayCollapse.IeeeRneDecay` | Universal $p \ge 1$ IEEE-754 RNE decay-stall midpoint $1 - 2^{-(p+2)}$ with exact specializations (`FP8`, `BF16`, `FP16`, `FP32`). |
| `one_ulp_per_step_sequential_collapse` | `SsmDecayCollapse.IeeeRneDecay` | Universal 1-ULP-per-step sequential collapse $\mathrm{seqPow}(p, m \cdot 2^p) = 2^{-m}$ (BF16 half-life `128` vs `177.10`, $2^{-32}$ at $T = 4096$). |
| `additive_swamping_exact_divergence` | `SsmDecayCollapse.AdditiveSwamping` | Exact linear additive swamping divergence $T \cdot 2^{-(p+1)}$ (`4` at $T = 1024$, `512` at $T = 131,072$ in BF16). |
| `dyadic_shift_subtract_tight_bounds` | `SsmDecayCollapse.ShiftSubtract` | Tight asymmetric signed-integer invariant interval $[-2^R B _ {\max}, 2^R B _ {\max} + (2^R - 1)]$ with exact attainment of both endpoints. |
| `dyadic_shift_subtract_zero_input_stall_asymmetry` | `SsmDecayCollapse.ShiftSubtract` | Under zero input, positive states $[0, 2^r - 1]$ stall permanently while every negative state strictly increases to $0$. |
| `csd_two_tap_half_life_gap_reduction` | `SsmDecayCollapse.ShiftSubtract` | 2-tap zero-multiplier CSD shift-subtract cuts worst adjacent decay-rate ratio from `2` to `3/2` with `65,536×` range over BF16. |

## 45. [`ce-lse-fp8-horizon/`](ce-lse-fp8-horizon/)

All statements are in [`ce-lse-fp8-horizon/Challenge.lean`](ce-lse-fp8-horizon/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`ce-lse-fp8-horizon/CeLseHorizon/Defs.lean`](ce-lse-fp8-horizon/CeLseHorizon/Defs.lean). See [`ce-lse-fp8-horizon/README.md`](ce-lse-fp8-horizon/README.md) for the `V = 1024` / `V = 131,072` FP8 conservation cliffs, FP16 loss-scale empty-window theorem, and pairwise `LogSumExp` proofs.

| Theorem | Module | Statement |
|---|---|---|
| `ce_gradient_zero_sum_conservation_exact` | `CeLseHorizon.CeConservation` | Exact discrete Cross-Entropy gradient zero-sum conservation $\sum (p _ v - \delta _ {v,y}) = 0$. |
| `fp8_e4m3_dual_horizon_and_rne_overshoot_cliff` | `CeLseHorizon.Fp8Horizons` | Exact OCP `FP8-E4M3` dual horizon (`V > 512` RTZ `-15/16`, `V = 1023` RNE overshoot `+255/256`, `V = 1024` cliff to `-1`). |
| `fp8_e5m2_128k_vocab_conservation_collapse` | `CeLseHorizon.Fp8Horizons` | Exact IEEE `FP8-E5M2` 128K vocab cliff (`V > 65536` RTZ `-7/8`, `V = 131,071` RNE `+32767/32768`, `V = 131,072` cliff to `-1`). |
| `fp16_loss_scale_empty_window_collapse_exact` | `CeLseHorizon.Fp16LossScale` | Exact FP16 power-of-two loss-scale empty-window collapse at $2^{30} - 2^{18}$ (normal) and $2^{41} - 2^{29}$ (subnormal). |
| `lse_naive_swamping_vs_pairwise_tree_exact` | `CeLseHorizon.LsePairwise` | Exact naive `1 + sum` and sequential `2^p t` `LogSumExp` stall vs zero-error pairwise tree `treeSum k t = 2^k t`. |
| `label_smoothing_fp8_total_erasure_exact` | `CeLseHorizon.Fp8Horizons` | Exact 100% FP8-E4M3 and FP8-E5M2 erasure of label smoothing $\varepsilon / V$ for $\varepsilon \le 1/8, V \ge 131,072$. |

## 46. [`allreduce-topology-xorvdc/`](allreduce-topology-xorvdc/)

All statements are in [`allreduce-topology-xorvdc/Challenge.lean`](allreduce-topology-xorvdc/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`allreduce-topology-xorvdc/AllReduceXorVdc/Defs.lean`](allreduce-topology-xorvdc/AllReduceXorVdc/Defs.lean). See [`allreduce-topology-xorvdc/README.md`](allreduce-topology-xorvdc/README.md) for the Binary-Tree wipeout paradox, zero-comm cross-rank XOR-VDC `TP×` variance theorem, and BF16 residual freeze depth proofs.

| Theorem | Module | Statement |
|---|---|---|
| `allreduce_subulp_drift_ring_vs_tree_exact` | `AllReduceXorVdc.TopologyDrift` | Exact `(TP - 1)`-fold Ring vs Binary-Tree/Direct sub-ULP drift separation (`63×` at `TP = 64`). |
| `allreduce_cancel_wipeout_ring_vs_tree_exact` | `AllReduceXorVdc.CancelWipeout` | Exact combinatorial wipeout laws: Ring `2/TP` vs Binary-Tree `TP/(2(TP - 1)) > 1/2` (`> 16×` worse at `TP = 64`) vs Direct `0`. |
| `cross_rank_xor_vdc_bijection_and_exact_mse` | `AllReduceXorVdc.CrossRankXorVdc` | Top-$K$ bijection on `Fin (2^K)`, zero bias, `< 1` ULP sum error, and exact MSE scaling (`64×` vs Ind-SR, `2048×` vs RNE at `TP = 64`). |
| `bf16_residual_stream_freeze_depth_exact` | `AllReduceXorVdc.ResidualFreeze` | Exact BF16 residual-stream freeze depth $L _ {\mathrm{freeze}}(p) = 2^{15 - 2p}$ (`32, 128, 512`) and boundary tie-to-even stall. |
| `kahan_compensated_residual_exact_recovery` | `AllReduceXorVdc.ResidualFreeze` | Exact Kahan conservation $s _ L + c _ L = s _ 0 + \sum x _ i$ and $|c _ L| \le u / 2$ across arbitrary depth $L$. |
| `fixed_scale_ternary_saturation_barrier` | `AllReduceXorVdc.TopologyDrift` | Identical $\pm S$ saturation across Ring, Tree, and Direct (`1×` ratio) proving dynamic rescaling is mandatory for ternary collectives. |

## 47. [`fano-sparse24-perm/`](fano-sparse24-perm/)

All statements are in [`fano-sparse24-perm/Challenge.lean`](fano-sparse24-perm/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`fano-sparse24-perm/FanoSparse24Perm/Defs.lean`](fano-sparse24-perm/FanoSparse24Perm/Defs.lean). See [`fano-sparse24-perm/README.md`](fano-sparse24-perm/README.md) for the Fano-plane $PG(2, 2)$ obstruction, sunflower barrier, and `4:8` vs `2:4` MXFP4 anchor-dilution proofs.

| Theorem | Module | Statement |
|---|---|---|
| `structured_topk_ef21_contraction_exact` | `FanoSparse24Perm.Ef21Structured` | Universal structured top-$k$ EF21 contraction $\alpha(k:m) = k/m$ with tight attainment (`1/2` for `2:4, 4:8, 8:16`). |
| `mxfp4_anchor_dilution_48_beats_24_exact` | `FanoSparse24Perm.Ef21Structured` | Universal rational Dinkelbach certificates proving `4:8 + MXFP4` (`18/37`) beats `2:4 + MXFP4` (`72/151`, gap `54/5587`). |
| `fano_plane_sparse24_obstruction_exact` | `FanoSparse24Perm.FanoObstruction` | Constructive proof that the 7 lines of $PG(2, 2)$ form the exact minimal weight-3 `2:4`-permutation barrier ($R _ {\mathrm{crit}}(2, 3) = 7$). |
| `sunflower_sparse24_obstruction_exact` | `FanoSparse24Perm.SunflowerObstruction` | Exact $S _ 8$ Venn-region proof that `≤ 3` weight-4 rows stay feasible while 4 sunflower rows kill all 35 ($R _ {\mathrm{crit}}(2, 4) = 4$). |
| `order_statistic_k2k_nmse_laws_exact` | `FanoSparse24Perm.OrderStatsNmse` | Exact Uniform $(k + 2)/(4(2k + 1))$ and Rényi-Laplace (`23/288` vs `79211/1411200`, `-29.72%`) `k:2k` NMSE laws. |
