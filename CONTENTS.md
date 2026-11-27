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

## 48. [`mxint-mxfp-swar-bounds/`](mxint-mxfp-swar-bounds/)

All statements are in [`mxint-mxfp-swar-bounds/Challenge.lean`](mxint-mxfp-swar-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`mxint-mxfp-swar-bounds/MxintMxfpSwar/Defs.lean`](mxint-mxfp-swar-bounds/MxintMxfpSwar/Defs.lean). See [`mxint-mxfp-swar-bounds/README.md`](mxint-mxfp-swar-bounds/README.md) for the `MXINT` vs `MXFP` EF21 crossover, `int16` SWAR packing, and half-integer collapse proofs.

| Theorem | Module | Statement |
|---|---|---|
| `mxint_all_b_ef21_contraction_exact` | `MxintMxfpSwar.Ef21Bounds` | Universal all-$B$ ($B \ge 1, w \ge 2$) exact symmetric `MXINT _ w` EF21 bounds $(B - 1)/(4 M^2 + B - 1)$ (AbsMax) and $B/(M^2 + B - 1)$ (`E8M0`). |
| `mxint_vs_mxfp_exact_blocksize_crossover` | `MxintMxfpSwar.Ef21Bounds` | Exact integer crossovers $B^*(w)$ where `MXFP _ w` overtakes `MXINT _ w` (`223/57` for `MXINT8` vs `MXFP8-E4M3`, winning at `B = 16, 32`). |
| `kulisch_mxint_zero_overflow_swar_exact` | `MxintMxfpSwar.KulischSwar` | Exact `B = 32` Kulisch dot bounds: `MXINT4` in `int12` (`±1568`), symmetric `MXINT6` in `int16` (`±30752`, 2-lane SWAR), asymmetric `MXINT6` overflows by `1` (`+32768`). |
| `half_integer_zero_free_o_one_over_b_collapse` | `MxintMxfpSwar.HalfIntAsym` | Exact $O(1/B)$ half-integer rescaled collapse and `E8M0` divergence thresholds $4^{w-1} - 2^{w-1} + 1 \in \{3, 13, 57, 993, 16257\}$. |
| `mxint4_asym_beats_sym_crossover_b16` | `MxintMxfpSwar.HalfIntAsym` | Exact `B = 15` tie (`1/15`), asymmetric `[-8, 7]` beats `[-7, 7]` for all $B \ge 16$, plus exact `4×` `7 vs 8` `E8M0` scale cliff. |
| `mxint_exact_integer_associativity` | `MxintMxfpSwar.KulischSwar` | Unconditional `Int` associativity, block-split additivity, and permutation invariance for `intDot`. |

## 49. [`sampling-gumbel-cdf-bounds/`](sampling-gumbel-cdf-bounds/)

All statements are in [`sampling-gumbel-cdf-bounds/Challenge.lean`](sampling-gumbel-cdf-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`sampling-gumbel-cdf-bounds/SamplingHorizons/Defs.lean`](sampling-gumbel-cdf-bounds/SamplingHorizons/Defs.lean). See [`sampling-gumbel-cdf-bounds/README.md`](sampling-gumbel-cdf-bounds/README.md) for the Gumbel impossible horizon, `Q32` speculative decoding, and descending-CDF vs Fenwick proofs.

| Theorem | Module | Statement |
|---|---|---|
| `gumbel_max_impossible_token_horizon_exact` | `SamplingHorizons.GumbelHorizon` | Exact finite-$b$-bit Gumbel-Max impossible-token horizon with rational certificates $\Delta _ {\mathrm{impossible}}(24) < 19.45 < 20$ and $\Delta _ {\mathrm{impossible}}(8) < 7.26 < 8$. |
| `specdec_exact_losslessness_vs_finite_residual_crash` | `SamplingHorizons.SpecDec` | Exact rational SpecDec losslessness vs bit-exact `FP8-E4M3` (`V = 64`) and `BF16` (`V = 2`) zero-residual `NaN` crash witnesses. |
| `specdec_q32_integer_exact_zero_leak` | `SamplingHorizons.SpecDec` | Exact division-free `Q32` integer speculative decoding (`accept + Z = 2^{32}`, zero over-accepts, zero crashes, exact `0` TV leak). |
| `descending_cdf_swamping_erasure_law` | `SamplingHorizons.CdfSwamping` | Exact RNE descending-CDF swamping cutoff $2^{-(m+2)}$ (`1/512` BF16, `1/4096` FP16, `2^{-25}` FP32) erasing all remaining tail tokens. |
| `fenwick_pairwise_tree_zero_swamping_exact` | `SamplingHorizons.CdfSwamping` | Balanced binary-tree / Fenwick pairwise sum over $2^k$ dyadic tail probabilities `2^{-r}` computes exact `2^k * 2^{-r}` with zero rounding error. |
| `top_p_nucleus_mass_shortfall_lower_bound` | `SamplingHorizons.CdfSwamping` | Exact cumulative mass shortfall & TV distance lower bound `K * t` (Llama-3 `V = 128,256` BF16 witness with TV `9/16 > 1/2`). |

## 50. [`alibi-bitsplit-kulisch/`](alibi-bitsplit-kulisch/)

All statements are in [`alibi-bitsplit-kulisch/Challenge.lean`](alibi-bitsplit-kulisch/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`alibi-bitsplit-kulisch/AlibiBitsplitKulisch/Defs.lean`](alibi-bitsplit-kulisch/AlibiBitsplitKulisch/Defs.lean). See [`alibi-bitsplit-kulisch/README.md`](alibi-bitsplit-kulisch/README.md) for the `ALiBi` swamping, finite-level bit-split, `W5A7 > W6A6`, and mixed-format Kulisch proofs.

| Theorem | Module | Statement |
|---|---|---|
| `alibi_content_swamping_and_dyadic_slope_exact` | `AlibiBitsplitKulisch.AlibiSwamping` | Universal RNE `ALiBi` content-swamping threshold $B \ge 2^{p+1}|x|$, `BF16`/`FP8`/`FP16` (`d = 65,520`) horizons, and zero mul-error for dyadic slopes. |
| `bilinear_int_asymmetric_bitsplit_crossovers_exact` | `AlibiBitsplitKulisch.BitsplitMxfp` | Exact finite-level symmetric `INT _ b` bilinear crossovers (`125/22`, `24025/92`, `10143/2350`, `49/5`, `10571/2254`). |
| `absmax_pinned_superoutlier_bitsplit_reversal` | `AlibiBitsplitKulisch.BitsplitMxfp` | Exact absmax-pinned super-outlier reversal (`W5A3 > W4A4` iff $S^2 > 125/22$, `W4A2 > W3A3` iff $S^2 > 49/5$). |
| `mxfp_w5a7_beats_w6a6_mantissa_parity_exact` | `AlibiBitsplitKulisch.BitsplitMxfp` | Exact 12-bit mantissa-parity dominance of `W5A7` (`MXFP5-E2M2 × MXFP7-E3M3`) over `W6A6` (`MXFP6-E3M2 × MXFP6-E3M2`) by `8/5`. |
| `mixed_format_signed_kulisch_width_exact` | `AlibiBitsplitKulisch.KulischExact` | Single-bit tight signed Kulisch widths across `FP4×INT4`, `FP4×INT8`, `INT4×FP8-E4M3` (`27..36b`), and `FP4×FP8-E4M3` (`28..37b`). |
| `kulisch_int64_exact_associativity_vs_fp32_drift` | `AlibiBitsplitKulisch.KulischExact` | Constructive `int64 _ t` Kulisch permutation invariance vs explicit `K = 32` `INT4 × FP8-E4M3` FP32 non-associativity witness. |

## 51. [`swiglu-kurtosis-diag-opt/`](swiglu-kurtosis-diag-opt/)

All statements are in [`swiglu-kurtosis-diag-opt/Challenge.lean`](swiglu-kurtosis-diag-opt/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`swiglu-kurtosis-diag-opt/SwiGluKurtosis/Defs.lean`](swiglu-kurtosis-diag-opt/SwiGluKurtosis/Defs.lean). See [`swiglu-kurtosis-diag-opt/README.md`](swiglu-kurtosis-diag-opt/README.md) for the `2×` ReGLU kurtosis, zero-FLOP diagonal equivalence, and asymmetric bit-allocation proofs.

| Theorem | Module | Statement |
|---|---|---|
| `reglu_exact_two_x_kurtosis_multiplication_law` | `SwiGluKurtosis.KurtosisLaws` | Exact `2×` gating-sparsity kurtosis identity $\mathrm{Kurt}(\mathrm{ReLU}(G) \cdot U) = 2\,\mathrm{Kurt}(G)\,\mathrm{Kurt}(U)$ with Gaussian (`18`) and Laplace (`72`) witnesses. |
| `correlated_bilinear_kurtosis_amplification_exact` | `SwiGluKurtosis.KurtosisLaws` | Exact correlated kurtosis amplification $2\mathbb{E}[G^8]/(\mathbb{E}[G^4])^2$ and Gaussian-mixture curve (`70/3` at $\rho = 1$, `76/3` at $\rho = 1/2$). |
| `swiglu_zero_flop_diagonal_equivalence_identity` | `SwiGluKurtosis.DiagonalEquiv` | Exact zero-FLOP diagonal invariance $W _ {\mathrm{down}} S^{-1}(\phi(g) \odot (S u)) = W _ {\mathrm{down}}(\phi(g) \odot u)$ leaving nonlinear `W _ {\mathrm{gate}}` untouched. |
| `swiglu_optimal_diagonal_scale_amgm_law` | `SwiGluKurtosis.DiagonalEquiv` | Exact AM-GM/SOS optimal diagonal scale $\lambda^2 = K\sqrt{\varepsilon _ a / \varepsilon _ w}$ with clamped optimality and `W4A4`/`W8A4`/`W16A4` certificates. |
| `gated_ffn_asymmetric_bit_allocation_dominance` | `SwiGluKurtosis.BitAllocAndFP4` | Universal 3-term cube AM-GM lower bound and exact integer-bit dominance `iff` laws (`(4, 5, 3) < (4, 4, 4) ↔ S _ u > 4 S _ d`). |
| `mxfp4_block32_vs_nvfp4_block16_kurtosis_underflow_gap` | `SwiGluKurtosis.BitAllocAndFP4` | `MXFP4` (`B = 32`) flushes all 31 background entries `< M/24` to zero, while `NVFP4` (`B = 16`) preserves 100% of the clean sub-block. |

## 52. [`bitserial-lut-dag-bounds/`](bitserial-lut-dag-bounds/)

All statements are in [`bitserial-lut-dag-bounds/Challenge.lean`](bitserial-lut-dag-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`bitserial-lut-dag-bounds/BitSerialLutDag/Defs.lean`](bitserial-lut-dag-bounds/BitSerialLutDag/Defs.lean). See [`bitserial-lut-dag-bounds/README.md`](bitserial-lut-dag-bounds/README.md) for the `2^(g-1) + g - 2` linear DAG lower bound, `(12, 2)` vs T-MAC `(14, 3)` circuit, and `int16` wrap-by-1 trap proofs.

| Theorem | Module | Statement |
|---|---|---|
| `binary_lut_dag_lower_bound_exact` | `BitSerialLutDag.BinaryDag` | Universal 2-input linear DAG lower bound $2^{g-1} + g - 2$ ops and $\lceil\log _ 2 g\rceil$ depth for all $g \ge 2$ (`2, 5, 10, 19` ops). |
| `tmac_depth2_optimal_12_vs_14_circuit` | `BitSerialLutDag.BinaryDag` | Exact soundness & completeness of `g = 4` `(12 ops, depth 2)` circuit beating T-MAC `(14, 3)` plus `(11, 3)` and lower-bound-tight `(10, 4)` circuits. |
| `ternary_lut_dag_bounds_and_symmetry` | `BitSerialLutDag.TernaryDag` | Exact symmetry-halved ternary LUT size $(3^g - 1)/2$, lower bound $(3^g - 1)/2 - g$, minimal $g = 2, 3, 4$ DAGs, and `(≤2, 4)` sparse DAG. |
| `popcnt_zero_lut_exact_bitserial_dot_identity` | `BitSerialLutDag.PopcntDot` | Universal bit-exact `POPCNT` dot-product identity for binary/ternary weights against arbitrary $b$-bit signed/unsigned activations. |
| `lut_vs_popcnt_amortization_crossover_exact` | `BitSerialLutDag.PopcntDot` | Exact rational LUT-vs-`POPCNT` amortization crossover and RDNA 3 no-crossover dominance theorem (`POPCNT` wins for all `M, N, K > 0`). |
| `tmac_int16_overflow_threshold_exact` | `BitSerialLutDag.PopcntDot` | Universal `int16` safety bound (`K _ {\max} = 258` symmetric `int8`) and exact full-`int8` wrap-by-1 trap (`+32768 → -32768`) at `K = 256/128/64`. |

## 53. [`muon-ns-dyadic-cycles/`](muon-ns-dyadic-cycles/)

All statements are in [`muon-ns-dyadic-cycles/Challenge.lean`](muon-ns-dyadic-cycles/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`muon-ns-dyadic-cycles/MuonNsDyadic/Defs.lean`](muon-ns-dyadic-cycles/MuonNsDyadic/Defs.lean). See [`muon-ns-dyadic-cycles/README.md`](muon-ns-dyadic-cycles/README.md) for the BF16 Jordan period-2/4/8 bifurcation, FP8/BF16 optimal dyadic quintics, and Polar-Express overshoot cliff proofs.

| Theorem | Module | Statement |
|---|---|---|
| `jordan_bf16_nonunit_sum_and_period2_limit_cycle` | `MuonNsDyadic.JordanCycles` | Proves Jordan's BF16 `(55/16, -153/32, 65/32)` sums to `11/16 ≠ 1`, traps Muon matrix-form in period-2 `{11/16, 71/64}`, with exact `23/64` worst-case `[0.01, 1]` deviation. |
| `jordan_bf16_parenthesization_bifurcation` | `MuonNsDyadic.JordanCycles` | Exact BF16 RNE parenthesization period-doubling bifurcation across Muon (period 2), Monomial (period 4), and Horner (period 8) on all `861` `[0.01, 1]` values. |
| `fp8_e4m3fn_optimal_quintic_exact_zero_error` | `MuonNsDyadic.OptimalDyadic` | Certifies GPU-discovered FP8-E4M3FN `(2, -9/8, 1/8)` achieves exact `0` 5-step error across all `28` `[0.05, 1]` values and `0` NaN/overflow on all `56` positive unit FP8 values. |
| `bf16_optimal_dyadic_quintic_one_ulp_confinement` | `MuonNsDyadic.OptimalDyadic` | Certifies GPU-discovered BF16 `(35/16, -31/16, 3/4)` confines all `564` `[0.05, 1]` BF16 values within 1 ULP (`1/128`, `44×–46×` tighter than Jordan). |
| `polar_express_bf16_fp8_one_ulp_overshoot_cliff` | `MuonNsDyadic.OvershootPareto` | Exact 1-ULP overshoot cliffs for Polar-Express (`129/128 → +Inf` BF16; `9/8 → NaN` FP8-E4M3FN) and MXFP4 saturation of Jordan `(3, -4, 2)` to `6`. |
| `universal_stationary_quintic_pareto_law` | `MuonNsDyadic.OvershootPareto` | Universal rational stationary quintic law: $a + b + c = 1 \implies p'(1) = 1 - 2a + 2c$, $|p'(1)| < 1 \iff a - 2 < c < a - 1$. |

## 54. [`kahan-neumaier-fp8-bounds/`](kahan-neumaier-fp8-bounds/)

All statements are in [`kahan-neumaier-fp8-bounds/Challenge.lean`](kahan-neumaier-fp8-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`kahan-neumaier-fp8-bounds/KahanNeumaierFp8/Defs.lean`](kahan-neumaier-fp8-bounds/KahanNeumaierFp8/Defs.lean). See [`kahan-neumaier-fp8-bounds/README.md`](kahan-neumaier-fp8-bounds/README.md) for the Dual Kahan-vs-Neumaier Separation, `FP8-E4M3FN` Kulisch-in-`int32_t`, and microbatch XOR-VDC SR proofs.

| Theorem | Module | Statement |
|---|---|---|
| `microbatch_rne_freeze_threshold_exact` | `KahanNeumaierFp8.RneFreeze` | Universal RNE freeze threshold $\rho _ {\mathrm{freeze,min}}(P) = 2^{P+1}$ (`8, 16, 256, 2048`) and max non-freeze ratio $2^{P+2} - 2$ with early-spike erasure vs pairwise tree preservation. |
| `kahan_late_dipole_spike_total_erasure_vs_neumaier` | `KahanNeumaierFp8.KahanNeumaier` | First half of Dual Separation: late dipole `[1^m, +S, -S]` causes `100%` Kahan erasure vs `100%` exact Neumaier recovery. |
| `neumaier_self_swamping_ceiling_beats_by_kahan` | `KahanNeumaierFp8.KahanNeumaier` | Second half of Dual Separation: Neumaier self-swamps at exact ceiling $M _ {\mathrm{Neumaier,max}}(P) = 2^{P+2}$ (`16, 32, 512, 4096`), beaten by Kahan's per-step fold-back. |
| `fp8_e4m3fn_kulisch_int32_9362_exact` | `KahanNeumaierFp8.KulischInt32` | Exact signed Kulisch bit-width law certifying up to $M \le 9{,}362$ arbitrary finite OCP `FP8-E4M3FN` values sum bit-exactly in `int32_t` (tight overflow at `9,363`). |
| `microbatch_xor_vdc_sr_zero_bias_and_stratification` | `KahanNeumaierFp8.XorVdcSr` | Bit-exact microbatch XOR-VDC SR bijection on $\mathrm{Fin}(2^K)$, exact zero bias, `< 1` ULP deterministic bound, and exact $M\times$ MSE reduction (`1/6` vs `M/6`). |
| `shared_exponent_int32_block_accum_associativity` | `KahanNeumaierFp8.BlockAccum` | Unconditional associativity, block-split additivity, and permutation invariance of shared-exponent `int32_t`/`int64_t` block accumulation. |

## 55. [`grpo-k3-kl-horizons/`](grpo-k3-kl-horizons/)

All statements are in [`grpo-k3-kl-horizons/Challenge.lean`](grpo-k3-kl-horizons/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`grpo-k3-kl-horizons/GrpoK3Kl/Defs.lean`](grpo-k3-kl-horizons/GrpoK3Kl/Defs.lean). See [`grpo-k3-kl-horizons/README.md`](grpo-k3-kl-horizons/README.md) for the negative-`k3` KL, FP8/BF16 clip-window collapse, binary-reward over-weighting, and one-pass negative-variance proofs.

| Theorem | Module | Statement |
|---|---|---|
| `schulman_k3_exact_nonnegativity_and_quadratic_bound` | `GrpoK3Kl.SchulmanK3` | Exact rational Schulman `k3` non-negativity, quadratic Taylor sandwich, global stabilizer $k _ 3^{\mathrm{stab}}(d) \ge d^2/3$, and `[2/2]` Padé non-negativity. |
| `bf16_k3_negative_kl_and_deadzone_exact` | `GrpoK3Kl.SchulmanK3` | Bit-exact `BF16`/`FP16` RNE negative-KL violations for both Order A (`0x3b01 → -1/256`) and Order B (`0x3b7f → -255/65536`) plus exact dead-zero bands. |
| `fp8_bf16_logprob_cancellation_clip_collapse` | `GrpoK3Kl.LogProbClipping` | Exact binade-ULP clip-escape proof certifying total `[4/5, 6/5]` PPO/GRPO clip-window collapse at $|\log p| \ge 2$ (`FP8-E4M3`), `32` (`BF16`), `256` (`FP16`). |
| `direct_logit_diff_binade_invariance` | `GrpoK3Kl.LogProbClipping` | Direct logit-difference tail-shift invariance capping error at $2^{-(m+1)} B$ independent of tail binade (`128×–256×` tighter than naive BF16 ULP). |
| `grpo_binary_reward_extreme_overweighting_exact` | `GrpoK3Kl.GrpoAdvantage` | Exact binary-reward GRPO over-weighting ratios $G - 1$ and $G^2/(4(G - 1))$ (`1024/63 > 16` at `G = 64`) versus `Dr.GRPO` ($|A _ i| \le 1$). |
| `grpo_bf16_onepass_negvar_and_fp8_mean_stall` | `GrpoK3Kl.GrpoAdvantage` | Bit-exact `BF16` one-pass negative-variance (`-1/8 < 0`) and `FP8-E4M3` $G = 64$ mean-saturation stall (`64/64 = 1 ≠ 4`). |

## 56. [`deltanet-householder-e8/`](deltanet-householder-e8/)

All statements are in [`deltanet-householder-e8/Challenge.lean`](deltanet-householder-e8/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`deltanet-householder-e8/DeltaNetHouseholderE8/Defs.lean`](deltanet-householder-e8/DeltaNetHouseholderE8/Defs.lean). See [`deltanet-householder-e8/README.md`](deltanet-householder-e8/README.md) for the Universal 2-ULP Safe Ceiling, WY triangular inverse growth, and `2 E _ 8` Weyl reflection proofs.

| Theorem | Module | Statement |
|---|---|---|
| `householder_spectral_stability_iff_exact` | `DeltaNetHouseholderE8.HouseholderSpectral` | Universal rational Householder spectral contraction `iff` law $0 \le \beta\|k\| _ 2^2 \le 2$ and strict explosion above `2`. |
| `quantized_unit_norm_supremum_exact` | `DeltaNetHouseholderE8.QuantizedTwoUlp` | Exact RNE binade-bottom unit-norm squared supremum $S _ {\max}^{(1)}(m) = ((2^{m+1}+2)/(2^{m+1}+1))^2 > 1$ with 8D `FP8-E4M3` witness `287/256`. |
| `universal_two_ulp_safe_ceiling_theorem` | `DeltaNetHouseholderE8.QuantizedTwoUlp` | Universal theorem for all $m \ge 2$: `1` ULP below `2` always explodes, whereas `2` ULPs below `2` (`7/4` FP8, `127/64` BF16, `1023/512` FP16) is unconditionally contractive. |
| `wy_triangular_inverse_norm_growth_exact` | `DeltaNetHouseholderE8.WyTriangular` | Exact aligned-key WY inverse $T _ {i,j} = (-1)^{i-j} \cdot 2$ with exact row $\ell _ 1$-norm $2i + 1$ and $\|T\| _ \infty = 2C - 1$ (`127` at `C = 64`). |
| `d8_and_e8_weyl_root_zero_ulp_orthogonality` | `DeltaNetHouseholderE8.WeylE8Closure` | Exact zero-remainder division `(2 * dot w x) % 8 = 0` (`>>> 2`), lattice closure, norm preservation, and involutivity for `D _ 8` and all `240` roots of `2 E _ 8`. |
| `non_weyl_hamming_closure_obstruction` | `DeltaNetHouseholderE8.WeylE8Closure` | Exact integer-closure obstruction for non-Weyl `Hamming[8,4,4]` (`(2 * dot v x) % 4 = 2`, non-integer reflection entry `1/2`). |

## 57. [`rope-q32-coprime-freeze/`](rope-q32-coprime-freeze/)

All statements are in [`rope-q32-coprime-freeze/Challenge.lean`](rope-q32-coprime-freeze/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`rope-q32-coprime-freeze/RopeQ32Coprime/Defs.lean`](rope-q32-coprime-freeze/RopeQ32Coprime/Defs.lean). See [`rope-q32-coprime-freeze/README.md`](rope-q32-coprime-freeze/README.md) for the BF16/FP16 freeze-run horizons, `Q32` Hensel-lifting relative invariance, and Dyadic Cayley rotation proofs.

| Theorem | Module | Statement |
|---|---|---|
| `rope_bf16_fp16_consecutive_freeze_run_exact` | `RopeQ32Coprime.FreezeHorizon` | Universal binade ULP freeze-run law (`32, 256, 1024, 8192` BF16 at `4K..1M`) and exact `FP16` `+Inf` overflow cliff at `m = 65,520`. |
| `rope_high_freq_random_phase_horizon_exact` | `RopeQ32Coprime.FreezeHorizon` | Exact high-frequency random-phase threshold at $m = 2^{p+1} + 1$ (`257` BF16, `2049` FP16) where `ulp ≥ 2 rad > π/2`. |
| `q32_modular_odd_dyadic_zero_drift_exact` | `RopeQ32Coprime.Q32Modular` | Universal Hensel-lifting theorem: odd-frequency `Q32` modular phase is a bijection on $\mathrm{Fin}(2^{32})$ with exact zero-drift relative-position additivity. |
| `quantized_rotation_norm_drift_exact` | `RopeQ32Coprime.RotationNormDrift` | Exact worst-case unit-circle norm drift `1/4` (`MXFP4-E2M1`), `21/256` (`FP8-E4M3`), and `0` identically for Dyadic Cayley rotations. |
| `relative_position_factorization_error_decomposition` | `RopeQ32Coprime.RelativeErrorCayley` | Exact algebraic separation of phase-truncation vs rotation-quantization logit error proving `Q32 + FP8` (`65/512 < 1`) strictly beats frozen BF16/FP16. |
| `dyadic_cayley_relative_composition_exact` | `RopeQ32Coprime.RelativeErrorCayley` | Exact $\mathrm{SO}(2, \mathbb{Q})$ group orthogonality, composition, and relative-position factorization laws for rational Cayley rotations. |

## 58. [`mrope-3d-coprime-bounds/`](mrope-3d-coprime-bounds/)

All statements are in [`mrope-3d-coprime-bounds/Challenge.lean`](mrope-3d-coprime-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`mrope-3d-coprime-bounds/Mrope3dCoprime/Defs.lean`](mrope-3d-coprime-bounds/Mrope3dCoprime/Defs.lean). See [`mrope-3d-coprime-bounds/README.md`](mrope-3d-coprime-bounds/README.md) for the separable `3/4` floor vs Coupled 3D shattering, BF16 Width freeze, and interleaved `> 10^6×` gain proofs.

| Theorem | Module | Statement |
|---|---|---|
| `separable_3d_mrope_axis_floor_theorem` | `Mrope3dCoprime.SeparableFloor` | Universal Separable-Axis Floor Theorem proving Qwen2-VL `(16, 24, 24)` exact `3/4` floor and unconditional Dirichlet–Welch bound $3/4 - 1/(4(N - 1))$. |
| `coupled_3d_mrope_shatters_separable_floor` | `Mrope3dCoprime.SeparableFloor` | Proves Coupled 3D phases shatter the separable floor, with exact 64-pair $\mathbb{Z} _ 4^3$ zero-sidelobe and 27-pair $\{1, 2, 3\}^3$ ($|K| \le 1/3$) witnesses. |
| `contiguous_mrope_bf16_width_freeze_exact` | `Mrope3dCoprime.Bf16FreezeResolution` | Proves `100%` BF16 cosine freeze across all 24 contiguous Width pairs (`40..63`) and all 63 patch offsets at $b = 10^6$. |
| `interleaved_vs_contiguous_mrope_resolution_gap` | `Mrope3dCoprime.Bf16FreezeResolution` | Exact geometric-series ratio certifying `> 10^7×` leading-pair and `> 10^6×` full-sum local spatial resolution gain for stride-3 / Qwen3-VL interleaved `mRoPE`. |
| `q32_3d_modular_phase_exact_relative_invariance` | `Mrope3dCoprime.Q32ModularPhase` | Exact 3D `Q32` modular relative-position homomorphism, cross-modal text-diagonal $(m, m, m)$ invariance, and full $2^{32}$ period along odd-frequency axes. |
| `cross_modal_fp_phase_drift_vs_q32_exact` | `Mrope3dCoprime.Q32ModularPhase` | Proves total cross-modal `BF16` collapse (`ulp = 1024`) and `FP16` `+Inf` overflow at $m = 131{,}072$ versus exact injective `Q32` phase. |

## 59. [`vcache-ipr-xorvdc-bounds/`](vcache-ipr-xorvdc-bounds/)

All statements are in [`vcache-ipr-xorvdc-bounds/Challenge.lean`](vcache-ipr-xorvdc-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`vcache-ipr-xorvdc-bounds/VcacheIprXorvdc/Defs.lean`](vcache-ipr-xorvdc-bounds/VcacheIprXorvdc/Defs.lean). See [`vcache-ipr-xorvdc-bounds/README.md`](vcache-ipr-xorvdc-bounds/README.md) for the IPR SR-vs-RNE phase transition, `XOR-VDC` super-convergence, and Rank-1 sink/WHT proofs.

| Theorem | Module | Statement |
|---|---|---|
| `ipr_attention_averaging_sr_vs_rne_exact` | `VcacheIprXorvdc.IprPhaseTransition` | Exact simplex IPR attention-averaging MSE decomposition, RNE-vs-SR threshold $N _ {\mathrm{eff}}^* = (\sigma _ {\mathrm{SR}}^2 - \sigma _ {\mathrm{RNE}}^2)/\mu _ {\mathrm{bias}}^2$, and `2.000×` peaked-head RNE advantage. |
| `cross_format_int2_sr_beats_int4_mxfp4_rne` | `VcacheIprXorvdc.IprPhaseTransition` | Exact cross-format inversion proving `INT2-SR` and `Ternary-SR` strictly beat `INT4-RNE` and `MXFP4-RNE` once $N _ {\mathrm{eff}} > \sigma _ {\mathrm{SR,low}}^2/\mu _ {\mathrm{bias,high}}^2$. |
| `xor_vdc_stratified_sr_superconvergence_and_iid_halving` | `VcacheIprXorvdc.XorVdcStratified` | Exact `Fin (2^K)` bijection, zero bias, `< 1` ULP $O(1/L^2)$ super-convergence, and consecutive MSB-flip `2×` i.i.d. variance halving for `XOR-VDC` stratified SR. |
| `rank1_attention_sink_ipr_crossover_exact` | `VcacheIprXorvdc.Rank1SinkWht` | Exact Rank-1 sink $\mathrm{IPR}(\alpha, L) = \alpha^2 + (1 - \alpha)^2/(L - 1)$ proving $\alpha \ge 3/4 \implies N _ {\mathrm{eff}} < 16/9 < 2$, restored to $L - 1$ by high-precision sink protection. |
| `rank1_split_wht_orthogonality_and_output_inversion` | `VcacheIprXorvdc.Rank1SinkWht` | Universal Sylvester WHT orthogonality $H _ {2^m}^T H _ {2^m} = 2^m I$ with Rank-1 mean-split commutation requiring only one output-side inverse WHT. |
| `sub4bit_vcache_packing_density_and_exact_int64_bounds` | `VcacheIprXorvdc.PackingInt64Bounds` | Exact `128K` V-cache compression ratios (`1 : 4 : 8 : 64/7 > 9.14×`), 5-trit/byte bijection, and zero-overflow `int64` `P * V` accumulator bounds. |

## 60. [`specdec-wiener-temp-bounds/`](specdec-wiener-temp-bounds/)

All statements are in [`specdec-wiener-temp-bounds/Challenge.lean`](specdec-wiener-temp-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`specdec-wiener-temp-bounds/SpecDecWienerTemp/Defs.lean`](specdec-wiener-temp-bounds/SpecDecWienerTemp/Defs.lean). See [`specdec-wiener-temp-bounds/README.md`](specdec-wiener-temp-bounds/README.md) for the Wiener-MMSE draft temperature rescue and sub-4-bit self-speculative dominance proofs.

| Theorem | Module | Statement |
|---|---|---|
| `wiener_mmse_temperature_uniquely_minimizes_logit_mse` | `SpecDecWienerTemp.WienerMMSE` | Exact completed-square SOS proof that $T _ {\mathrm{MMSE}}^* = 1 + \sigma _ q^2/\sigma _ z^2$ uniquely minimizes quantized-draft logit MSE at $\sigma _ z^2 \sigma _ q^2/(\sigma _ z^2 + \sigma _ q^2)$. |
| `wiener_mmse_strictly_beats_variance_matching_and_uncalibrated` | `SpecDecWienerTemp.WienerMMSE` | Irrational-free algebraic dominance $\mathrm{MSE}(T _ {\mathrm{MMSE}}^*) < \mathrm{MSE}(T _ {\mathrm{var}}) < \mathrm{MSE}(1)$ across all $\sigma _ z^2, \sigma _ q^2 > 0$. |
| `quantized_draft_tv_acceptance_lower_bound_exact` | `SpecDecWienerTemp.AcceptanceTV` | Exact acceptance–TV identity $\alpha = 1 - \mathrm{TV}$, ratio/multiplicative perturbation bounds, and Rényi-2 collision sensitivity identity $1 - \|p\| _ 2^2$. |
| `expected_specdec_yield_and_speedup_exact` | `SpecDecWienerTemp.SpecDecYield` | Closed-form geometric yield $(1 - \alpha^{\gamma+1})/(1 - \alpha)$, net speedup, and exact discrete marginal-benefit unimodality in lookahead $\gamma$. |
| `sub4bit_self_speculative_dominance_over_fp8_bf16` | `SpecDecWienerTemp.Sub4BitDominance` | Universal bandwidth ceilings ($S \le 1$ `BF16`, $S < 2$ `FP8` for all $\alpha, \gamma$) vs certified `INT2` (`2.976×`), `INT3`, and `INT4` self-speculative dominance. |
| `wiener_temperature_exact_acceptance_rescue_witnesses` | `SpecDecWienerTemp.AcceptanceRescue` | Exact binary and multi-class rational-base softmax ensembles proving strict acceptance rescue at $T _ {\mathrm{MMSE}}^*$ with zero-cost scale absorption. |

## 61. [`rag-popcnt-matryoshka-bounds/`](rag-popcnt-matryoshka-bounds/)

All statements are in [`rag-popcnt-matryoshka-bounds/Challenge.lean`](rag-popcnt-matryoshka-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`rag-popcnt-matryoshka-bounds/RagPopcntMatryoshka/Defs.lean`](rag-popcnt-matryoshka-bounds/RagPopcntMatryoshka/Defs.lean). See [`rag-popcnt-matryoshka-bounds/README.md`](rag-popcnt-matryoshka-bounds/README.md) for the 2-stage `POPCNT + INT4` oversampling hierarchy and Matryoshka spectral-decay crossover proofs.

| Theorem | Module | Statement |
|---|---|---|
| `popcnt_binary_and_twoplane_exact_dot_identities` | `RagPopcntMatryoshka.PopcntIdentities` | Universal bit-exact `XOR+POPCNT` bipolar, 1.58-bit ternary, and 2-bit 4-level symmetric `POPCNT` dot-product identities with zero multipliers. |
| `two_stage_oversample_snr_squared_hierarchy` | `RagPopcntMatryoshka.OversampleSnr` | Exact Cantelli concentration and rational $\mathrm{SNR}^2$ hierarchy $\eta _ {\mathrm{1b}}^2 = 4/\pi^2 < 1/2 < 4/5 < \eta _ {\mathrm{1.58b}}^2 < \eta _ {\mathrm{2b}}^2 < 1$ (`> 1.99×` / `> 2.17×`). |
| `matryoshka_vs_full_dim_binary_spectral_crossover_exact` | `RagPopcntMatryoshka.MatryoshkaCrossover` | Exact Euclidean-fidelity crossover `iff` $E(d _ M) < \eta _ q^2$, strict monotonicity under steeper spectra, and equal-byte `192 B/vec` flat-vs-steep bounds. |
| `hypercube_sign_wht_automatic_spectral_normalization` | `RagPopcntMatryoshka.HypercubeNorm` | Constant hypercube norm $\|\mathrm{sgn}(H x)\| _ 2^2 = D$ and positive-scale invariance explaining hypercube immunity to unnormalized inner-product hijack. |
| `stage2_int4_rescore_gap_preservation_exact` | `RagPopcntMatryoshka.Int4RescoreGap` | Universal Top-$K$ ranking preservation and pure-integer Stage-2 symmetric `INT4` margin certification ($64\|q\| _ 1 < \text{gap}$). |
| `rag_memory_and_bandwidth_speedup_roofline_exact` | `RagPopcntMatryoshka.RooflineSpeedup` | Exact `16×`/`8×` VRAM compression (`192/384 MiB` vs `3072 MiB` FP16 at `1M × 1536`) and exact 2-stage byte-transfer ratio $1/16 + MK/(4N)$ (`> 15.9×`). |

## 62. [`flashattn-dyadic-slack-bounds/`](flashattn-dyadic-slack-bounds/)

All statements are in [`flashattn-dyadic-slack-bounds/Challenge.lean`](flashattn-dyadic-slack-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`flashattn-dyadic-slack-bounds/FlashAttnDyadicSlack/Defs.lean`](flashattn-dyadic-slack-bounds/FlashAttnDyadicSlack/Defs.lean). See [`flashattn-dyadic-slack-bounds/README.md`](flashattn-dyadic-slack-bounds/README.md) for the dyadic-slack zero-mantissa-error, `L = 65,520` FP16 cliff, and identical-cancellation normalization proofs.

| Theorem | Module | Statement |
|---|---|---|
| `dyadic_power_of_two_rescale_zero_mantissa_error` | `FlashAttnDyadicSlack.DyadicRescale` | Exact IEEE-754 proof that multiplying normal floats by $2^{-k}$ shifts only the exponent with `0` mantissa error vs eager `1/2`-ULP midpoint drift. |
| `eager_online_softmax_one_ulp_per_step_collapse` | `FlashAttnDyadicSlack.DyadicRescale` | Universal inductive eager 1-ULP-per-step collapse $\mathrm{seqPow}(p, m \cdot 2^p) = 2^{-m}$ strictly underestimating true exponential decay. |
| `slack_threshold_fp16_fp8_overflow_boundary_exact` | `FlashAttnDyadicSlack.SlackOverflow` | Exact integer slack overflow `iff` boundaries for `FP8-E4M3` ($\tau \le 8$) and `FP16` tile width `64` ($\tau \le 9$), certifying safe windows `[4, 6]` / `[6, 8]`. |
| `fp16_flat_attention_65520_overflow_cliff_exact` | `FlashAttnDyadicSlack.SlackOverflow` | Bit-exact IEEE-754 `FP16` RNE flat-attention overflow cliff at exact `L = 65,520` (`65,504 + 16`), causing `100%` `+Inf`/`NaN` for all $L \ge 65{,}520$. |
| `dyadic_exponent_normalization_cancels_identically` | `FlashAttnDyadicSlack.DyadicNormKulisch` | Zero-mantissa-error `2^{-1}` normalization keeping $0 \le \ell < 2^{14}$ for arbitrary $L$ while cancelling identically in $(2^{-k} O)/(2^{-k} \ell) = O/\ell$. |
| `flash_tile_int32_kulisch_associativity_and_exactness` | `FlashAttnDyadicSlack.DyadicNormKulisch` | Exact signed `int32` (`Q8.20`) `64`-element `P * V` Kulisch zero-overflow, zero-drift, and `List.Perm` permutation invariance proof. |

## 63. [`nsa-ballbound-moba-bounds/`](nsa-ballbound-moba-bounds/)

All statements are in [`nsa-ballbound-moba-bounds/Challenge.lean`](nsa-ballbound-moba-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`nsa-ballbound-moba-bounds/NsaBallBoundMoba/Defs.lean`](nsa-ballbound-moba-bounds/NsaBallBoundMoba/Defs.lean). See [`nsa-ballbound-moba-bounds/README.md`](nsa-ballbound-moba-bounds/README.md) for the MoBA antipodal blindspot, Zero-Sqrt Ball-Bound, and Quest-AABB separation proofs.

| Theorem | Module | Statement |
|---|---|---|
| `moba_antipodal_and_buried_needle_blindspot_exact` | `NsaBallBoundMoba.MobaBlindspot` | Universal antipodal-pair ($B \ge 2$) and buried-needle ($B \ge 3$) blindspot forcing $q^T S _ b \le 0$ while $\max _ j q^T k _ j = 2\|q\| _ 2^2 > 0$. |
| `zero_sqrt_ball_bound_exact_soundness_zero_fn` | `NsaBallBoundMoba.BallBoundExact` | Universal pure-integer Cauchy–Schwarz soundness certifying exact `0` false negatives for Zero-Sqrt Ball-Bound with `+1` scalar per block. |
| `ball_bound_strictly_tighter_than_quest_aabb_and_half_metadata` | `NsaBallBoundMoba.QuestAabbSeparation` | Exact `(d + 1)/(2d)` metadata dominance (`65/128` at $d = 64$) and all-dimension ($d = m^2$) sphere witness where Quest-AABB over-estimates by exact $\sqrt{d}\times$. |
| `quantization_absorbing_ball_bound_zero_fn_all_precisions` | `NsaBallBoundMoba.BallBoundExact` | Quantization-absorbing Ball-Bound preserving exact `0` false negatives across all summary precisions (`1-bit` through `FP8`). |
| `nsa_three_branch_convex_gate_antipodal_breakdown` | `NsaBallBoundMoba.NsaGateAndPopcnt` | Exact NSA 3-branch convex-gate lower bound $\ge E _ 0^2$ under distant antipodal needles, collapsing to `0` under Ball-Bound selection. |
| `popcnt_twoplane_summary_bandwidth_dominance` | `NsaBallBoundMoba.NsaGateAndPopcnt` | Exact `9/3/1`-weighted `2-Bitplane POPCNT` dot-product identity with `4×`/`8×` bit-bandwidth reduction vs `INT8`/`FP16`. |

## 64. [`relu2-teal-deadzone-bounds/`](relu2-teal-deadzone-bounds/)

All statements are in [`relu2-teal-deadzone-bounds/Challenge.lean`](relu2-teal-deadzone-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`relu2-teal-deadzone-bounds/Relu2TealDeadzone/Defs.lean`](relu2-teal-deadzone-bounds/Relu2TealDeadzone/Defs.lean). See [`relu2-teal-deadzone-bounds/README.md`](relu2-teal-deadzone-bounds/README.md) for the `ReLU^2` kurtosis, Uniform-PRE vs FP-POST `4×` split, and `TEAL`/`CATS` deadzone reclamation proofs.

| Theorem | Module | Statement |
|---|---|---|
| `relu2_exact_kurtosis_seventy_thirds_and_outlier_amplification` | `Relu2TealDeadzone.KurtosisOutliers` | Exact `ReLU` kurtosis `6` and `ReLU^2` kurtosis `70/3`, plus exact $c^4$ outlier-moment amplification (`> 75×` on 1% `4×` outliers). |
| `relu2_quantization_order_uniform_pre_beats_post` | `Relu2TealDeadzone.QuantOrderDichotomy` | Uniform quantizer `POST`-vs-`PRE` deadzone ratio $2N$ (`> 5×` wider for `INT4-u4`) and strict `PRE` dominance for $x < M(1/2 - 1/(4N))$. |
| `relu2_quantization_order_fp_post_beats_pre_exact_4x` | `Relu2TealDeadzone.QuantOrderDichotomy` | Opposite floating-point dichotomy: exact two-sided squared-error inflation $(2 - \varepsilon)^2 \le \mathrm{ratio} \le (2 + \varepsilon)^2 \to 4\times$ (`+6.02 dB`). |
| `teal_cats_shifted_deadzone_reclamation_uniform_exact` | `Relu2TealDeadzone.DeadzoneReclamation` | Exact `TEAL`/`CATS` shifted-deadzone uniform MSE reduction $(1 - \tau/M)^{-2}$ at zero extra bits (`4×, 16×, 64×`). |
| `teal_cats_fp_superquadratic_logarithmic_density_bonus` | `Relu2TealDeadzone.DeadzoneReclamation` | Exact floating-point step contraction $\frac{x - \tau}{x}\cdot\frac{M}{M - \tau} < 1$ proving strictly super-quadratic MSE gain $> (1 - \tau/M)^{-2}$ on $(\tau, M)$. |
| `prune_before_quantize_mask_flip_and_bitmask_crossover` | `Relu2TealDeadzone.MaskFlipBitmask` | Exact pre-pruning mask-flip boundary $[\tau - \Delta/2, \tau + \Delta/2)$ and `uint64_t` bitmask sparse `W4` crossover $s^* = \mathrm{ov}/(1 + \mathrm{ov}) < 1/5$. |

## 65. [`ssm-tustin-pade-horizons/`](ssm-tustin-pade-horizons/)

All statements are in [`ssm-tustin-pade-horizons/Challenge.lean`](ssm-tustin-pade-horizons/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`ssm-tustin-pade-horizons/SsmTustinPade/Defs.lean`](ssm-tustin-pade-horizons/SsmTustinPade/Defs.lean). See [`ssm-tustin-pade-horizons/README.md`](ssm-tustin-pade-horizons/README.md) for the Tustin Nyquist cliff, `ZOH` blackout, and subtraction-free `Padé-(0,2)` stability proofs.

| Theorem | Module | Statement |
|---|---|---|
| `tustin_nyquist_snap_to_minus_one_horizon_exact` | `SsmTustinPade.TustinNyquist` | Universal IEEE-754 RNE Tustin Nyquist snap-to-`-1.0` horizon $z _ {\mathrm{osc}}(p) = 2^{p+1} + 8$ (`24, 40, 520, 4104`) and unconditional binades $k \ge p + 2$. |
| `tustin_vs_zoh_infinite_memory_stall_two_x_gap` | `SsmTustinPade.StallBlackout` | Exact `2×` small-$z$ infinite-memory (`+1.0`) stall separation between Tustin/`Padé-(0,2)` ($z \le 2^{-p}$) and `ZOH` ($z \le 2^{-(p+1)}$). |
| `zoh_b_bar_catastrophic_cancellation_blackout_horizon` | `SsmTustinPade.StallBlackout` | Exact `100%` `ZOH` $\bar{B}$ blackout for $z \le 2^{-(p+1)}$ and exact `(0, 1]` blackout ratio $(B - f - 2)/B$ (`118/127 > 92.91%` BF16). |
| `pade02_unconditional_positivity_and_contraction_exact` | `SsmTustinPade.Pade02Laws` | Exact $0 < A _ {\mathrm{pade02}}(z) < 1$ for all $z > 0$ (zero unstable/Nyquist poles), $O(z^3)$ Taylor matching, and `FP8-E4M3FN` overflow thresholds. |
| `pade02_b_bar_zero_blackout_and_fourth_order_accuracy` | `SsmTustinPade.Pade02Laws` | Subtraction-free $0 < B _ {\mathrm{pade02}}(z) \le 1$ (`0%` blackout), exact 4th-order accuracy $\le z^4/360$ on `(0, 1]` (`19×` tighter than Tustin at `z = 1`). |
| `ssm_trajectory_energy_conservation_and_nyquist_blowup` | `SsmTustinPade.TrajectoryEnergy` | Exact inductive $O(T^2)$ Nyquist/stall energy blowup at $a = \pm 1$ vs uniform boundedness $|h _ T| \le |b|/(1 - a)$ for `Padé-(0,2)`. |

## 66. [`vlm-tome-cumulant-bounds/`](vlm-tome-cumulant-bounds/)

All statements are in [`vlm-tome-cumulant-bounds/Challenge.lean`](vlm-tome-cumulant-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`vlm-tome-cumulant-bounds/VlmTomeCumulant/Defs.lean`](vlm-tome-cumulant-bounds/VlmTomeCumulant/Defs.lean). See [`vlm-tome-cumulant-bounds/README.md`](vlm-tome-cumulant-bounds/README.md) for the unweighted TV ceiling, Cumulant-2 logit bonus, WHT matching dichotomy, and ViT schedule proofs.

| Theorem | Module | Statement |
|---|---|---|
| `unweighted_merge_tv_distortion_and_exact_ceiling` | `VlmTomeCumulant.ProportionalAttention` | Exact unweighted-merge TV distortion $(s - 1) p'(1 - p')/(1 + (s - 1) p')$, exact ceiling $(r - 1)/(r + 1)$ for $r^2 = s$, and enclosures for `s = 2, 8, 32`. |
| `proportional_attention_zero_dispersion_exact_invariance` | `VlmTomeCumulant.ProportionalAttention` | Exact zero-dispersion probability and Value-output invariance (`0` TV distortion) under proportional attention (`+ln s`). |
| `within_cluster_dispersion_jensen_underweight_and_cumulant2_bonus` | `VlmTomeCumulant.ProportionalAttention` | Discrete Jensen underweighting on dispersed clusters and identical 2nd-order $O(\sigma^2)$ partition-residual cancellation via the Cumulant-2 Logit Bonus (`+ln s + σ^2/2`). |
| `bipartite_wht_int4_outlier_rescue_vs_binary_walsh_tie` | `VlmTomeCumulant.WalshHadamardSimHash` | Orthogonal `H _ {2^k}` $1/\sqrt{d}$ outlier flattening rescuing `INT4`/`MXFP4` paired with equidistant $2^{k-1}$ Walsh-code Hamming ties degrading 1-bit SimHash. |
| `vit_front_loaded_dominates_constant_r_schedule` | `VlmTomeCumulant.ScheduleFlopBounds` | Exact Abel-summation proof that front-loaded ViT schedules strictly dominate ToMe `Constant-r` on both FLOPs and compounding drift. |
| `late_loaded_merging_flop_infeasibility_ceiling` | `VlmTomeCumulant.ScheduleFlopBounds` | Exact `> 2/3` baseline FLOP lower bound proving infeasibility of any $\ge 3/2$ (`1.5×`) FLOP speedup for final-third late-loaded merging. |

## 67. [`embed-zipf-lazystamp-bounds/`](embed-zipf-lazystamp-bounds/)

All statements are in [`embed-zipf-lazystamp-bounds/Challenge.lean`](embed-zipf-lazystamp-bounds/Challenge.lean) against pure-`Init` (zero Mathlib) definitions in [`embed-zipf-lazystamp-bounds/EmbedZipfLazyStamp/Defs.lean`](embed-zipf-lazystamp-bounds/EmbedZipfLazyStamp/Defs.lean). See [`embed-zipf-lazystamp-bounds/README.md`](embed-zipf-lazystamp-bounds/README.md) for the tied-embedding flush, BF16 `v_t` freeze, `Lazy-Stamp AdamW`, and Zipf mixed-precision proofs.

| Theorem | Module | Statement |
|---|---|---|
| `tied_embedding_dense_pushdown_zero_sum_and_asymmetry` | `EmbedZipfLazyStamp.TiedGrad` | Exact tied-embedding column-sum conservation $\sum _ v g _ {\mathrm{out}}[v, j] = 0$ and sparse-input vs dense-output asymmetry ratio $p _ y^{-1} \cdot p _ v$. |
| `rare_token_rne_weight_flush_and_fp8_subnormal_underflow` | `EmbedZipfLazyStamp.RneFlush` | Universal IEEE-754/OCP RNE half-ULP weight-update flush, `FP8` subnormal blackout (`2^{-10}`, `2^{-17}`), and exact Zipf-rank flush thresholds. |
| `bf16_sparse_adamw_v_decay_freeze_exact` | `EmbedZipfLazyStamp.Bf16Freeze` | Universal sharp $1 - \beta _ 2 \le 2^{-(p+2)}$ permanent EMA decay-freeze law trapping `BF16` $\beta _ 2 = 0.999$ and $\eta\lambda = 10^{-4}$ across all $K$ steps. |
| `lazy_stamp_adamw_exact_equivalence_to_dense_updates` | `EmbedZipfLazyStamp.LazyAdamW` | Exact inductive equivalence of $O(1)$ `Lazy-Stamp AdamW` to $\Delta$ dense steps, breaking `BF16` $\beta _ 2 = 0.999$ freeze for `100%` of states at $\Delta = 4$. |
| `lazy_stamp_bandwidth_and_work_speedup_exact` | `EmbedZipfLazyStamp.BandwidthSpeedup` | Exact $V / U$ memory-traffic and FLOP speedup (`32×` at `131,072 / 4,096`, `≥ 25×` for `U ≤ 5,242`) and savings fraction $1 - U / V$. |
| `zipf_mixed_precision_embedding_allocation_pareto` | `EmbedZipfLazyStamp.ZipfPareto` | Exact Cauchy–Schwarz/AM-GM optimality of $4^{b _ r - b _ s} = p _ r / p _ s$ with certified `< 2.0 b/param` Zipf allocations beating uniform `4-bit` (`MXFP4`) at half VRAM. |

## 68. [`two-adic-carry-firewall-covers/`](two-adic-carry-firewall-covers/)

Pure-Init Lean 4 2-adic compactness engine: finite prefix-tree certificates prove universal bitwise-arithmetic and Collatz-type theorems over all natural numbers.

| Theorem | Module | Statement |
|---|---|---|
| `coverTree_sound` | `TwoAdicCarryFirewallCovers.Theorems` | A checked finite 2-adic prefix tree whose leaves certify balls $B(r, d)$ proves $P(n)$ for all $n \in \mathbb{N}$. |
| `T4_global_convergence` | `TwoAdicCarryFirewallCovers.Theorems` | The bit-4-cleared Collatz map $T _ 4$ sends every $n$ to $\{0, 1\}$ (4 prefix bits certify 7 steps). |
| `T5_global_convergence` | `TwoAdicCarryFirewallCovers.Theorems` | The bit-5-cleared Collatz map $T _ 5$ sends every $n$ to $\{0, 1\}$, via a 506-leaf depth-15 tree (64.8x compression). |
| `X21_global_convergence_to_zero` | `TwoAdicCarryFirewallCovers.Theorems` | The XOR-Collatz map $X _ {2,1}$ sends every $n$ to $0$. |
| `X33_global_convergence_to_zero` | `TwoAdicCarryFirewallCovers.Theorems` | The XOR-Collatz map $X _ {3,3}$ sends every $n$ to $0$. |
| `grayQuad2_val_ceiling` | `TwoAdicCarryFirewallCovers.Theorems` | $2^{15} \nmid G(n)^2 + 3n + 60$ for all $n$, where $G(n) = n \oplus (n \gg 1)$ (744.7x compression). |
| `grayQuad2_neq_shift15` | `TwoAdicCarryFirewallCovers.Theorems` | $G(n)^2 + 3n + 60 \ne n \ll 15$ for all $n$. |
| `T8_nontrivial_6cycle_never_drops` | `TwoAdicCarryFirewallCovers.Theorems` | For $T _ 8$ the positive 6-cycle through $975$ never drops below $975$ (sharpness of the $k \le 5$ range). |

## 69. [`bitwise-grundy-periodicity-compiler/`](bitwise-grundy-periodicity-compiler/)

Pure Lean 4 Init (zero Mathlib) formalization of borrow-guarded subtraction games: Kummer borrow-popcount identity, dyadic borrow-wall periodicity, a kernel-checked Sprague-Grundy periodicity compiler, the multi-heap XOR theorem and the aperiodic borrow-parity boundary.

| Theorem | Module | Statement |
|---|---|---|
| `kummer_borrow_popcount` | `BitwiseGrundyPeriodicityCompiler.Theorems` | For $s \le n$: $\mathrm{popcount}(n - s) + \mathrm{popcount}(s) = \mathrm{popcount}(n) + \mathrm{borrowCount}(n, s)$. |
| `borrowCount_le_shift_inv` | `BitwiseGrundyPeriodicityCompiler.Theorems` | For $s < 2^k$ and $s \le n$: $\mathrm{borrowCount}(n + m \cdot 2^{k+B}, s) \le B \iff \mathrm{borrowCount}(n, s) \le B$. |
| `isWinningMulti_iff_nimSum_ne_zero` | `BitwiseGrundyPeriodicityCompiler.Theorems` | For every game $G$ and every list of heaps $hs$: $\mathrm{IsWinningMulti}(G, hs) \iff \mathrm{nimSum}(hs.\mathrm{map}(g _ G)) \ne 0$. |
| `dyadic_borrow_wall_periodicity` | `BitwiseGrundyPeriodicityCompiler.Theorems` | If all guards of $G$ are wall guards, then $g _ G(n + 2^{\mathrm{gameShiftBits}(G)}) = g _ G(n)$ for all $n$. |
| `checkCert_sound_grundy` | `BitwiseGrundyPeriodicityCompiler.Theorems` | If $\mathrm{checkCert}(G, c) = \mathrm{true}$, then $g _ G(n) = \mathrm{evalPeriodic}(c, n)$ for all $n$. |
| `G_coprime_p5_period_5` | `BitwiseGrundyPeriodicityCompiler.Theorems` | For the game $\{2\,(\text{borrow-free}), 3, 7\}$ and all $n \ge 15$: $g(n + 5) = g(n)$. |
| `grundyParity_not_eventually_periodic` | `BitwiseGrundyPeriodicityCompiler.Theorems` | For all $n _ 0$ and $p > 0$ there is $n \ge n _ 0$ with $g _ {\mathrm{par}}(n + p) \ne g _ {\mathrm{par}}(n)$. |
| `grundyParity_oneHeap_periodic_vs_twoHeap_aperiodic` | `BitwiseGrundyPeriodicityCompiler.Theorems` | For $n \ge 12$, $g _ {\mathrm{par}}(n) \ne 0 \iff n \bmod 4 \in \{0, 3\}$; for $k \ge 3$, $g _ {\mathrm{par}}(4k) \oplus g _ {\mathrm{par}}(4) = 0 \iff v _ 2(k)$ is even. |

## 70. [`ca-torsion-lyapunov-flux-compiler/`](ca-torsion-lyapunov-flux-compiler/)

Pure-Init Lean 4 potential/flux/Lyapunov certificate compiler: a finite kernel-decidable check on a cellular-automaton rule proves conservation, torsion, convergence and acyclicity laws on rings of every length.

| Theorem | Module | Statement |
|---|---|---|
| `thm_pat101_conservation_0xac8c` | `CaTorsionLyapunovFluxCompiler.Theorems` | For every $w \ge 1$, $x$ and $t$, the nonlinear rule 0xac8c conserves the number of cyclic 101 windows: $\Phi(T ^ t x) = \Phi(x)$. |
| `thm_strict_fp_termination_0x2c48` | `CaTorsionLyapunovFluxCompiler.Theorems` | Rule 0x2c48 satisfies $T(T ^ {4w} x) = T ^ {4w} x$ on every ring of length $w \ge 1$. |
| `thm_global_acyclicity_0x2c48` | `CaTorsionLyapunovFluxCompiler.Theorems` | If $T ^ P x = x$ for some $P \ge 1$ under rule 0x2c48, then $T x = x$ (no non-trivial cycles on any ring). |
| `thm_travelingWave_locking_rule152` | `CaTorsionLyapunovFluxCompiler.Theorems` | Under rule 152, $T(T ^ {3w} x) = \mathrm{ringRot}(1, T ^ {3w} x)$ for every ring and configuration. |
| `thm_microcanonical_0xf0e0` | `CaTorsionLyapunovFluxCompiler.Theorems` | For rule 0xf0e0 and $x ^ \ast = T ^ w x$: $T x ^ \ast = \mathrm{ringRot}(1, x ^ \ast)$ and $\# _ {11}(x ^ \ast) = \# _ {11}(x)$. |
| `thm_blinker_convergence_rule108` | `CaTorsionLyapunovFluxCompiler.Theorems` | For ECA rule 108 and $y = T ^ {2w} x$: $T(T y) = y$. |
| `thm_mod3_torsion_0xb0f0` | `CaTorsionLyapunovFluxCompiler.Theorems` | Rule 0xb0f0 satisfies $\Phi(T ^ t x) \equiv \Phi(x) \pmod 3$ for all $w \ge 1$, $x$, $t$, with no integer lift. |
| `thm_mod2_torsion_0x83bc` | `CaTorsionLyapunovFluxCompiler.Theorems` | Rule 0x83bc satisfies $\Phi(T ^ t x) \equiv \Phi(x) \pmod 2$ for all $w \ge 1$, $x$, $t$, with no integer lift. |

## 71. [`carried-ca-coboundary-rigidity/`](carried-ca-coboundary-rigidity/)

Pure Lean 4 Init formalization (zero Mathlib, toolchain v4.34.1): one-sided weighted-defect rigidity for strongly connected causal bijective bit transducers and exact conservation laws for carried Rule 30, Fredkin routers, bounded-walk involutions and a period-4 carried hybrid automaton.

| Theorem | Module | Statement |
|---|---|---|
| `CarriedCaCoboundaryRigidityChallenge.causal_bij_weight_rigidity` | `CarriedCaCoboundaryRigidity.Theorems` | A strongly connected causal bijective Mealy transducer (any state type) with a nowhere-zero weight sequence and a one-sided bounded weighted defect is the identity on every finite bit word. |
| `CarriedCaCoboundaryRigidityChallenge.causal_bij_unbounded_both_sides` | `CarriedCaCoboundaryRigidity.Theorems` | A non-identity strongly connected causal bijective transducer has weighted defect unbounded above and unbounded below for every nowhere-zero weight sequence. |
| `CarriedCaCoboundaryRigidityChallenge.carriedRule30_alt_bound` | `CarriedCaCoboundaryRigidity.Theorems` | One pass of carried Rule 30 (T30) changes the alternating sum of any bit word by at most 1. |
| `CarriedCaCoboundaryRigidityChallenge.carriedRule30_iter_alt_exact` | `CarriedCaCoboundaryRigidity.Theorems` | Zero-flushed iterates of T30 conserve the alternating sum exactly for every iterate count t and every word. |
| `CarriedCaCoboundaryRigidityChallenge.altSemigroup_exact` | `CarriedCaCoboundaryRigidity.Theorems` | Every finite composition of the flushed Rule 30 and Rule 46 passes conserves the alternating sum and the value modulo 3. |
| `CarriedCaCoboundaryRigidityChallenge.fredkinRouter_iter_popcount_exact` | `CarriedCaCoboundaryRigidity.Theorems` | For every delay d and every iterate count t, the zero-flushed carried Fredkin router conserves popcount exactly. |
| `CarriedCaCoboundaryRigidityChallenge.walkInv_involutive` | `CarriedCaCoboundaryRigidity.Theorems` | For every capacity K, the bounded-walk transducer walkInv K is an involution on all finite bit words. |
| `CarriedCaCoboundaryRigidityChallenge.rule54_105_period4` | `CarriedCaCoboundaryRigidity.Theorems` | The nonlinear carried hybrid automaton T54_105 satisfies $T ^ 4 = \mathrm{id}$ on all finite bit words. |

## 72. [`binary-srs-matrix-cp-compiler/`](binary-srs-matrix-cp-compiler/)

Pure-Init Lean 4 matrix-weight plus critical-pair certificate compiler for binary string rewriting: a finite kernel-decidable check proves termination, confluence and normal-form uniqueness on all bit-strings, with an exact confluence dichotomy and infinite residue-normalizer families.

| Theorem | Module | Statement |
|---|---|---|
| `cert_sound` | `BinarySrsMatrixCpCompiler.Theorems` | If the finite checker accepts a `ConfluenceCert` for a binary SRS $R$, then $R$ is terminating, confluent and has unique normal forms on all bit-strings. |
| `convertible_iff_normalize_eq` | `BinarySrsMatrixCpCompiler.Theorems` | For a certified $R$ and all bit-strings $u, v$: $\mathrm{Convertible}(R, u, v) \iff \mathrm{normalize}(R, u) = \mathrm{normalize}(R, v)$. |
| `confluent_of_term_invariant` | `BinarySrsMatrixCpCompiler.Theorems` | A terminating SRS preserving an invariant that is injective on normal forms is confluent, has unique normal forms, and $\mathrm{Convertible}(u, v) \iff \mathrm{inv}(u) = \mathrm{inv}(v)$. |
| `ampSys_terminating` | `BinarySrsMatrixCpCompiler.Theorems` | For $b \ge 2$, $s < r$, $k, d \ge 1$, the system $\{10 \to 0^b 1,\; 0^{k+d} \to 0^k,\; 1^r \to 1^s\}$ is terminating. |
| `ampSys_confluent_iff` | `BinarySrsMatrixCpCompiler.Theorems` | For the same parameters the system is confluent if and only if $k \le b^s$ and $d \mid b^r - b^s$. |
| `mod3_convertible_iff` | `BinarySrsMatrixCpCompiler.Theorems` | Two bit-strings are convertible under the 4-rule system `mod3SRS` iff they have equal length and $\mathrm{binVal}(u) \equiv \mathrm{binVal}(v) \pmod 3$. |
| `mersenneSRS_master` | `BinarySrsMatrixCpCompiler.Theorems` | For every $m \ge 2$, the $(2^m - 1)$-rule system is terminating, confluent, has unique normal forms, and is convertible exactly when lengths agree and $\mathrm{binVal}(u) \equiv \mathrm{binVal}(v) \pmod{2^m - 1}$. |
| `fermatModSRS_master` | `BinarySrsMatrixCpCompiler.Theorems` | For every $m \ge 1$, the $(2^m + 1)$-rule system is terminating, confluent, has unique normal forms, and is convertible exactly when lengths agree and $\mathrm{binVal}(u) \equiv \mathrm{binVal}(v) \pmod{2^m + 1}$. |

## 73. [`modular-carry-residue-duality/`](modular-carry-residue-duality/)

Pure-Init Lean 4 dual MSB-Euclid / LSB-2-adic carry-transducer engine with residue-blind reciprocal popcount laws for Mersenne, Fermat and negacyclic moduli ($\forall k, d, t$).

| Theorem | Module | Statement |
|---|---|---|
| `ModularCarryResidueDualityChallenge.master_dual_carry_residue_law` | `ModularCarryResidueDuality.Theorems` | For every odd $m$, $L$ and $n < 2 ^ L$: $m \cdot \mathcal{I} _ m(n, L) = 2 ((n \bmod m) + c _ L) - O _ m(n \bmod m, L)$. |
| `ModularCarryResidueDualityChallenge.synchronized_trace_divisibility_iff` | `ModularCarryResidueDuality.Theorems` | $m \mid n \iff c _ L = 0 \iff (\forall i \le L,\ r _ i = c _ i) \iff Q _ L(n) = \lfloor n / m \rfloor$ for every odd $m$. |
| `ModularCarryResidueDualityChallenge.carry_complementarity_law` | `ModularCarryResidueDuality.Theorems` | For $m \nmid n$: $\kappa _ {\mathrm{add}}(\lfloor n / m \rfloor, Q _ L(n \bmod m)) + W _ m(n, L) = L - 1 - v _ 2(n \bmod m)$. |
| `ModularCarryResidueDualityChallenge.mersenne_dual_invariant_law` | `ModularCarryResidueDuality.Theorems` | For $m = 2 ^ k - 1$, $k \ge 2$, $t \ge 1$: $\mathcal{I} _ m(n, t k) = 0$ if $m \mid n$, else $2 - t \cdot s _ 2(n \bmod m)$. |
| `ModularCarryResidueDualityChallenge.mersenne_divisibility_threshold_iff` | `ModularCarryResidueDuality.Theorems` | For $t \ge 3$: $(2 ^ k - 1) \mid n \iff s _ 2(Q _ {t k}(n)) - s _ 2(\lfloor n / (2 ^ k - 1) \rfloor) = W _ {2 ^ k - 1}(n, t k)$. |
| `ModularCarryResidueDualityChallenge.mersenne_reciprocal_popcount_law` | `ModularCarryResidueDuality.Theorems` | $s _ 2(Q _ {t k}(r)) = t (k - s _ 2(r)) + 1 - v _ 2(r)$ for $0 < r < 2 ^ k - 1$. |
| `ModularCarryResidueDualityChallenge.negacyclic_reciprocal_popcount_law` | `ModularCarryResidueDuality.Theorems` | For odd $m \ge 3$ with $m \mid 2 ^ d + 1$: $s _ 2(Q _ {2 t d}(r)) = t d + 1 - v _ 2(r)$ for $0 < r < m$, independent of $s _ 2(r)$. |
| `ModularCarryResidueDualityChallenge.fermat_reciprocal_popcount_law` | `ModularCarryResidueDuality.Theorems` | $s _ 2(Q _ {2 t k}(r)) = t k + 1 - v _ 2(r)$ for $m = 2 ^ k + 1$ and $0 < r < m$. |

## 74. [`carry-defect-weight-spectra/`](carry-defect-weight-spectra/)

Exact Hamming-weight spectra of the carry defect between integer and carry-less multiplication: complete for multipliers 1 mod 4, the Mersenne gap law, and a certificate compiler.

| Theorem | Module | Statement |
|---|---|---|
| `spectrum_one_mod_four` | `CarryDefectWeightSpectra.Theorems` | For every $c \ge 5$ with $c \bmod 4 = 1$ and every $w \in \mathbb{N}$ there is an $x$ with $W _ c (x) = w$, i.e. $\mathcal{W}(c) = \mathbb{N}$. |
| `mersenne_zero_defect_iff` | `CarryDefectWeightSpectra.Theorems` | For $m \ge 1$ and every $x$, $\Delta(2 ^ m - 1, x) = 0$ if and only if $x$ is $m$-sparse (the $m$-fold generalization of Fibbinary numbers). |
| `mersenne_spectrum_classify` | `CarryDefectWeightSpectra.Theorems` | For $m \ge 2$ and every $w$, a weight-$w$ defect exists if and only if $w \ne 1$. |
| `defectWeight_shift_add` | `CarryDefectWeightSpectra.Theorems` | If $x < 2 ^ K$ and $c x < 2 ^ K$ then $W _ c (x + 2 ^ K y) = W _ c (x) + W _ c (y)$ for every $y$. |
| `potentialCert_sound` | `CarryDefectWeightSpectra.Theorems` | If a finite state-table certificate passes the executable check and its root has pending tails $(0, 0)$, then $\Delta(c, x) \ne 0$ implies $\mu \le W _ c (x)$ for every $x \in \mathbb{N}$, where $\mu$ is the certified bound. |
| `spectrum_23` | `CarryDefectWeightSpectra.Theorems` | A defect of weight $w$ exists for $c = 23$ if and only if $w \ne 1$. |
| `spectrum_175` | `CarryDefectWeightSpectra.Theorems` | A defect of weight $w$ exists for $c = 175$ if and only if $w = 0$ or $w \ge 3$. |
| `spectrum_211` | `CarryDefectWeightSpectra.Theorems` | Every weight $w \in \mathbb{N}$ is attained for $c = 211$, including weight $1$. |

## 75. [`carry-prefix-threshold-monoid/`](carry-prefix-threshold-monoid/)

Carry-lookahead prefix monoid: a sharp width threshold collapses all multi-input, signed-borrow and modular carry maps into a finite aperiodic threshold-step semigroup.

| Theorem | Module | Statement |
|---|---|---|
| `collapse_tree_universality` | `CarryPrefixThresholdMonoid.Theorems` | For every prefix tree whose leaf blocks have modulus at least $U - L$ and preserve the window $[L, U]$, evaluating the tree in the finite threshold-step semigroup and applying it to any carry $c \in [L, U]$ equals the exact floor-division carry action. |
| `collapse_sharpness_obstruction` | `CarryPrefixThresholdMonoid.Theorems` | If $0 < M < U - L$ there is a block of modulus $M$ whose action on $[L, U]$ is represented by no threshold-step element, so the width threshold is sharp. |
| `aperiodic` | `CarryPrefixThresholdMonoid.Theorems` | Every threshold-step element satisfies $e ^ 3 = e ^ 2$ (the semigroup is aperiodic of index at most $2$). |
| `enumBounded_length` | `CarryPrefixThresholdMonoid.Theorems` | The bounded threshold-step semigroup on $N \ge 1$ carry states has exactly $N ^ 2 - N + 1$ elements. |
| `tree_exact_carry_absorption` | `CarryPrefixThresholdMonoid.Theorems` | A prefix tree of threshold-step elements evaluates to a constant (absorbs every incoming carry) if and only if its fringe is not a resonant chain. |
| `three_input_exact_absorption` | `CarryPrefixThresholdMonoid.Theorems` | For every prefix tree of three-operand digit sums $s \le 3$, absorption holds iff the digit string is not bit-resonant, for both the unsigned and the signed-borrow encodings. |
| `three_input_resonant_triple_count` | `CarryPrefixThresholdMonoid.Theorems` | For every width $w \ge 1$ the resonant digit strings carry total weight $2 \cdot 4 ^ w$ (out of $8 ^ w$ operand triples). |
| `odd_modulus_never_absorbs` | `CarryPrefixThresholdMonoid.Theorems` | For every odd $m > 1$, every width $w$ and residue $r < m$, the base-$2$ block of width $w$ is not carry-absorbing modulo $m$. |

## 76. [`dualrail-tropical-carry-horizon/`](dualrail-tropical-carry-horizon/)

Dual-rail redundant binary addition: finite potential and relational certificates lift to exact all-width identities, with an exactly tight horizon-2 bound and no horizon for ripple carry.

| Theorem | Module | Statement |
|---|---|---|
| `potential_lift_all_widths` | `DualrailTropicalCarryHorizon.Theorems` | A valid finite potential certificate $\varphi$ for a dual-rail transducer gives, at every width $w$, $\mathrm{prefixVal} _ w (\text{out}) + 2 ^ w \varphi(\text{state} _ w) = \mathrm{prefixSum} _ w (\text{target}) + \varphi(q)$. |
| `relational_bisim_mod_eq` | `DualrailTropicalCarryHorizon.Theorems` | A valid finite relational invariant between two transducers, vanishing on the initial pair, forces equal prefix values modulo $2 ^ w$ at every width $w$. |
| `avizAdd_exact_int` | `DualrailTropicalCarryHorizon.Theorems` | For every width $w$ and all streams $x, y$: $\mathrm{prefixVal} _ w (x \boxplus y) + 2 ^ w \varphi(\text{state} _ w) = \mathrm{prefixVal} _ w (x) + \mathrm{prefixVal} _ w (y)$ for the dual-rail adder $\boxplus$. |
| `avizAdd_assoc_mod` | `DualrailTropicalCarryHorizon.Theorems` | For every width $w$ and all streams $x, y, z$, $(x \boxplus y) \boxplus z$ and $x \boxplus (y \boxplus z)$ have equal prefix values modulo $2 ^ w$. |
| `avizAdd_horizon2` | `DualrailTropicalCarryHorizon.Theorems` | If two pairs of input streams agree on positions $i - 2, i - 1, i$ then the adder outputs agree at position $i$. |
| `compileRight_equiv_all_widths` | `DualrailTropicalCarryHorizon.Theorems` | For every width $w$, environment and dual-rail expression $e$, the right-chain compilation of $e$ has the same prefix value modulo $2 ^ w$ as the direct evaluation. |
| `exact_horizon_achieved` | `DualrailTropicalCarryHorizon.Theorems` | For every outer port word and inner port, two streams differing only at position $0$ give chain outputs that differ at the computed maximal lag, so the horizon bound is attained. |
| `no_horizon_cert_for_ripple` | `DualrailTropicalCarryHorizon.Theorems` | For every $H$ and rank table $R$, the ripple-carry transducer admits no valid horizon certificate. |

## 77. [`gray-carry-whitening-transducer/`](gray-carry-whitening-transducer/)

Exact fiber counts for the Gray-coded carry word of binary addition at every width, carry-borrow Gray orthogonality, radix-B generalization and a k-operand impossibility.

| Theorem | Module | Statement |
|---|---|---|
| `gray_carry_whitening_binary` | `GrayCarryWhiteningTransducer.Theorems` | For every $w$, $c _ 0$ and $z < 2 ^ w$, exactly $3 ^ {w - \lvert z \rvert}$ pairs of $w$-bit operands have Gray-coded carry word equal to $z$ modulo $2 ^ w$. |
| `gray_carry_whitening_gray_coords` | `GrayCarryWhiteningTransducer.Theorems` | The same count $3 ^ {w - \lvert z \rvert}$ holds for the carry defect of Gray-code addition, computed in Gray coordinates. |
| `gray_carry_full_fiber_count` | `GrayCarryWhiteningTransducer.Theorems` | For $z < 2 ^ {w + 1}$ the number of pairs with Gray-coded carry word exactly $z$ is $3 ^ {w - \lvert z \bmod 2 ^ w \rvert}$ if the parity of $z$ equals $c _ 0$, and $0$ otherwise. |
| `gray_joint_carry_borrow_fiber_count` | `GrayCarryWhiteningTransducer.Theorems` | For $u, v < 2 ^ w$ the number of pairs with Gray carry word $u$ and Gray borrow word $v$ (mod $2 ^ w$) is $2 ^ {w - \lvert u \rvert - \lvert v \rvert}$ if $u \mathbin{\&} v = 0$ and $0$ otherwise. |
| `gray_carry_borrow_orthogonal` | `GrayCarryWhiteningTransducer.Theorems` | If $b + b _ 0 \le a$ then the Gray-coded carry word of $a + b + c _ 0$ and the Gray-coded borrow word of $a - b - b _ 0$ have disjoint bits. |
| `radix_carry_whitening_law` | `GrayCarryWhiteningTransducer.Theorems` | For every base $B \ge 2$, width $w$ and $z < 2 ^ w$, the carry-difference word has fiber count $\binom{B + 1}{2} ^ {w - \lvert z \rvert} \binom{B}{2} ^ {\lvert z \rvert}$. |
| `k_operand_whitening_impossibility` | `GrayCarryWhiteningTransducer.Theorems` | For every arity $k \ge 3$ the multi-operand carry slice counts are not all equal, so balanced whitening is impossible. |
| `radix_carry_borrow_orthogonality_binary_unique` | `GrayCarryWhiteningTransducer.Theorems` | For every base $B \ge 3$ there are digits $d _ 1, d _ 2 < B$ producing a carry and a borrow at the same position, so $B = 2$ is the unique radix of carry-borrow orthogonality. |

## 78. [`rhop-compressor-carry-confluence/`](rhop-compressor-carry-confluence/)

Exact capacity dichotomies for carry-free binary compressor cells at every hop depth, an exact classification of 1-hop carry-free 4:2 compressors, a carry-ledger popcount conservation law for arbitrary compressor networks, and a minimal carry-defect transducer certifying carry-save confluence.

| Theorem | Module | Statement |
|---|---|---|
| `carry_free_capacity_dichotomy` | `RhopCompressorCarryConfluence.Defs` | $\mathrm{Nonempty}(\mathrm{CarryFreeCell}\; p\; v\; M) \iff M \le 2 v \land p \le M + 2 v + 1$ for all $p \ge 1$ and all $v, M$. |
| `rhop_capacity_dichotomy` | `RhopCompressorCarryConfluence.Defs` | $\mathrm{Nonempty}(\mathrm{RHopCompressor}\; p\; v\; r) \iff p \le 2 v \cdot 2 ^ r + 1$ for all $p \ge 1$ and all $v, r$. |
| `no_carry_free_6_2` | `RhopCompressorCarryConfluence.Defs` | No 1-hop carry-free 6:2 compressor exists for any horizontal carry bound $M$. |
| `no_3hop_18_2` | `RhopCompressorCarryConfluence.Defs` | No 3-hop 18:2 compressor exists (while 3-hop 17:2 does). |
| `cell42_bijection_right` | `RhopCompressorCarryConfluence.Defs` | Every valid 1-hop carry-free 4:2 horizontal-carry function equals $h _ m$ for some mask $m$ in $\mathrm{Fin}\; 64$ (exact 64-cell classification). |
| `netW_popcount_carry_conservation` | `RhopCompressorCarryConfluence.Defs` | For any mixed compressor network with carry ledger $K$ and width $w \ge 1$: $\mathrm{popListW}(Y, w) + \sum _ {k < w - 1} K(k) + 2 K(w - 1) = \mathrm{popListW}(X, w)$. |
| `confluence_csa_3state` | `RhopCompressorCarryConfluence.Theorems` | Two networks reaching column height at most 2 are accepted by the 3-state transducer with state equal to the carry-ledger difference in $\{-1, 0, 1\}$ at every prefix. |
| `transducer_state_minimality` | `RhopCompressorCarryConfluence.Theorems` | For every $h \ge 1$ every state $q$ in $\{-(h-1), \dots, h-1\}$ is reached by some pair of equal-sum height-$h$ word lists, so $2h - 1$ states are necessary. |

## 79. [`fcsr-cyclotomic-zolotarev/`](fcsr-cyclotomic-zolotarev/)

Pure-Init Lean 4 exact 2-adic potential, reversibility, carry-bound, half-period, d-section cyclotomic and Zolotarev even-period laws for Feedback-with-Carry Shift Registers of every odd connection integer.

| Theorem | Module | Statement |
|---|---|---|
| `word_representation_exact` | `FcsrCyclotomicZolotarev.Theorems` | For every FCSR specification and state $s$ and every $n$, $q \cdot W _ n(s) + 2^n P _ q(\mathrm{step}^n s) = P _ q(s)$: an exact $2$-adic rational representation with no limits. |
| `step_bijection_on_core` | `FcsrCyclotomicZolotarev.Theorems` | On the periodic core of any FCSR, the clock tick has an exact two-sided inverse: $\mathrm{invStep}(\mathrm{step}\, s) = s$ and $\mathrm{step}(\mathrm{invStep}\, s) = s$. |
| `carry_bounds_on_core` | `FcsrCyclotomicZolotarev.Theorems` | On the periodic core the carry satisfies $0 \le m \le \mathrm{wt}(c) - 1$ (Goresky-Klapper bounds, proved constructively). |
| `universal_carry_bit_conservation` | `FcsrCyclotomicZolotarev.Theorems` | Over every periodic orbit of length $T$, $\sum _ {t < T} m _ t = (\mathrm{wt}(c) - 1) \sum _ {t < T} a _ t$. |
| `halfPeriod_certificate` | `FcsrCyclotomicZolotarev.Theorems` | If $s$ is in the core and $q \mid (2^h + 1) P _ q(s)$, then $\mathrm{step}^h s$ is the complement of $s$, $\mathrm{step}^{2h} s = s$, bits and carries are anti-periodic with shift $h$, and over $2h$ ticks $\sum a _ t = h$ and $\sum m _ t = h (\mathrm{wt}(c) - 1)$. |
| `dSection_cyclotomic_engine` | `FcsrCyclotomicZolotarev.Theorems` | If $q$ divides the $d$-section repunit $\sum _ {j < d} 2^{jk}$, then for every core state the section quantum $c(t)$ lies in $[1, d - 1]$, is $k$-periodic, $S(t) = -q \cdot c(t)$, and the section bit and carry sums obey the stated conservation laws. |
| `even_period_of_mod8_3_or_5` | `FcsrCyclotomicZolotarev.Theorems` | For every odd $q \ge 3$ with $q \equiv 3$ or $5 \pmod 8$, if $2^T \equiv 1 \pmod q$ then $T$ is even (prime or composite $q$). |
| `family_pow2_add_3` | `FcsrCyclotomicZolotarev.Theorems` | For $q = 2^k + 3$ and all $k \ge 3$: tap weight $2$, single-bit carries on the core, exact $k$-block coupling with $W _ k(s) + P(\mathrm{step}^k s) \in \{-3, -2, -1\}$, and every period of the state encoding $-1$ is even. |

## 80. [`kummer-carry-valuation-automata/`](kummer-carry-valuation-automata/)

Pure-Init Lean 4 Kummer-type exact valuation laws: shifted-bitwise Kummer collapses, Gray-code binomial sandwiches and sharp k-binomial slopes proved by finite carry-valuation automaton certificates.

| Theorem | Module | Statement |
|---|---|---|
| `v2_binom_add_popcount` | `KummerCarryValuationAutomata.Theorems` | Kummer: for all $a, b$, $v _ 2 \binom{a + b}{a} + s _ 2(a + b) = s _ 2(a) + s _ 2(b)$. |
| `v2_trinom_add_popcount` | `KummerCarryValuationAutomata.Theorems` | Trinomial Kummer: for all $a, b, c$, $v _ 2$ of the trinomial coefficient $\frac{(a + b + c)!}{a!\, b!\, c!}$ plus $s _ 2(a + b + c)$ equals $s _ 2(a) + s _ 2(b) + s _ 2(c)$. |
| `shifted_xor_kummer_exact` | `KummerCarryValuationAutomata.Theorems` | For all $n$, $2 v _ 2 \binom{n + (n \oplus 2n)}{n} = 2 s _ 2(n) + s _ 2(n \oplus 2n)$. |
| `shifted_or_kummer_exact` | `KummerCarryValuationAutomata.Theorems` | For all $n$, $v _ 2 \binom{n + (n \mathbin{|} 2n)}{n} = s _ 2(n \mathbin{|} 2n)$. |
| `gray_binom_even` | `KummerCarryValuationAutomata.Theorems` | For every $n \ge 1$, $2$ divides $\binom{n + G(n)}{n}$ where $G(n) = n \oplus \lfloor n/2 \rfloor$ is the Gray code. |
| `gray_strictly_below_shifted_xor` | `KummerCarryValuationAutomata.Theorems` | For every $n \ge 1$, $v _ 2 \binom{n + G(n)}{n} + 1 \le v _ 2 \binom{n + (n \oplus 2n)}{n}$. |
| `binom_11n_sharp_slope` | `KummerCarryValuationAutomata.Theorems` | For every $n \ge 1$, $2 v _ 2 \binom{11 n}{n} + 2 \le 5 s _ 2(n)$. |
| `binom_55n_sharp_infinite` | `KummerCarryValuationAutomata.Theorems` | On the explicit infinite family $n _ m$ (`fam55`), $4 v _ 2 \binom{55 n _ m}{n _ m} + 8 = 13 s _ 2(n _ m)$ and $s _ 2(n _ m) = 4m + 8$, so the slope $13/4$ and offset $8$ are sharp. |

## 81. [`popcount-clock-borrow-accel/`](popcount-clock-borrow-accel/)

Pure-Init Lean 4 exact unit-clock, Mersenne hitting-time, synchronous-collision, borrow-acceleration and unique-attractor-cycle laws for popcount-driven bitwise dynamics.

| Theorem | Module | Statement |
|---|---|---|
| `T_xor_unit_clock` | `PopcountClockBorrowAccel.Theorems` | For all $t, x$, the quadratic bit-moment decreases by exactly one per step: $V(T _ \oplus^t(x)) = V(x) - t$. |
| `T_xor_hits_mersenne_exact` | `PopcountClockBorrowAccel.Theorems` | If $x < 2^m$ and $V(x) + m = N$, then $T _ \oplus^N(x) = 2^m - 1$. |
| `T_xor_sync_collision_iff` | `PopcountClockBorrowAccel.Theorems` | Two numbers $x, y$ collide synchronously under $T _ \oplus$ for some $t$ if and only if $V(x) = V(y)$. |
| `T_sub_borrow_acceleration` | `PopcountClockBorrowAccel.Theorems` | If $\Phi(x) > 0$ then $2^{s _ 2(x)} \le x$, the borrow step $T _ -(x)$ equals $T _ \oplus^{1 + \mathrm{ctz}(x \gg s _ 2(x))}(x)$, and $\Phi(T _ -(x)) = \Phi(x) - 1$. |
| `T_sub_hits_mersenne_exact` | `PopcountClockBorrowAccel.Theorems` | For every $x$, after exactly $\Phi(x)$ borrow steps the orbit is a Mersenne word $2^k - 1$. |
| `F_xor_wrap_unique_2w_cycle` | `PopcountClockBorrowAccel.Theorems` | For every $w \ge 1$, the wrapped carry-free flow sends every $x < 2^w$ to $2^w - 1$, which lies on a cycle of exact length $2w$. |
| `F_sub_wrap_unique_cycle` | `PopcountClockBorrowAccel.Theorems` | For every $w \ge 1$, the wrapped borrow-coupled flow sends every $x < 2^w$ to $2^w - 1$, which lies on a cycle of exact length $w + 1$. |
| `complement_carry_borrow_conjugacy` | `PopcountClockBorrowAccel.Theorems` | For $w \ge 1$ and $x < 2^w$, complementing the borrow-coupled flow on the complement of $x$ gives exactly the carry-synchronized addition dual flow at $x$. |

## 82. [`tfunction-curvature-holonomy/`](tfunction-curvature-holonomy/)

Pure-Init Lean 4 exact single-cycle lifting laws for 1-Lipschitz 2-adic T-functions: bit-slice doubling criterion, curvature-holonomy transport, a width-4 lifting engine, universal carry-mask XOR symmetry, complete hybrid and run-family classifications, and the no-universal-finite-threshold theorem.

| Theorem | Module | Statement |
|---|---|---|
| `singleCycle_succ_iff` | `TfunctionCurvatureHolonomy.Theorems` | For a $1$-Lipschitz T-function $f$ that is single-cycle mod $2^w$, $f$ is single-cycle mod $2^{w+1}$ if and only if it has unit bit-slice derivative and odd bit-slice holonomy at $w$. |
| `holonomy_succ_iff_curvatureSum_zero` | `TfunctionCurvatureHolonomy.Theorems` | If $f$ is $1$-Lipschitz and single-cycle mod $2^{w+1}$, then its holonomy at $w + 1$ is odd if and only if its curvature sum $K _ w(f)$ vanishes mod $2^{w+2}$. |
| `lift_singleCycle_from_w4` | `TfunctionCurvatureHolonomy.Theorems` | A width-$4$ single-cycle check, unit slice derivatives at all widths $w + 1$ with $w \ge 3$, and $K _ w(f) \equiv 0 \pmod{2^{w+2}}$ for all $w \ge 3$ force $f$ to be single-cycle mod $2^w$ for every $w \ge 1$. |
| `singleCycle_xor_carryMask_iff` | `TfunctionCurvatureHolonomy.Theorems` | For every $1$-Lipschitz $g$ and every $k$, XORing $g$ with the carry-propagation mask $2k \cdot (x \oplus (x + 1))$ preserves single-cycle behaviour at every width $w \ge 1$. |
| `hybridH_singleCycle_iff_bits` | `TfunctionCurvatureHolonomy.Theorems` | The hybrid map $H _ {a,b,C,k}$ is single-cycle at every width if and only if $C _ 0 = 1$, $a _ 1 = 1 \to C _ 1 = 1$, $a _ 0 = 0 \to C _ 2 = 1$ and $b _ 0 = 1 \to C _ 3 = 1$, independently of $k$. |
| `runT_singleCycle_iff` | `TfunctionCurvatureHolonomy.Theorems` | For every $d \ge 2$ and $C$, $R _ {d,C}(x) = x + ((2 \cdot \mathrm{run} _ d(x)) \mathbin{|} C)$ is single-cycle at every width if and only if $C _ 0 = 1$ and $C _ d = 1$. |
| `runT_sharp_threshold` | `TfunctionCurvatureHolonomy.Theorems` | For every $d \ge 2$, $R _ {d,1}$ is single-cycle at every width $1 \le w \le d$ but not at width $d + 1$. |
| `no_universal_finite_threshold` | `TfunctionCurvatureHolonomy.Theorems` | For every $W \ge 1$ there is a $1$-Lipschitz T-function that is single-cycle at all widths $1 \le w \le W$ but not at width $W + 1$. |
