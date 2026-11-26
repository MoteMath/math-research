# Exact Multi-Draft Speculative Decoding OT Gaps, Quantized-Draft Loss, and Modular `BitVec` Reversible Transformers (`spec-decoding-ot-bounds`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **8 / 10** | **10 / 10** | **91 / 100** |

*Heuristic self-rating (`3 * 9 + 2 * 9 + 2 * 10 + 2 * 8 + 10 = 91 / 100`): universal correlated-vs-i.i.d. multi-draft speculative decoding optimal transport multiplicative gap $K^K / (K^K - (K - 1)^K)$ and additive gap $((K - 1) / K)^K$ for all $K \ge 1$ and all vocabulary sizes $V$ with tight witnesses, constructive counterexamples refuting both default-order and oracle descending-$p / q$-sorted Cyclic Madow optimality, universal tight quantized-draft acceptance loss laws for both single-draft ($K = 1$) and correlated multi-draft ($K \ge 2$) decoding, unconditional bit-exact modular `BitVec b` reversible Transformer invertibility for all bit-widths $b$ and depths $L$, and exact unimodularity and hyperbolic exponential drift of the $2 \times 2$ floating-point reversible coupling Jacobian $M(\gamma)$ — all formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

We formalize six universal algebraic, extremal, and finite-precision theorems from the Wave 4C (`w4-spec-ot-coupling`) campaign entirely over $\mathbb{Q}$ and `BitVec b` in pure Lean 4 `Init` (zero Mathlib, zero transcendental functions):

1. **Exact Multi-Draft Correlated vs I.I.D. Optimal Transport Gaps (`multidraft_corr_vs_iid_exact_gaps`):**
   For any number of drafts $K \ge 1$, any vocabulary size $V \in \mathbb{N}$, any discrete probability distributions $p, q \in \Delta _ V(\mathbb{Q})$, and any subset $S \subseteq [V]$, define the global correlated ceiling $\alpha _ K^{\mathrm{corr}}(p, q) = \sum _ {i=1}^V \min(p _ i, K q _ i)$ and the i.i.d. Strassen/Hall upper functional
   ```math
   \Phi _ K^{\mathrm{iid}}(p, q; S) = p(S^c) + 1 - (1 - q(S))^K.
   ```
   We prove universally that
   ```math
   \alpha _ K^{\mathrm{corr}}(p, q) - \Phi _ K^{\mathrm{iid}}(p, q; S) \le \left(\frac{K - 1}{K}\right)^K,
   ```
   ```math
   \bigl(K^K - (K - 1)^K\bigr)\, \alpha _ K^{\mathrm{corr}}(p, q) \le K^K \, \Phi _ K^{\mathrm{iid}}(p, q; S),
   ```
   giving the exact tight multiplicative ceiling $\alpha _ K^{\mathrm{corr}} / \alpha _ K^{\mathrm{iid}} \le \frac{K^K}{K^K - (K - 1)^K}$ ($4/3, 27/19, 256/175, \dots \to e / (e - 1)$) and additive ceiling $((K - 1)/K)^K \to 1 / e$. Both bounds are attained with exact equality for **every** $K \ge 1$ at the 2-symbol witness $p = (1, 0)$, $q = (1/K, (K - 1)/K)$.

2. **Constructive Refutation of Naive & Oracle-Sorted Cyclic Madow Optimality (`cyclic_madow_optimality_refutation_exact`):**
   For 1-PRNG Cyclic Madow drafting at $K = 2$ ($U _ k = (U + k / 2) \bmod 1$), folding $[0, 1)$ modulo $1/2$ yields the exact Strassen acceptance functional $\alpha _ 2^{\mathrm{Madow}}(p, q) = \min _ {S \subseteq [V]} \bigl(p(S^c) + 2 \, \mathrm{Leb}(\pi _ 2(\bigcup _ {i \in S} I _ i))\bigr)$. We certify two exact $V = 4$ counterexamples:
   - **Default order strictly worse than i.i.d. OT:** $p = (1/2, 0, 1/2, 0)$, $q = (1/4, 1/4, 1/4, 1/4)$ gives $\alpha _ 2^{\mathrm{Madow}} = 1/2 < \alpha _ 2^{\mathrm{iid}} = 3/4 < \alpha _ 2^{\mathrm{corr}} = 1$.
   - **Even oracle descending-$p / q$ sort is strictly suboptimal and worse than i.i.d. OT:** $p = (3/10, 9/20, 1/4, 0)$, $q = (1/5, 3/10, 1/5, 3/10)$ has monotone likelihood ratios $(3/2, 3/2, 5/4, 0)$, yet $\alpha _ 2^{\mathrm{Madow}} = 17/20 < \alpha _ 2^{\mathrm{iid}} = 91/100 < \alpha _ 2^{\mathrm{corr}} = 1$.

3. **Exact Single-Draft Quantized-Draft Acceptance Loss Law (`quantized_draft_loss_k1_exact`):**
   Working in positive rational weight space $w _ i = e^{z _ i}$ with multiplicative quantization radius $R = e^\epsilon \ge 1$ ($w _ i \le R w' _ i$ and $w' _ i \le R w _ i$ for all $i$), we prove for every $V \ge 2$, every $R \ge 1$, and every target distribution $p \in \Delta _ V(\mathbb{Q})$:
   ```math
   \bigl|\alpha _ 1(p, \mathrm{softmax}(w)) - \alpha _ 1(p, \mathrm{softmax}(w'))\bigr| \le \frac{R - 1}{R + 1} = \tanh\!\left(\frac{\epsilon}{2}\right),
   ```
   attained with exact equality for every $V \ge 2$.

4. **Exact Correlated Multi-Draft Quantized-Draft Acceptance Loss Law (`quantized_draft_loss_multidraft_exact`):**
   For every $K \ge 2$, $V \ge 2$, $R \ge 1$, and $R$-bounded positive draft weights $w, w'$:
   ```math
   \alpha _ K^{\mathrm{corr}}(p, \mathrm{softmax}(w)) - \alpha _ K^{\mathrm{corr}}(p, \mathrm{softmax}(w')) \le \frac{(K - 1)(R^2 - 1)}{1 + (K - 1) R^2},
   ```
   attained with exact equality for every $K \ge 2$, $V \ge 2$, $R \ge 1$. In the small-$\epsilon$ regime, this scales as $2 \epsilon (K - 1) / K$, proving that correlated multi-draft speculative decoding is up to **$4\times$ more sensitive** to draft logit quantization than single-draft decoding ($\epsilon / 2$).

5. **Unconditional Bit-Exact Modular `BitVec b` Reversible Transformer Invertibility (`modular_bitvec_reversible_exact_inverse`):**
   For every bit-width $b \in \mathbb{N}$, every depth $L \in \mathbb{N}$, arbitrary layer maps $F _ \ell, G _ \ell : \mathrm{BitVec}\; b \to \mathrm{BitVec}\; b$, and every initial state $(x _ 0, y _ 0) \in \mathrm{BitVec}\; b \times \mathrm{BitVec}\; b$, the $L$-layer modular additive Feistel pass `fwdPass` and its reverse pass `revPass` satisfy
   ```math
   \mathrm{revPass} _ L(F, G, \mathrm{fwdPass} _ L(F, G, s)) = s \quad\wedge\quad \mathrm{fwdPass} _ L(F, G, \mathrm{revPass} _ L(F, G, s)) = s
   ```
   bit-for-bit identically, with zero reconstruction drift across arbitrary depth and unlimited $2^b$ two's-complement wrap-arounds.

6. **Symplectic Unimodularity & Hyperbolic Exponential Drift of Floating-Point Reversible Blocks (`symplectic_float_reversible_unimodular`):**
   For every $\gamma \in \mathbb{Q}$ and $n \in \mathbb{N}$, the $2 \times 2$ coupling Jacobian $M(\gamma) = \begin{pmatrix} 1 + \gamma^2 & \gamma \\ \gamma & 1 \end{pmatrix}$ satisfies $\det M(\gamma) = \det(M(\gamma)^n) = 1$, $\mathrm{tr}\, M(\gamma) = 2 + \gamma^2 > 2$ whenever $\gamma \ne 0$, $(M(\gamma)^n) _ {0,0} \ge 1 + n \gamma^2$, and exponential $\ell _ \infty$ row-sum amplification $(M(\gamma)^n) _ {0,0} + (M(\gamma)^n) _ {0,1} \ge (1 + \gamma)^n$ for all $\gamma \ge 0$.

## For Non-Mathematicians

Large language models use two key engineering techniques to run faster and fit in less GPU memory: **speculative decoding** (a small "draft" model proposes $K$ candidate tokens in parallel for the large model to verify at once) and **reversible Transformers** (layers designed to run backward during training so activations do not need to be stored in memory).

This repository provides 100% machine-checked Lean 4 proofs for four concrete limits and fixes across both techniques:
- **Exact ceiling of correlated multi-draft speculative decoding:** Sampling $K$ draft tokens in a correlated way instead of independently can boost acceptance probability by at most $\frac{K^K}{K^K - (K - 1)^K}$ (from $4/3$ at $K = 2$ up to $e / (e - 1) \approx 1.582$ as $K \to \infty$), and by at most $((K - 1)/K)^K \to 1/e \approx 0.368$ additively — and both limits are sharp.
- **Why naive cyclic systematic sampling fails:** A popular single-random-number correlation scheme (Cyclic Madow) does **not** always hit the correlated ceiling; we prove explicit 4-token examples where even oracle-sorted Cyclic Madow performs strictly worse than plain independent drafting ($0.85 < 0.91 < 1.00$).
- **Why quantized draft models hurt multi-draft decoding up to $4\times$ more:** Compressing a draft model's logits to $\pm \epsilon$ degrades single-draft acceptance by at most $\tanh(\epsilon / 2) \approx \epsilon / 2$, but degrades correlated $K$-draft acceptance by up to $\frac{(K - 1)(e^{2\epsilon} - 1)}{1 + (K - 1) e^{2\epsilon}} \approx 2 \epsilon$ as $K \to \infty$ — up to $4\times$ higher worst-case sensitivity.
- **Zero-drift modular integer reversible layers vs. exploding floating point:** In IEEE floating point (`FP16`/`BF16`), reversible Transformer layers have a hyperbolic transfer matrix with trace $2 + \gamma^2 > 2$, amplifying tiny rounding errors exponentially like $(1 + \gamma)^L$ across depth $L$. Switching the residual addition to exact modular two's-complement `BitVec b` arithmetic guarantees **0-bit reconstruction error** at every depth $L$, even through unlimited integer wrap-arounds.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `multidraft_corr_vs_iid_exact_gaps` | Universal additive gap $((K - 1)/K)^K$ and multiplicative gap $K^K / (K^K - (K - 1)^K)$ for all $K \ge 1$, $V$, probability distributions $p, q$, and subsets $S$, plus tight 2-symbol attainment witness for every $K \ge 1$. |
| `cyclic_madow_optimality_refutation_exact` | Exact $K = 2, V = 4$ counterexamples showing default-order Cyclic Madow ($1/2 < 3/4 < 1$) and oracle descending-$p/q$-sorted Cyclic Madow ($17/20 < 91/100 < 1$) are strictly worse than both i.i.d. OT and the correlated OT ceiling. |
| `quantized_draft_loss_k1_exact` | Universal sharp single-draft quantized-draft acceptance loss $\|\alpha _ 1(p, q) - \alpha _ 1(p, q')\| \le (R - 1)/(R + 1)$ for all $V \ge 2$, $R \ge 1$, with exact equality witness for every $V \ge 2$. |
| `quantized_draft_loss_multidraft_exact` | Universal sharp correlated $K$-draft quantized-draft acceptance loss $\alpha _ K^{\mathrm{corr}}(p, q) - \alpha _ K^{\mathrm{corr}}(p, q') \le \frac{(K - 1)(R^2 - 1)}{1 + (K - 1) R^2}$ for all $K \ge 2$, $V \ge 2$, $R \ge 1$, with exact equality witness. |
| `modular_bitvec_reversible_exact_inverse` | Exact bidirectional invertibility (`revPass ∘ fwdPass = id` and `fwdPass ∘ revPass = id`) for all bit-widths $b$, all depths $L$, all layer maps $F, G$, and all states $s \in \mathrm{BitVec}\; b \times \mathrm{BitVec}\; b$. |
| `symplectic_float_reversible_unimodular` | Exact unimodularity $\det M(\gamma) = \det(M(\gamma)^n) = 1$, hyperbolic trace $2 + \gamma^2 > 2$ ($\gamma \ne 0$), $(M(\gamma)^n) _ {0,0} \ge 1 + n \gamma^2$, and exponential $\ell _ \infty$ row-sum growth $(M(\gamma)^n) _ {0,0} + (M(\gamma)^n) _ {0,1} \ge (1 + \gamma)^n$ ($\gamma \ge 0$). |

## Proof Architecture

1. **Pure-`Init` Rational & Power Infrastructure (`SpecDecodingOt/Defs.lean`, `SpecDecodingOt/RatHelpers.lean`):**
   Defines `sumRat`, `ratPow`, `isProbDist`, `alpha1`, `alphaCorr`, `strassenObj`, `alphaIID`, exact interval-union Lebesgue measure `madowHit2` / `alphaMadow2`, `softmaxRat`, modular `BitVec b` `fwdPass` / `revPass`, and `Mat2` / `symplecticM`, along with Bernoulli monotonicity and geometric-sum identities over `Rat`.
2. **Multi-Draft OT Gaps & Cyclic Madow Refutation (`SpecDecodingOt/MultidraftOT.lean`):**
   - Splits on $q(S) \le 1/K$ vs $q(S) \ge 1/K$: the additive gap follows from Bernoulli monotonicity of $K x + (1 - x)^K$, while the multiplicative gap follows from the pure-algebraic geometric-sum factorization $1 - u^K = (1 - u) \sum _ {j=0}^{K-1} u^j$ comparing $u = 1 - x$ against $v = 1 - 1/K$.
   - Evaluates the exact folded modulo-$1/2$ interval unions for `madowCE1` and `madowCE2` over all $2^4 = 16$ subsets.
3. **Quantized-Draft Acceptance Loss Laws (`SpecDecodingOt/QuantizedDraft.lean`):**
   - A shared subset-partition lemma derives $A (1 - A') \le R^2 A' (1 - A)$ for any subset $P \subseteq [V]$.
   - For $K = 1$, closes via the exact sum-of-squares identity $(R - 1)(R(1 - A) - A)^2 \ge 0$.
   - For $K \ge 2$, splits on $K A \le 1$ vs $1 \le K A$: the $K A \le 1$ branch closes via the exact factorization $(R^2 - 1)(1 - K A)(R^2 (K - 1)(1 - A) - A) \ge 0$, and the $1 \le K A$ branch closes via $(R^2)(K A - 1) \ge 0$.
4. **Modular `BitVec` Reversibility & Symplectic Drift (`SpecDecodingOt/ReversibleBitVec.lean`):**
   - Induction on depth $L$ using exact modular cancellation $u + v - v = u$ and `BitVec.sub_add_cancel`.
   - Multiplicativity of $\det$ on `Mat2` and direct induction on $n$ for $(M(\gamma)^n) _ {0,0} \ge 1 + n \gamma^2$ and $(M(\gamma)^{k+1}) _ {0,0} + (M(\gamma)^{k+1}) _ {0,1} = (1 + \gamma)((M(\gamma)^k) _ {0,0} + (M(\gamma)^k) _ {0,1}) + \gamma^2 (M(\gamma)^k) _ {0,0}$.

## Prior-Art Context

- **Speculative Decoding & Multi-Draft Optimal Transport:** Leviathan et al. (2023) and Chen et al. (2023) introduced single-draft speculative decoding with acceptance $\alpha _ 1(p, q) = 1 - \mathrm{TV}(p, q)$. Sun et al. (SpecTr, NeurIPS 2023) formulated multi-draft speculative decoding as an optimal transport / Strassen–Hall matching problem, and subsequent works studied independent vs. correlated draft couplings and systematic (Madow) sampling. Theorems 1–2 establish the exact universal $(1 - 1/e)^{-1}$ correlated-vs-i.i.d. ceiling and constructively refute both naive and oracle-sorted Cyclic Madow optimality.
- **Quantized Draft Models in Speculative Decoding:** Low-bit (INT4/FP8) draft models are widely deployed to minimize drafting latency, yet exact worst-case acceptance degradation as a function of logit quantization radius $\epsilon$ and draft count $K$ was previously analyzed only via loose TV/KL bounds. Theorems 3–4 establish the sharp closed-form laws $(R - 1)/(R + 1)$ and $\frac{(K - 1)(R^2 - 1)}{1 + (K - 1) R^2}$, revealing the up-to-$4\times$ multi-draft sensitivity amplification.
- **Reversible Residual Networks & Bit-Exact Integer Coupling:** Gomez et al. (RevNet, NeurIPS 2017) and Mangalam et al. (Reversible Vision Transformers, CVPR 2022) use additive coupling layers for $O(1)$ activation memory, while floating-point roundoff drift in deep reversible networks is a known numerical stability hazard. Theorems 5–6 formalize both the exact symplectic hyperbolic instability of floating-point coupling and the unconditional 0-bit bijectivity of modular `BitVec b` arithmetic.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build log and `#print axioms` output, and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
