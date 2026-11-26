# Exact EF21 Contraction & Quantization Laws (`ef21-ternary-contraction`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **10 / 10** | **8 / 10** | **9 / 10** | **90 / 100** |

*Heuristic self-rating (weighted $3 \cdot \mathrm{Nov} + 2 \cdot \mathrm{Sur} + 2 \cdot \mathrm{Gen} + 2 \cdot \mathrm{Use} + \mathrm{Ver} = 90 / 100$): exact closed-form worst-case EF21 contraction laws across all dimensions $d \ge 1$ and all block sizes $B \ge 1$, unifying optimal ternary compression, OCP E2M1 MXFP4/NVFP4 multi-regime phase transitions, symmetric 2-bit zero-omission collapse, and $m$-bit mantissa stochastic rounding.*

## For Mathematicians

We establish five exact, universal compression and contraction theorems over $\mathbb{R}$ for distributed optimization with Error Feedback (`EF21`) and floating-point stochastic rounding (`SR`):

1. **Exact Ternary EF21 Contraction Law (`ternary_ef21_contraction_exact`):** For every dimension $d \ge 1$, optimal ternary compression $\mathcal{C} _ {\mathrm{tern}}(x) = \arg\min _ {\gamma \in \mathbb{R},\, t \in \{-1,0,1\}^d} \|x - \gamma t\| _ 2^2$ has exact worst-case contraction constant
```math
\alpha_{\mathrm{tern}}(d) = \left(\sum_{i=0}^{d-1} \left(\sqrt{i+1} - \sqrt{i}\right)^2\right)^{-1},
```
proved universally for all $x \in \mathbb{R}^d$ via sorting and Abel summation by parts on $(y _ i + \sqrt{M}\, w _ i)(y _ i - \sqrt{M}\, w _ i)$, and attained tightly at the unique extremal profile $w _ i = \sqrt{i+1} - \sqrt{i}$ where every prefix satisfies $(\sum _ {i=0}^{k-1} w _ i)^2 / k = 1$.

2. **Exact Harmonic Sandwich (`alphaTern_harmonic_sandwich`):** For every $d \ge 1$,
```math
\frac{4}{4 + H_{d-1}} \;\le\; \alpha_{\mathrm{tern}}(d) \;\le\; \frac{4}{3 + H_d},
```
proving $\alpha _ {\mathrm{tern}}(d) = \Theta(1 / \ln d)$ — an exponential separation over 1-bit sign compression ($\alpha _ {\mathrm{1-bit}}(d) = 1/d$).

3. **Universal Multi-Regime MXFP4 & NVFP4 Contraction Laws (`mxfp4_nvfp4_ef21_contraction_universal`):** For the exact nearest-neighbor OCP E2M1 quantizer $Q _ {\mathrm{E2M1}}$ onto $\{0, \pm 1/2, \pm 1, \pm 3/2, \pm 2, \pm 3, \pm 4, \pm 6\}$ and **every** block size $B \ge 1$:
   - **MXFP4** (E8M0 power-of-2 block scale, $|y _ i| \le 6$, $\max _ i |y _ i| > 3$) exhibits **three exact phase regimes** governed by
   ```math
   \alpha_{\mathrm{MXFP4}}(B) = \min\!\left(\frac{384}{B + 399},\; \frac{192}{B + 195},\; \frac{144}{B + 143}\right),
   ```
   with tight extremal configurations $(5, 1/4)$ for $1 \le B \le 8$, $(7/2, 1/4)$ for $9 \le B \le 12$, and $(3^+, 1/4)$ for $B \ge 13$ (exact values $48/53$ at $B = 16$ and $144/175$ at $B = 32$).
   - **NVFP4** (continuous/FP8 block scale, $|y _ i| \le 6$, $\max _ i |y _ i| = 6$) exhibits **two exact phase regimes** governed by
   ```math
   \alpha_{\mathrm{NVFP4}}(B) = \min\!\left(\frac{24B + 12}{25B + 11},\; \frac{576}{B + 575}\right),
   ```
   with exact attainment at $(6, 5)$ for $1 \le B \le 23$ and $(6, 1/4)$ for $B \ge 24$ (exact values $132/137$ at $B = 16$ and $576/607$ at $B = 32$).

4. **Symmetric 2-Bit Zero-Omission Collapse (`symmetric_2bit_no_zero_collapse`):** Omitting $0$ from symmetric 2-bit $\{\pm\mu, \pm 3\mu\}$ forces worst-case contraction $\alpha \le 9 / (d + 8) = O(1/d)$ on the 1-sparse unit vector $e _ 0$, attained identically at $\gamma = 3 / (d + 8)$.

5. **Mantissa Stochastic Rounding Variance Law (`mantissa_sr_variance_law`):** For every $m \in \mathbb{N}$ and every $t \in [0, 1]$,
```math
\frac{t(1 - t)}{(2^m + t)^2} \;\le\; \frac{1}{4 \cdot 2^m (2^m + 1)},
```
with exact attainment at $t^* = 2^m / (2 \cdot 2^m + 1)$, proved via a single exact sum-of-squares identity.

## For Non-Mathematicians

When thousands of GPUs train a large AI model in parallel, they constantly send massive lists of numbers (gradients) to each other. To save network bandwidth, engineers compress each number to just a few bits — for example, **1-bit** (only $+$ or $-$), **ternary** ($-, 0, +$), or **4-bit floating point** (`MXFP4` and `NVFP4`, used on modern AI accelerators). To stop compression errors from ruining training, algorithms like **EF21** keep track of leftover errors and feed them back on the next step; their speed depends directly on a guarantee called the **contraction factor** $\alpha$ (higher is better, $1$ is lossless).

This package proves the exact mathematical speed limits of these compressors for **every** vector size and block size:
- Simply adding **zero** to 1-bit compression (going from $\{-, +\}$ to $\{-, 0, +\}$) causes an exponential jump in worst-case performance: at dimension $1024$, ternary compression is **$375\times$ stronger** than 1-bit compression.
- Conversely, if you use a richer **2-bit** grid $\{\pm 1, \pm 3\}$ that *leaves out zero*, the guarantee collapses back down to $O(1/d)$ on sparse vectors — proving that including zero is structurally essential.
- For modern 4-bit hardware formats (`MXFP4` and `NVFP4`), we find the **exact** worst-case guarantees for every block size $B \ge 1$ — uncovering exact phase transitions where the worst-case input pattern switches abruptly (at $B = 9, 13$ for MXFP4 and $B = 24$ for NVFP4).

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `ternary_ef21_contraction_exact` | Universal EF21 contraction $\alpha _ {\mathrm{tern}}(d) = (\sum _ {i=0}^{d-1} (\sqrt{i+1} - \sqrt{i})^2)^{-1}$ and exact tightness at $w _ i = \sqrt{i+1} - \sqrt{i}$ for all $d \ge 1$. |
| `alphaTern_harmonic_sandwich` | Exact harmonic bounds $4 / (4 + H _ {d-1}) \le \alpha _ {\mathrm{tern}}(d) \le 4 / (3 + H _ d)$ for all $d \ge 1$. |
| `mxfp4_nvfp4_ef21_contraction_universal` | Exact universal multi-regime contraction bounds and tightness/attainment for MXFP4 (3 regimes) and NVFP4 (2 regimes) for all $B \ge 1$. |
| `symmetric_2bit_no_zero_collapse` | Exact $\alpha \le 9 / (d + 8)$ collapse and attainment at $\gamma = 3 / (d + 8)$ on $e _ 0$ for symmetric 2-bit $\{\pm\mu, \pm 3\mu\}$ for all $d \ge 1$. |
| `mantissa_sr_variance_law` | Exact worst-case relative variance $1 / (4 \cdot 2^m (2^m + 1))$ and attainment at $t^* = 2^m / (2 \cdot 2^m + 1)$ for all $m \in \mathbb{N}$. |

## Prior-Art Context

- **EF21 & Contractive Compressors:** Richtárik, Sokolov, and Fatkhullin (NeurIPS 2021) introduced EF21 for $\alpha$-contractive compressors. Standard analyses cite $\alpha = 1/d$ for 1-bit signSGD/EF-SignSGD and $\alpha = K/d$ for Top-$K$. While ternary quantization (TernGrad, Wen et al. 2017; QSGD, Alistarh et al. 2017) is widely studied as an *unbiased* compressor, the exact worst-case *contractive* constant $\alpha _ {\mathrm{tern}}(d) = (\sum (\sqrt{i+1} - \sqrt{i})^2)^{-1} = \Theta(1/\ln d)$ and its Abel-summation extremal law have not previously been formalized or characterized cleanly in the EF21 literature.
- **OCP Microscaling FP4 (`MXFP4` / `NVFP4`):** The OCP Microscaling Formats specification (v1.0, 2023) defines E2M1 with E8M0 block scaling (`B = 32`), and NVIDIA Blackwell introduced `NVFP4` (`B = 16`) with FP8 block scales. Prior work focuses on empirical SQNR and training curves; here we provide the first machine-checked exact worst-case EF21 contraction laws across all $B \ge 1$, including the exact 3-regime MXFP4 phase diagram (`B ∈ [1,8]`, `[9,12]`, `[13,∞)`) and 2-regime NVFP4 phase diagram (`B ∈ [1,23]`, `[24,∞)`).
- **Natural Compression & Mantissa SR:** Horváth et al. (2019) proved $\omega = 1/8$ for Natural Compression ($m = 0$); our `mantissa_sr_variance_law` generalizes this uniformly to all $m$-bit mantissas via a single exact algebraic sum-of-squares identity (`1/8` for Natural, `1/24` for E2M1, `1/80` for E5M2, `1/288` for E4M3).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim `#print axioms` output and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
