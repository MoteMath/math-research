# Carryless Carried Resonance Curve (`carryless-carried-resonance-curve`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **7 / 10** | **6 / 10** | **10 / 10** | **78 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): Exact four-regime law for $v _ 2(a^n - \mathrm{clpow}(a, n))$ comparing carried and carry-less ($\mathbb{F} _ 2[x]$) powers, an infinitely inhabited resonance curve where the bridge is a scaled 2-adic isometry with a unique non-natural root, and a reusable Hensel-bridge lifter. Formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Write $\mathrm{clpow}(a, n)$ for the carry-less ($\mathbb{F} _ 2[x]$) power of the integer $a$ and $v _ 2$ for the 2-adic valuation. The package proves the exact value of $v _ 2(a^n - \mathrm{clpow}(a, n))$ for $n = 2^e m$ with $m$ odd:

- **Regime I** ($a \equiv 1 \bmod 4$, $v _ 2(a - 1) = r$): the valuation is $r + e$ (carried-dominated).

- **Regime II** ($a \equiv 3 \bmod 4$, $v _ 2(a + 1) = s$, $2^e < s + e$): the valuation is $2^e$ (carry-less-dominated, Frobenius dilation).

- **Regime III** ($a \equiv 3 \bmod 4$, $s + e < 2^e$): the valuation is $s + e$ (carried-dominated).

- **Regime IV, the resonance curve** $s = 2^e - e$ with $e \ge 2$: for every odd multiplier $B$ the perturbed bridge $F(n) = B\, a^{2^e(2n+1)} - \mathrm{clmul}(B, \mathrm{clpow}(a, 2^e(2n+1)))$ is an exact **scaled isometry** at scale $L = 2^e + 1$: $v _ 2(F(n)) = L + v _ 2(n - n _ *)$ for a unique non-natural 2-adic root $n _ * \in \mathbb{Z} _ 2 \setminus \mathbb{N}$. The root is invariant under every odd $B < 2^{2^e}$, and its first bit is shifted exactly by bit $2^e$ of $B$ (**bit-$2^e$ carry-coupling root-shift law**).

A reusable **Hensel-bridge lifter** (`henselLift`) turns any scaled isometry $F$ into the exact divisibility characterization $2^{L+t} \mid F(n) \iff n \bmod 2^t = \mathrm{henselLift}(F, L, t)$, with exact valuations along the lift, unboundedness of the lift for nowhere-zero $F$, and invariance under odd scalings. The resonance curve is infinitely inhabited (explicit arithmetic progression $(2q + 1) 2^{2^e - e} - 1$) and the regime boundary is kernel-sharp (for $a = 7$ the valuation is exactly $\min(2^e, 3 + e)$).

## For Non-Mathematicians

Computers can multiply whole numbers in two ways. The usual way carries digits over to the next column, like in school. The "carry-less" way, used for checksums and in some encryption hardware, throws the carries away. For a power $a^n$ the two results agree in their lowest binary digits and then disagree. This package proves exactly where they first disagree, for every $a$ and $n$, and shows that the answer depends on a surprisingly clean case split. On one special curve of parameters the two worlds are perfectly entangled: the difference behaves like a distance measure on the 2-adic numbers, so the exact digit at which they disagree tells you where you are relative to a single hidden 2-adic number that is not a whole number.

## Headline Theorems

The trusted statements are in [`Challenge.lean`](Challenge.lean) (namespace `CarrylessCarriedResonanceCurveChallenge`) and are proved in [`Solution.lean`](Solution.lean) with identical signatures.

| Theorem | Statement |
| :--- | :--- |
| `henselLift_iff_dvd` | For a scaled isometry $F$ at scale $L$: $2^{L+t} \mid F(n)$ if and only if $n \bmod 2^t$ equals the Hensel lift of $F$ at precision $t$. |
| `regime_I_carried_dominated` | If $v _ 2(a - 1) = r \ge 2$, $e \ge 1$, $m$ odd, then $v _ 2(a^{2^e m} - \mathrm{clpow}(a, 2^e m)) = r + e$. |
| `regime_II_carryless_dominated` | If $v _ 2(a + 1) = s \ge 2$, $e \ge 1$, $m$ odd and $2^e < s + e$, then the valuation is $2^e$. |
| `regime_III_carried_dominated` | If $v _ 2(a + 1) = s \ge 2$, $e \ge 1$, $m$ odd and $s + e < 2^e$, then the valuation is $s + e$. |
| `resonant_bridge_master` | On the resonance curve $v _ 2(a + 1) = 2^e - e$ with $e \ge 2$ and odd $B$, the bridge has a Hensel root below $2^t$ at every precision, an exact divisibility characterization, and an unbounded root. |
| `resonant_root_invariance_below_threshold` | The Hensel roots of the bridge are the same for every odd $B < 2^{2^e}$ as for $B = 1$. |
| `resonant_bit_root_shift_law` | The first root bit for odd $B$ equals the first root bit for $B = 1$ XOR bit $2^e$ of $B$. |
| `resonance_curve_infinitely_inhabited` | For all $e, q$, the number $x = (2q + 1) 2^{2^e - e} - 1$ lies on the resonance curve: $v _ 2(x + 1) = 2^e - e$. |

## Layout

- [`CarrylessCarriedResonanceCurve/Defs.lean`](CarrylessCarriedResonanceCurve/Defs.lean): definitions needed to state the headline theorems.
- [`CarrylessCarriedResonanceCurve/Theorems.lean`](CarrylessCarriedResonanceCurve/Theorems.lean): all proofs (zero `sorry`, zero `native_decide`, zero custom axioms, no imports beyond `Init`).
- [`scripts/explore_and_verify.py`](scripts/explore_and_verify.py): exact pure-`int` replay and sharpness checks (no floating point).

## Prior-Art Context

- **Carry-less multiplication and $\mathbb{F} _ 2[x]$:** carry-less multiplication is the CLMUL instruction (Gueron and Kounavis 2010) and the polynomial arithmetic underlying CRC and GCM. Frobenius dilation $\mathrm{clpow}(a, 2) = a(x^2)$ is the classical characteristic-2 identity.
- **Hensel lifting and 2-adic isometries:** the lifter is an exact scaled-isometry version of Hensel's lemma; compare Anashin and Khrennikov (*Applied Algebraic Dynamics*, 2009) on 2-adic isometries and T-functions.
- **Referee notes:** `PASS` by `referee-4` (#69), Novelty 4.6/5 (S-Tier). The `referee-10` prober (#134) reproduced 23,349 cases with 0 mismatches and flags two limits: the root-shift law is proved only for bit $0$ of the root (as stated in `resonant_bit_root_shift_law`), and the lifter is instantiated on a single family (the resonance-curve bridge). No prior record of the four-regime law or of the resonance-curve isometry was found by the swarm.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. Toolchain: `leanprover/lean4:v4.34.1`.
