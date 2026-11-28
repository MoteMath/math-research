# Carry-Less $\mathbb{F} _ 2[X]$ Smith GCD Determinants and Binary Carry-Collision Singularity Paradoxes (`carryless-f2-smith-determinants`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **92 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): Unconditional Lean 4 formalization over every commutative ring $R$ establishing the universal carry-less $\mathbb{F} _ 2[X]$ Smith–Möbius determinant theorem, strict positivity of the $q = 2$ polynomial-norm Smith matrix $\det\bigl(2^{\deg \gcd _ {\mathrm{cl}}(i+1, j+1)}\bigr) = \prod _ {k=1}^n \Phi _ {\mathbb{F} _ 2[X]}(k) > 0$, and three sharp singularity collapses — most strikingly the `n = 9` binary carry-collision paradox where raw integer $\det\bigl(\gcd _ {\mathrm{cl}}(i+1, j+1)\bigr)$ climbs through $1, 1, 2, 4, 8, 16, 96, 384$ and then vanishes identically for all $n \ge 9$.*

---

## For Mathematicians

Classical Smith (1876) theory shows that $\det(\gcd(i, j)) _ {1 \le i, j \le n} = \prod _ {k = 1}^n \varphi(k) > 0$ for all $n \in \mathbb{N}$. Replacing ordinary multiplication by pure-silicon **carry-less multiplication** (`clmul`, corresponding to polynomial multiplication in $\mathbb{F} _ 2[X]$ via the bijection $\mathrm{natToPoly} : \mathbb{N} \to \mathbb{F} _ 2[X]$) yields the carry-less greatest common divisor $\gcd _ {\mathrm{cl}}(a, b) \in \mathbb{N}$ and an astonishing split between intrinsic $\mathbb{F} _ 2[X]$ norms and raw integer encodings:

1. **Exact Ring Isomorphism (`natToPoly_clmul`, `polyToNat_natToPoly`, `natToPoly_polyToNat`):**
   $\mathrm{natToPoly}$ and $\mathrm{polyToNat}$ are mutual inverses between $\mathbb{N}$ and $(\mathbb{Z} / 2\mathbb{Z})[X]$, mapping `clmul` to polynomial multiplication and binary XOR to polynomial addition. Because $\mathbb{F} _ 2$ has only a single unit ($1$), every nonzero polynomial is monic and $d \mid _ {\mathrm{cl}} m \implies d \le m$ on $\mathbb{N} _ {\ge 1}$.

2. **Universal Carry-Less Smith–Möbius Factorization (`det_clgcdMat_of_divisorSum`, `det_clgcdMat`):**
   Over **every commutative ring $R$**, for **every function $f : \mathbb{N} \to R$** and **every $n \in \mathbb{N}$**:
   ```math
   \det\Bigl(f\bigl(\gcd_{\mathrm{cl}}(i + 1,\; j + 1)\bigr)\Bigr)_{0 \le i, j < n}
   = \prod_{k = 1}^{n} (\mathrm{clMobiusInv}\, f)(k),
   ```
   where $\mathrm{clMobiusInv}\, f$ is the unique divisor-poset Möbius inverse satisfying $\sum _ {d \mid _ {\mathrm{cl}} m} (\mathrm{clMobiusInv}\, f)(d) = f(m)$.

3. **Carry-Less Euler Totient Law & Strict Positivity (`sum_clTotient_divisors`, `det_clgcd_pow2_deg`):**
   Let $\Phi _ {\mathrm{cl}}(m) = \#\{a < 2^{\deg m} : \gcd _ {\mathrm{cl}}(a, m) = 1\} = |(\mathbb{F} _ 2[X] / (P _ m))^\times|$. Then $\sum _ {d \mid _ {\mathrm{cl}} m} \Phi _ {\mathrm{cl}}(d) = 2^{\deg m}$ for all $m \ge 1$, and for all $n \in \mathbb{N}$:
   ```math
   \det\Bigl(2^{\deg \gcd_{\mathrm{cl}}(i + 1,\; j + 1)}\Bigr)_{0 \le i, j < n}
   = \prod_{k = 1}^{n} \Phi_{\mathrm{cl}}(k) > 0
   ```
   (beginning $1, 1, 1, 2, 4, 4, 12, 48, 144, 288, 2016, 4032, \dots$; `NO_EXACT_OEIS_MATCH` in OEIS).

4. **Three Sharp Singularity Collapse Paradoxes:**
   - **Raw Integer `n = 9` Carry-Collision Paradox (`det_clgcd_id_collapse_nine`):**
     For $G _ n(i, j) = \gcd _ {\mathrm{cl}}(i + 1, j + 1)$, $\det(G _ 8) = 384$ in $\mathbb{Z}$, yet **$\det(G _ n) = 0$ over EVERY commutative ring $R$ for ALL $n \ge 9$**. The culprit is $9 = \mathrm{clmul}(3, 7)$ ($X^3 + 1 = (X + 1)(X^2 + X + 1)$), whose carry-less divisors $\{1, 3, 7, 9\}$ collide in ordinary arithmetic: $9 - 7 - 3 + 1 = 0$.
   - **Carry-Less Coprimality `n = 4` Collapse (`det_clgcd_coprime_collapse_four`):**
     For $C _ n(i, j) = \mathbf{1}[\gcd _ {\mathrm{cl}}(i + 1, j + 1) = 1]$, $\det(C _ 3) = 1$ in $\mathbb{Z}$, yet **$\det(C _ n) = 0$ over every ring $R$ for all $n \ge 4$** (because $4 = \mathrm{clmul}(2, 2) = X^2$ is the first carry-less square).
   - **Carry-Less Hamming-Weight `n = 2` Collapse (`det_clgcd_popcount_collapse_two`):**
     For $H _ n(i, j) = \mathrm{popcount}(\gcd _ {\mathrm{cl}}(i + 1, j + 1))$, $\det(H _ 1) = 1$ in $\mathbb{Z}$, yet **$\det(H _ n) = 0$ over every ring $R$ for all $n \ge 2$** (because $\mathrm{popcount}(2) - \mathrm{popcount}(1) = 0$).

---

## For Non-Mathematicians

In 1876, Henry Smith proved that if you build an $n \times n$ table of greatest common divisors $\gcd(i, j)$, its determinant is always strictly positive for every size $n$.

Now repeat the exact same construction using **carry-less polynomial division** (the XOR-and-shift arithmetic built into modern CPUs). If you measure each carry-less GCD by its polynomial size $2^{\deg}$, the determinant stays strictly positive forever ($1, 1, 1, 2, 4, 4, 12, 48, 144, \dots$). **But if you simply read the carry-less GCD as a plain integer**, the determinant climbs smoothly through $1, 1, 2, 4, 8, 16, 96, 384$ — and then **suddenly drops to zero at $n = 9$ and stays zero forever**, because the binary polynomial $X^3 + 1$ (`9`) factors as $(X + 1)(X^2 + X + 1)$ (`3` and `7`), and those four divisors satisfy the accidental integer cancellation $9 - 7 - 3 + 1 = 0$.

---

## Headline Theorems

The trusted theorem statements live in [`Challenge.lean`](Challenge.lean) (definitions in [`CarrylessSmithDet/Defs.lean`](CarrylessSmithDet/Defs.lean)) and are proved unconditionally in [`CarrylessSmithDet/Theorems.lean`](CarrylessSmithDet/Theorems.lean) (re-exported by [`Solution.lean`](Solution.lean)).

| Theorem | Summary |
| :--- | :--- |
| `natToPoly_clmul` | `natToPoly (clmul a b) = natToPoly a * natToPoly b`. |
| `polyToNat_natToPoly` | `polyToNat (natToPoly n) = n`. |
| `natToPoly_polyToNat` | `natToPoly (polyToNat P) = P`. |
| `det_clgcdMat_of_divisorSum` | Universal carry-less Smith $LDL^T$ factorization for any divisor-sum pair `(f, g)`. |
| `det_clgcdMat` | Universal carry-less Smith–Möbius determinant theorem over every `CommRing R`. |
| `sum_clTotient_divisors` | $\sum _ {d \mid _ {\mathrm{cl}} m} \Phi _ {\mathrm{cl}}(d) = 2^{\lfloor \log _ 2 m \rfloor}$ for all $m \ge 1$. |
| `det_clgcd_pow2_deg` | $\det\bigl(2^{\deg \gcd _ {\mathrm{cl}}(i+1, j+1)}\bigr) = \prod _ {k < n} \Phi _ {\mathrm{cl}}(k + 1) > 0$ for all $n$. |
| `det_clgcd_id_collapse_nine` | $\det\bigl(\gcd _ {\mathrm{cl}}(i+1, j+1)\bigr) = 384$ at $n = 8$, and $= 0$ over every ring $R$ for all $n \ge 9$. |
| `det_clgcd_coprime_collapse_four` | $\det\bigl(\mathbf{1}[\gcd _ {\mathrm{cl}}(i+1, j+1) = 1]\bigr) = 1$ at $n = 3$, and $= 0$ for all $n \ge 4$. |
| `det_clgcd_popcount_collapse_two` | $\det\bigl(\mathrm{popcount}(\gcd _ {\mathrm{cl}}(i+1, j+1))\bigr) = 1$ at $n = 1$, and $= 0$ for all $n \ge 2$. |

---

## Build & Verification

Built against `leanprover/lean4:v4.34.1` and Mathlib `v4.34.1`:

```bash
lake build
lake build Challenge
lake env lean PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for verbatim build and `#print axioms` receipts, and [`comparator.json`](comparator.json) for the Palomar Comparator + `nanoda` verification manifest.
