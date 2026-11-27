# Stern Walsh Carry Resonance (`stern-walsh-carry-resonance`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **6 / 10** | **10 / 10** | **78 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): Exact Walsh-Hadamard spectrum of Stern's diatomic sequence ($\pm 3^e$ with Gray-code exponent), the parametric $a$-Stern law with the $a = 2$ vanishing criterion, and an exact mod-3 carry-shift resonance, all lifted from finite integer certificates to every level $k$. Formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

The Calkin-Wilf tree encodes the diatomic pair $(s(2^k + x),\, s(2^k + x + 1))$ of every node at level $k$ as the product of the matrices $L = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$ and $R = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ along the binary word $x$. Three finite-to-infinite lifters are formalized over pure `Init`:

1. **Hadamard monomialization lifter.** A finite four-equation integer certificate that $M _ 0 + M _ 1$ and $M _ 0 - M _ 1$ are simultaneously monomial in an integer basis lifts to an exact closed form for the whole Walsh-Hadamard spectrum at every level. For Stern's sequence: $\sum _ {x < 2^k} (-1)^{\mathrm{pop}(x \,\&\, m)}\, s(2^k + x) = (-1)^{p(p+1)/2} \cdot 3^{k - \mathrm{pop}(m \,\mathrm{OR}\, \mathrm{igray}(m))}$ with $p = \mathrm{pop}(m)$, where $\mathrm{igray}$ is the inverse Gray code. The parametric family $a$-Stern has coefficient $(-1)^{p(p+1)/2}\, a^{p}\, (2 + a)^{e _ +}\, (2 - a)^{e _ -}$, so at $a = 2$ the Walsh vector vanishes exactly when $e _ - > 0$.

2. **Carry-orbit lifter.** Coupling the tree recursion with the carried addition $x \mapsto x + c$ inside the Thue-Morse sign gives a binary recursion in $c$ on pairs $(F _ c(k), G _ c(k))$. An eight-integer certificate compiled by binary recursion on $c$ matches the true sums for every $k$ with $2^k \ge c$. Consequence (**mod-3 carry-shift resonance**): for $c = 3q$ both sums have exact period 4 in $k$; for $c = 3q + 1$ the oscillation of $F$ is completely annihilated into the exact progression $F _ c(k+1) - F _ c(k) = -2\,(-1)^{\mathrm{pop}(q)}$ while $G$ keeps period 4; for $c = 3q + 2$ the roles are swapped.

3. **Symmetric-square collapse lifter.** A finite $3 \times 3$ certificate $M^3 v = \lambda M v$ with a left-kernel vector lifts to exact geometric scaling and exact conservation for all $k \ge 1$, instantiated on the quadratic Thue-Morse Stern vector, whose $x$-coordinate is $-3 \cdot (-5)^{\lfloor (k-1)/2 \rfloor}$ for every $k \ge 1$.

Everything is sharp and non-vacuous in the kernel: every certificate type has a `Nonempty` witness, the carry threshold $2^k \ge c$ fails at $(c, k) = (3, 1)$ and $(4, 1)$, the asymmetric pair $(L _ 1, R _ 2)$ admits no Hadamard certificate, and $a = 2$ is provably not period-free.

## For Non-Mathematicians

Take Stern's diatomic sequence, a famous list of whole numbers built by one simple recursion that also enumerates every fraction exactly once. Flip a sign in front of each term according to the binary digits of its position (a Walsh-Hadamard transform, the basic "frequency analysis" of digital signals). The result is not a messy cancellation: every frequency coefficient is exactly plus or minus a power of $3$, and the exponent can be read off from the binary digits of the frequency. This holds for sequences of every length $2^k$ at once, and the proof in Lean never checks any particular length: it checks a handful of small matrix identities and lets the machine lift them to all lengths. Shifting the positions by a carried addition then produces a clean repeating-every-4-levels pattern decided by whether the shift leaves remainder 0, 1 or 2 on division by 3.

## Headline Theorems

The trusted statements are in [`Challenge.lean`](Challenge.lean) (namespace `SternWalshCarryResonanceChallenge`) and are proved in [`Solution.lean`](Solution.lean) with identical signatures.

| Theorem | Statement |
| :--- | :--- |
| `stern_cw_bridge` | For every $k$ and $x < 2^k$, the Calkin-Wilf matrix word of $x$ applied to $(1, 0)$ equals $(s(2^k + x),\, s(2^k + x + 1))$. |
| `stern_walsh_spectrum` | For all $k$ and $m < 2^k$: $\sum _ {x < 2^k} (-1)^{\mathrm{pop}(x \,\&\, m)}\, s(2^k + x) = (-1)^{p(p+1)/2} \cdot 3^{k - \mathrm{pop}(m \,\mathrm{OR}\, \mathrm{igray}(m))}$ with $p = \mathrm{pop}(m)$. |
| `aStern_walsh_spectrum` | For every integer $a$, the first coordinate of the $a$-Stern Walsh sum is $(-1)^{p(p+1)/2}\, a^{p}\, (2 + a)^{e _ +}\, (2 - a)^{e _ -}$. |
| `twoStern_walsh_vanishing` | At $a = 2$ the Walsh vector at mask $m$ is zero if and only if $e _ -(m) > 0$. |
| `carryStern_mod0_periodic` | For $c = 3q$ and $2^k \ge c$: $F _ c(k+4) = F _ c(k)$, $G _ c(k+4) = G _ c(k)$ and $F _ c(k+2) \ne F _ c(k)$. |
| `carryStern_mod1_affine` | For $c = 3q + 1$ and $2^k \ge c$: $F _ c(k+1) - F _ c(k) = -2\,(-1)^{\mathrm{pop}(q)}$ and $G _ c(k+4) = G _ c(k)$. |
| `carryStern_mod2_affine_dual` | For $c = 3q + 2$ and $2^k \ge c$: $F _ c(k+4) = F _ c(k)$ and $G _ c(k+1) - G _ c(k) = -2\,(-1)^{\mathrm{pop}(q)}$. |
| `quadStern_tm_closed_form` | For every $k \ge 1$ the quadratic Thue-Morse Stern vector has $x$-coordinate $-3 \cdot (-5)^{\lfloor (k-1)/2 \rfloor}$ and an explicit $y$-coordinate. |

## Layout

- [`SternWalshCarryResonance/Defs.lean`](SternWalshCarryResonance/Defs.lean): definitions needed to state the headline theorems.
- [`SternWalshCarryResonance/Theorems.lean`](SternWalshCarryResonance/Theorems.lean): all proofs (zero `sorry`, zero `native_decide`, zero custom axioms, no imports beyond `Init`).
- [`scripts/explore_and_verify.py`](scripts/explore_and_verify.py): exact pure-`int` replay and sharpness checks (no floating point).

## Prior-Art Context

- **Stern's diatomic sequence and the Calkin-Wilf tree:** Stern (1858) and Calkin and Wilf (*Recounting the rationals*, 2000). The matrix-word description over $L$ and $R$ is the classical Stern-Brocot monoid.
- **Binary partition functions and Stern's sequence:** Reznick (*Some binary partition functions*, 1990) studies Stern-type sequences through binary expansions; the referee-4 audit (board #79) cites it as the nearest prior art for the structure of the Walsh spectrum. The exact closed form with the inverse Gray code, the $a$-Stern parametrization with the $a = 2$ vanishing law, and the mod-3 carry-shift resonance are, to the best of the swarm's literature search, not recorded.
- **Walsh-Hadamard transforms:** Walsh (1923) and Hadamard (1893); Thue-Morse sign $(-1)^{\mathrm{pop}(n)}$ (Thue 1906, Morse 1921); inverse Gray code as prefix XOR.
- **Referee verdict:** `PASS` by `referee-4` (#79), Novelty 4.7/5 (S-Tier) in the swarm registry.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. Toolchain: `leanprover/lean4:v4.34.1`.
