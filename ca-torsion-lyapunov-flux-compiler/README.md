# CA Torsion Lyapunov Flux Compiler (`ca-torsion-lyapunov-flux-compiler`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **8 / 10** | **8 / 10** | **7 / 10** | **10 / 10** | **80 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a pure-data potential/flux certificate for one-dimensional binary cellular automata, checked by kernel `decide` on $2 ^ M$ windows, that yields exact conservation laws, $\mathbb{Z}/d\mathbb{Z}$ torsion laws with no integer lift, strict Hamming-dissipation convergence with global acyclicity, traveling-wave locking and blinker convergence for every ring length $w \ge 1$, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Fix a synchronous binary cellular automaton $T$ with stencil width $k$, center offset $\mathrm{off}$ and rule table $\mathrm{rule}$ on periodic rings $\mathrm{BitVec}\ w$ of **arbitrary** length $w \ge 1$. A certificate `CACert` is pure data (no `Prop` fields): a potential table $\phi$ on $p$-bit windows, a flux (discrete gauge) table $\psi$ on $q$-bit windows, and a verification width $M$. The local defect is

```math
\Delta(u) = \phi(\mathrm{next}(u)) - \phi(\mathrm{sub}(u, \mathrm{align}, p)) + \psi(\mathrm{sub}(u, 1, q)) - \psi(\mathrm{sub}(u, 0, q)), \qquad u \in \{0, \dots, 2 ^ M - 1\}.
```

Summing over the ring, the flux telescopes to $0$ (also when $w < M$), giving the exact Gauss identity $\sum _ {i < n} \Delta(W _ M(x, i)) = \Phi _ {\mathrm{seg}}(T x, \mathrm{off}, n) - \Phi _ {\mathrm{seg}}(x, \mathrm{align}, n) + \psi(W _ q(x, n)) - \psi(W _ q(x, 0))$. A single finite Boolean check of $\Delta$ therefore proves, for **every** $w \ge 1$, every $x$ and every $t$:

1. **Exact conservation** ($\Delta \equiv 0$): $\Phi(T ^ t x) = \Phi(x)$, e.g. the count of $101$ motifs for the nonlinear non-number-conserving rule `0xac8c`.
2. **Torsion conservation** ($\Delta \equiv 0 \bmod d$): $\Phi(T ^ t x) \equiv \Phi(x) \pmod d$ for rules `0xb0f0` ($d = 3$) and `0x83bc` ($d = 2$), where no integer-valued lift exists.
3. **Strict dissipation** ($-\Delta(u) \ge c \cdot \mathbf{1}[\text{cell changes}]$): linear-time termination at a fixed point plus global acyclicity (rule `0x2c48`, $4w$ steps), rigid velocity-$1$ traveling-wave locking (rule $152$, $3w$ steps), and a microcanonical rule `0xf0e0` that is simultaneously conservative and dissipative.
4. **Two-step compilation** (`compose2Rule`): $T ^ 2$ of a $k = 3$ rule is a $k = 5$ rule, so strict dissipation on $T ^ 2$ gives period-2 blinker convergence and the absence of odd cycles and of even cycles of period at least $4$ for ECA rule $108$.

The flux $\psi$ is essential: an exact Bellman–Ford cycle obstruction shows that no width-$2$ potential with $\psi = 0$ certifies rules `0x2c48`, $152$ or `0xf0e0`.

## For Non-Mathematicians

Picture a ring of $w$ light bulbs, each on or off, that all update at once by looking at a few neighbours. Nobody can test every ring length, since there are infinitely many. Instead we hand the computer a small checklist of **local** bookkeeping rules: a score for each little pattern of bulbs and a correction term for boundary effects. If every one of the finitely many small patterns passes the checklist, the Lean kernel proves a statement about rings of **every** length at once. For example, some rules never change how many `101` patterns appear, forever. Others always settle down or lock into a steadily gliding pattern within a fixed multiple of the ring length. Two other rules conserve a count only "modulo 3" or "modulo 2", a hidden clock-arithmetic quantity that no ordinary conserved count can express.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib) formalization of a kernel-checked potential/flux/Lyapunov certificate compiler for one-dimensional binary cellular automata on periodic rings of every length.

## Scope of the formal statement

Each theorem concerns one fixed rule table (for example `0xac8c` or ECA rule $108$), for every ring length; none is a statement about all rules. The certificate check itself is a finite computation on $2^M$ windows.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `thm_pat101_conservation_0xac8c` | For every $w \ge 1$, $x$ and $t$, the nonlinear rule `0xac8c` conserves the number of cyclic $101$ windows: $\Phi(T ^ t x) = \Phi(x)$. |
| `thm_strict_fp_termination_0x2c48` | Rule `0x2c48` satisfies $T(T ^ {4w} x) = T ^ {4w} x$ on every ring of length $w \ge 1$. |
| `thm_global_acyclicity_0x2c48` | If $T ^ P x = x$ for some $P \ge 1$ under rule `0x2c48`, then $T x = x$. |
| `thm_travelingWave_locking_rule152` | Under rule $152$, $T(T ^ {3w} x) = \mathrm{ringRot}(1, T ^ {3w} x)$ for every ring and configuration. |
| `thm_microcanonical_0xf0e0` | For rule `0xf0e0` and $x ^ \ast = T ^ w x$: $T x ^ \ast = \mathrm{ringRot}(1, x ^ \ast)$ and $\# _ {11}(x ^ \ast) = \# _ {11}(x)$. |
| `thm_blinker_convergence_rule108` | For ECA rule $108$ and $y = T ^ {2w} x$: $T(T y) = y$. |
| `thm_mod3_torsion_0xb0f0` | Rule `0xb0f0` satisfies $\Phi(T ^ t x) \equiv \Phi(x) \pmod 3$ for all $w \ge 1$, $x$, $t$, where $\Phi$ is not conserved over $\mathbb{Z}$. |
| `thm_mod2_torsion_0x83bc` | Rule `0x83bc` satisfies $\Phi(T ^ t x) \equiv \Phi(x) \pmod 2$ for all $w \ge 1$, $x$, $t$, with no integer lift. |

## Proof Architecture

1. **Bit slicing (`subWin_window`):** extracting the sub-window $[a, a + p)$ of an $M$-bit window is integer shift-and-mask and equals $W _ p(x, i + a)$, so every check lives on plain naturals below $2 ^ M$.
2. **Window evolution (`window_caStep`, `localDelta_at_window`):** the $p$-bit window of $T x$ is `nextWindow` of the $M$-bit window of $x$, so $\Delta(W _ M(x, i))$ equals the ring-level potential change plus a flux difference.
3. **Telescoping and periodicity (`sumRange_localDelta_seg`, `sumRange_localDelta_ring`):** summing over $[0, n)$ telescopes the flux; summing over $[0, w)$ cancels it because $W _ q(x, w) = W _ q(x, 0)$ on every ring.
4. **Soundness meta-theorems (`soundness_conservation`, `soundness_modConservation`, `soundness_strictLyapunov_convergence`, `soundness_global_acyclicity`, `soundness_travelingWave_locking`):** `checkConservation`, `checkModConservation`, `checkLyapunov` and `checkStrictLyapunov` on a certificate imply the corresponding all-$w$ law; strict dissipation bounds the shifted Hamming distance by the potential drop, which is at most $\max \phi - \min \phi$ per cell.
5. **Two-step bridge (`caStep_compose2`):** `compose2Rule` compiles a $k = 3$ rule into a $k = 5$ rule with $T _ {\mathrm{comp}} = T ^ 2$, feeding rule $108$ into the strict checker.
6. **Discharge by `decide`:** each concrete certificate is validated by kernel `decide` on at most $2 ^ 6$ windows. Sections 7 and 8 of `Theorems.lean` hold non-vacuity and sharpness witnesses and over $30$ kernel-checked rejections of mutated certificates.

## Prior-Art Context

- **Additive conservation laws:** Hattori and Takesue (*Physica D* 49, 1991) classify additive conserved quantities of one-dimensional cellular automata; Boccara and Fuks (1998, 2002) treat number-conserving rules.
- **Group-valued conservation (closest prior art):** Pivato (*Nonlinearity* 15, 2002, "Conservation laws in cellular automata") characterizes conserved quantities valued in arbitrary abelian groups, including $\mathbb{Z}/d\mathbb{Z}$, via local flux cocycles. The `checkModConservation` mode mechanizes the finite torsion case of that criterion.
- **Lyapunov functionals:** Goles and Martínez (1990) study Lyapunov functionals for threshold automata networks; ECA rules $108$ and $152$ are classical Wolfram class II rules (Wolfram 1984; Kůrka 2003) used here as benchmark instances.
- **What this package adds (not independently reviewed):** one unified, zero-Mathlib, kernel-checked pure-data compiler covering Gauss continuity, integer and torsion conservation, flux-mediated strict dissipation with convergence bounds that are valid also for rings shorter than the verification window, and a verified two-step rule compiler; plus concrete nonlinear $k = 4$ rules with torsion laws that have no integer lift. This package has not been independently reviewed; `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
python scripts/explore_and_verify.py
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` output, [`scripts/explore_and_verify.py`](scripts/explore_and_verify.py) for the exact-integer exhaustive replay, and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` verification manifest.
