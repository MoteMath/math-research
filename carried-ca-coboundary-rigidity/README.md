# Carried Cellular-Automaton Coboundary Rigidity (`carried-ca-coboundary-rigidity`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **89 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): a universal, state-space-free conservation-versus-bijectivity no-go theorem for strongly connected causal bijective bit transducers, an exact alternating-weight conservation law for the carried Rule 30 / Rule 120 transducer `T30`, and three infinite parametric families (Fredkin routers, bounded-walk involutions, a period-4 hybrid), all checked in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

A *carried-hybrid* 1D binary cellular automaton updates site $i$ from a short spatial window and a carry bit $c _ i$ that is passed to site $i + 1$:

```math
(y _ i,\; c _ {i+1}) = \Phi(x _ {i-1}, \dots, x _ {i-d},\; x _ i,\; c _ i).
```

A single bit flip can move the carry across arbitrarily many sites, so the interaction range is infinite and spatial-window conservation tests do not apply. We model every such automaton, and every finite composition or iterate of them, as a causal Mealy bit transducer `Mealy Q`, and prove:

1. **One-sided rigidity (no-go).** If `Q` is arbitrary (even infinite), the transducer is strongly connected and causal bijective (`out q false ≠ out q true`), and `w : Nat → Int` is any nowhere-zero weight sequence, then a one-sided bound $\Delta _ w(T, x) \le M$ on the weighted defect forces $T(x) = x$ for every finite word $x$ (`causal_bij_weight_rigidity`). A non-identity machine has defect unbounded above and below (`causal_bij_unbounded_both_sides`).
2. **Carried Rule 30.** Pairing Wolfram Rule 30 output with its De Morgan dual Rule 120 carry gives a strongly connected, chaotic transducer `T30` whose alternating sum $\mathrm{alt}(x) = \sum _ i (-1)^i x _ i$ changes by at most $1$ per pass for all widths (`carriedRule30_alt_bound`), is exactly conserved by every zero-flushed iterate (`carriedRule30_iter_alt_exact`), and is conserved, together with the value modulo $3$, by every finite composition with the companion Rule 46 machine (`altSemigroup_exact`). Swapping output and carry (`T120`) trades alternating weight for popcount.
3. **Fredkin routers $\mathcal{F} _ d$ for every delay $d$.** Every zero-flushed iterate conserves popcount exactly (`fredkinRouter_iter_popcount_exact`), and the carry tunnels across runs of ones of any length.
4. **Bounded-walk involutions $\mathcal{W} _ K$ for every capacity $K$.** `walkInv K` is an involution on all finite words (`walkInv_involutive`) with exact popcount defect $s _ {\mathrm{final}} - K$; they are the sharpness family for dropping strong connectivity in item 1.
5. **Deep period 4.** The nonlinear carried automaton `T54_105` satisfies $T^4 = \mathrm{id}$ on all finite words (`rule54_105_period4`), is bijective, and has unbounded two-sided defect for every nowhere-zero weight.

Every finite certificate (bisimulation, coboundary potential, 81-state composition) is a decidable check on `Fin n` lifted to all lengths by induction, with a bridge to `BitVec w`. Single-bit perturbations of the Rule 30 table break the conservation law in all 16 cases, and `T30` grows Hamming weight unboundedly while `alt` is conserved.

## For Non-Mathematicians

Picture a long row of light switches that is updated step by step by a simple digital circuit. Each switch looks at its left neighbour, itself and a small "carry" signal handed down the row, like carrying a digit when you add numbers by hand. Because the carry can ripple along the whole row, nobody could check by finger-counting that some quantity (say, the number of switches that are on) stays under control.

This package proves that for these rippling circuits, if the circuit never loses information and any state can reach any other, then it cannot keep a one-sided lid on a weighted count of lit switches unless it does nothing at all. It then shows what *can* be conserved: a particular carried circuit built from the Rule 30 output and the Rule 120 carry (not Wolfram's ordinary synchronous Rule 30 automaton) conserves an alternating count of lit switches and the remainder after division by 3, exactly, for any row length. Families of circuits for every delay and every capacity are checked, plus a nonlinear circuit that returns to its starting row after exactly four steps. The proofs are accepted by Lean's kernel with no unfinished steps.

## Scope of the formal statement

`T30` is a hand-written sequential carried transducer (output bit from Rule 30, carry bit from Rule 120). It is not Wolfram's synchronous Rule 30 cellular automaton, and the conservation statements are about this transducer only.

## Contents

| Theorem | Statement |
| :--- | :--- |
| `causal_bij_weight_rigidity` | Strongly connected causal bijective transducer with a one-sided bounded weighted defect is the identity |
| `causal_bij_unbounded_both_sides` | A non-identity such transducer has defect unbounded above and below |
| `carriedRule30_alt_bound` | One pass of `T30` changes $\mathrm{alt}$ by at most $1$ |
| `carriedRule30_iter_alt_exact` | Zero-flushed iterates of `T30` conserve $\mathrm{alt}$ exactly |
| `altSemigroup_exact` | Words over `T30`, `T46` conserve $\mathrm{alt}$ and the value mod $3$ |
| `fredkinRouter_iter_popcount_exact` | Flushed Fredkin routers conserve popcount for all $d$ and $t$ |
| `walkInv_involutive` | The bounded-walk transducer is an involution for all $K$ |
| `rule54_105_period4` | `T54_105` satisfies $T^4 = \mathrm{id}$ on all finite words |

The file layout is `CarriedCaCoboundaryRigidity/Defs.lean` (definitions), `CarriedCaCoboundaryRigidity/Theorems.lean` (proofs), `Challenge.lean` (statements with `sorry`), `Solution.lean` (the same statements, proved), and `scripts/explore_and_verify.py` (independent exact Python replay, integers and booleans only).

## Prior Art and Credit

- **Local-window CA conservation laws:** Hattori and Takesue (1991), Boccara and Fuks (1998) and Moreira (2003) classify additive invariants of sliding-block automata of finite radius. Carried-hybrid automata have unbounded range, and the coboundary potential must depend on the hidden carry register, so those spatial flux tests do not represent it.
- **Synchronous automaton groups:** Grigorchuk, Sidki and Nekrashevych study causal bijective Mealy automata acting on the binary rooted tree. The characterization of causal bijectivity (`out q false ≠ out q true`) is classical and is used here as a foundation, not claimed as new. The one-sided weighted-defect rigidity law, the Rule 30 / Rule 120 conservation, the Fredkin and walk families and the certified period-4 lift are the contributions claimed here. No prior-art search was recorded, and the package has not been independently reviewed.
- **Anti-duplication:** no overlap with the other packages in this repository (`binary-lyness-periods`, `carry-determinants`, `zero-carry-spanning-trees` and others).

## Build and Verification

Pinned toolchain `leanprover/lean4:v4.34.1`, pure `Init`, no dependencies.

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest.
