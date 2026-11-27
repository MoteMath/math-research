# Carry-Echo and Directed-Carry Silicon Sandpile Duality Engine (`carry-echo-sandpile-duality`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **86 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): purely constructive (`[propext, Quot.sound]`, zero `Classical.choice`, zero matrix-tree theorem) Abelian toppling and harmonic-group certificate engine instantiated on the parametric Carry-Echo and Directed-Carry sandpile families across all bases $b \ge 2$ and widths $w \ge 1$, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

We formalize a reusable, purely constructive (`[propext, Quot.sound]`, zero `Classical.choice`) Abelian toppling and harmonic-group engine (`AbelianToppleSys`, `LinearBalance`, `HarmonicGroupCert`), proving confluence, odometer uniqueness (`confluent_and_odometer_unique`), burning necessity, and constructive group-isomorphism certification without invoking the matrix-tree theorem.

We instantiate the engine on two parametric silicon sandpile families for all bases $b \ge 2$ and widths $w \ge 1$: (1) the **Carry-Echo sandpile** (each toppling sends $1$ chip up and $b$ chips down, echoing carries), proving exact skew-weight conservation modulo the repunit $R _ {b, w + 1} = (b ^ {w + 1} - 1)/(b - 1)$, exact quadratic-harmonic potential drop $\Delta \Psi = (\sum f _ i)(b ^ {w + 1} - 1)$ (`carryEcho_total_avalanche_law`), local dual-skew recurrence classification and bijection with $\mathrm{Fin}(R _ {b, w + 1})$, and the **explicit closed-form Myers greedy identity** $e _ {b, w}$ (`carryEcho_explicitIdentity_eq`) with universal self-addition avalanche laws (`carryEcho_identity_laws_ge2`); and (2) the **Directed-Carry sandpile**, where every stable configuration is recurrent and chip mass satisfies exact Kummer conservation (`directedCarry_kummer_conservation`).

## For Non-Mathematicians

When a column in a base-$b$ counter overflows, it spills chips to its neighbours—an "Abelian sandpile" whose final settled state does not depend on the order of spills. We prove exact conservation and group laws for two infinite families of bit-sliced sandpiles across every base $b \ge 2$ and width $w \ge 1$: an ordinary directed-carry sandpile obeying Kummer's carry law, and a "carry-echo" sandpile whose neutral identity configuration has an explicit closed-form formula and exact avalanche counts divisible by $b ^ {w + 1} - 1$.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `CarryEchoSandpileDuality/Theorems.lean`, definitions in `CarryEchoSandpileDuality/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `carryEcho_skew_conservation` | In the carry-echo sandpile of base $b$ and width $w \ge 1$, every avalanche conserves `skewWeight` up to top-site topplings times the repunit $R _ {b, w + 1}$. |
| `carryEcho_total_avalanche_law` | For all $b \ge 2$ and $w$, the harmonic potential $\Psi$ drops by exactly $(\sum _ i f _ i)(b ^ {w + 1} - 1)$ during any carry-echo avalanche. |
| `carryEcho_recurrent_iff_dualSkew` | For all $b \ge 2$ and $w \ge 1$, a carry-echo configuration is recurrent if and only if it satisfies the local dual-skew canonicality predicate `IsDualSkew`. |
| `carryEcho_recurrent_count_left` | The harmonic encoding and Myers greedy decoding establish an exact bijection between recurrent carry-echo configurations and $\mathrm{Fin}(R _ {b, w + 1})$. |
| `carryEcho_explicitIdentity_eq` | For all $b \ge 2$ and $w \ge 1$, the explicit closed-form configuration `explicitIdentity b w` equals the sandpile group identity. |
| `carryEcho_identity_laws_ge2` | For all $b \ge 2$ and $w \ge 2$, self-addition of the identity satisfies exact harmonic value, top-site firing $1$, and chip-mass congruence modulo $b$. |
| `directedCarry_all_stable_recurrent` | In the directed-carry sandpile of base $b \ge 2$ and width $w \ge 1$, every stable configuration is recurrent. |
| `directedCarry_kummer_conservation` | In the directed-carry sandpile, chip mass drops by $(b - 1) \sum _ i f _ i + f _ {w - 1}$, matching Kummer's carry conservation law. |

## Proof Architecture

1. **Constructive Abelian toppling chassis (`AbelianToppleSys`, `confluent_and_odometer_unique`, `burning_necessity`):** proves confluence, odometer uniqueness, and burning necessity purely constructively without `Classical.choice`.
2. **Harmonic group certificate (`HarmonicGroupCert`):** certifies recurrence equivalence, bijective encoding/decoding, and unique idempotent identity from local balance identities.
3. **Carry-Echo instantiation (`carryEcho_*`):** proves skew-weight conservation, exact $(b ^ {w + 1} - 1)$ avalanche divisibility, dual-skew bijection with Myers greedy decoding, and the closed-form identity element.
4. **Directed-Carry instantiation & sharpness (`directedCarry_*`, `sharpness_*`):** proves all-stable recurrence and Kummer conservation, alongside kernel-checked boundary and cyclic counterexamples.

## Prior-Art Context

- **Classical sandpile & chip-firing lineage:** Dhar's Abelian sandpile burning algorithm (1990), **Björner, Lovász & Shor** (*Chip-firing games on graphs*, EJC 1991) for confluence and odometer uniqueness, and **Lee, Liang & Tzeng** (1991) together with **Speer** (*Asymmetric Abelian Sandpile Models*, J. Stat. Phys. 1993, §4–5) for the 1D $(1\text{ up}, b\text{ down})$ asymmetric sandpile's recurrent count $(b ^ {w + 1} - 1)/(b - 1)$ and forbidden-subconfiguration characterization.
- **Referee audit (referee-2, referee-6 Tier A+ 9.0/8.0/9.5; recorded in `REGISTRY.md`):** the purely constructive (`[propext, Quot.sound]`, zero `Classical.choice`, zero matrix-tree theorem) odometer-cancellation burning engine reused across both families, the explicit Myers greedy-encoder closed-form identity $e _ {b, w}$, the universal self-addition avalanche laws, and the exact constant-drop divisibility $(b ^ {w + 1} - 1) \mid \Delta \Psi$ are new.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
