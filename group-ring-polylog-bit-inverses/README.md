# Exact $\mathbb{Z}[\mathbb{F} _ 2^k]$ Group-Ring Inversion, Parseval Duality, and the Shared-Bit Idempotent Lifting Engine (`group-ring-polylog-bit-inverses`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **9 / 10** | **10 / 10** | **9 / 10** | **9 / 10** | **10 / 10** | **93 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism Name:** **$\mathbb{Z}[\mathbb{F} _ 2^k]$ Group-Ring Inversion, Parseval Rigidity, and the Shared-Bit Idempotent Lifting Engine (`sharedLift`)***

## For Mathematicians

**Mechanism Name:** **$\mathbb{Z}[\mathbb{F} _ 2^k]$ Group-Ring Inversion, Parseval Rigidity, and the Shared-Bit Idempotent Lifting Engine (`sharedLift`)**

## For Non-Mathematicians

**Mechanism Name:** **$\mathbb{Z}[\mathbb{F} _ 2^k]$ Group-Ring Inversion, Parseval Rigidity, and the Shared-Bit Idempotent Lifting Engine (`sharedLift`)**

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `GroupRingPolylogBitInverses/Theorems.lean`, definitions in `GroupRingPolylogBitInverses/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `parseval_plancherel` | **Core Engine Theorem 3 (Exact Parseval / Plancherel Duality):** `∑_ω wht(f)(ω) * wht(g)(ω) = 2^k * ∑_x f(x) * g(x)`. |
| `higman_rigidity` | **Obstruction Theorem 1 (Pure-Silicon Higman Rigidity):** In `Z[F_2^k]` for ALL `k ≥ 0`, every exact `Z`-unit (`f * g = δ_0`) satisfies `∑_x f(x)^2 = 1`, i.e., `f = ± δ_a` (no non-trivial `Z`-units exist). |
| `binary01_no_self_inverse` | **Obstruction Theorem 5 (Pure `{0, 1}` Self-Inversion Impossibility):** No non-negative binary element `f : BVec k → {0, 1}` with `/supp(f)/ ≥ 2` can satisfy `f * f = c • δ_0` for ANY integer `c`. |
| `treeElem_wht` | **Theorem A.1 (Dual Multiplexer Tree WHT Law):** Every single Walsh coefficient of `treeElem d` is `2^d * spectralSign d ω ∈ {-2^d, +2^d}`. |
| `treeElem_polylog_identity` | Machine-checked infinite theorem `treeElem_polylog_identity` proved in pure Lean 4 `Init`. |
| `asymTree_non_self_inverse` | Machine-checked infinite theorem `asymTree_non_self_inverse` proved in pure Lean 4 `Init`. |
| `k3_no_spanning_ternary_dyadic` | **Sharpness 2 (`k = 3` Dyadic Inversion Impossibility — Exact Gap at `k = 3`):** NO full-affine-spanning ternary element on `F_2^3` is dyadically invertible (`f * g = 2^m • δ_0`). Combined with Theorem C (`∀ k ≥ 2, k ≠ 3`) and `baseA3` (`k = 3, D = 3`), this shows that the `k = 3` exception cannot be removed from Theorem C for ternary elements with full affine span. |
| `unshiftedLift_breaks_ternary` | Machine-checked finite instance: `unshiftedLift (treeElem 1) (treeElem 1)` is not ternary (proved in pure Lean 4 `Init`). |

## Prior-Art Context

- - **Classical Prior Art (Honest Distinction):** - *Higman (1940)* proved that all torsion units of $\mathbb{Z}[A]$ for an elementary abelian $2$-group $A = \mathbb{F} _ 2^k$ are trivial; the triviality of all units of $\mathbb{Z}[\mathbb{F} _ 2^k]$ is itself classical (Higman, *The units of group-rings*, Proc. London Math. Soc. 46 (1940)); `higman_rigidity` is a short Parseval proof of that known fact, mechanized here. - *Dense Boolean Bent Functions* (Rothaus 1976; Maiorana–McFarland) satisfy $f * f = 2^{2m} \delta _ 0$ on $\mathbb{F} _ 2^{2m}$, but have **100% dense** support ($/\mathrm{supp}(f)/ = N$). - *Fourier-Sparse / Plateaued Boolean Functions & Address Functions* (Nisan–Szegedy 1994; Sanyal 2019; Chiarelli–Hatami–Saks 2020).
- Built against `leanprover/lean4:v4.34.1` (pure `Init` stack; `enable_nanoda: true` in `comparator.json`); `scripts/explore_and_verify.py` re-evaluates small instances in exact integer arithmetic (it proves nothing by itself).

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).