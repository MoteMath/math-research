# Exact Hensel Lifting Engine for Mixed Bitwise-Arithmetic Diophantine Equations (`adic-2`) (`mba-hensel-block-jet-lifting`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **8 / 10** | **8 / 10** | **10 / 10** | **84 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): **Mechanism:** **The MBA-Hensel & Affine Block-Jet Lifting Engine** (standalone Lean 4.34.1, zero Mathlib, zero floating-point arithmetic, zero `sorry`, zero `native_decide`). Mixed Bitwise-Arithmetic (MBA) expressions over the 10-operator silicon algebra define exact projective systems $\mathrm{evalMod}\ w\ e : \mathbb{N} \to \mathbb{Z}/2^w\mathbb{Z}$ that are universally **2-*

## For Mathematicians

**Mechanism:** **The MBA-Hensel & Affine Block-Jet Lifting Engine** (standalone Lean 4.34.1, zero Mathlib, zero floating-point arithmetic, zero `sorry`, zero `native_decide`). Mixed Bitwise-Arithmetic (MBA) expressions over the 10-operator silicon algebra define exact projective systems $\mathrm{evalMod}\ w\ e : \mathbb{N} \to \mathbb{Z}/2^w\mathbb{Z}$ that are universally **2-adic 1-Lipschitz** (width-coherent, proved in `evalMod_coherent`). Unlike classical polynomials over $\mathbb{Z}[x]$: 1. Bitwise operators ($\land, \lor, \oplus$) have **no classical Taylor derivative**; for example, the bit-$w$ discrete derivative of $A \land B$ carries a quadratic Boolean defect $d _ w(A) \land d _ w(B)$ and depends on bit $w$ (not bit $0$) of $A(x)$ and $B(x)$. 2. Different roots of the same MBA equation can exhibit **non-uniform 2-adic ramification orders** $v(c) \in \mathbb{N}$ across disjoint residue classes $x \equiv c \pmod{2^s}$. 3. At double

## For Non-Mathematicians

**Mechanism:** **The MBA-Hensel & Affine Block-Jet Lifting Engine** (standalone Lean 4.34.1, zero Mathlib, zero floating-point arithmetic, zero `sorry`, zero `native_decide`). Mixed Bitwise-Arithmetic (MBA) expressions over the 10-operator silicon algebra define exact projective systems $\mathrm{evalMod}\ w\ e : \mathbb{N} \to \mathbb{Z}/2^w\mathbb{Z}$ that are universally **2-

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `MbaHenselBlockJetLifting/Theorems.lean`, definitions in `MbaHenselBlockJetLifting/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `evalMod_coherent` | Machine-checked infinite theorem `evalMod_coherent` proved in pure Lean 4 `Init`. |
| `symDeriv0_sound` | **Engine Theorem 3.1 (Soundness of Symbolic MBA Differential Compiler `symDeriv0`):** |
| `quadLiftFromJet_sound` | **Engine Theorem 4.2 (Single-Step Exact Quadratic Lifting & Uniqueness `w → 2*w`):** |
| `thm1_constructive_lifts` | **Main Theorem 1b (Constructive Infinite Bit-by-Bit Lifts of Both 2-Adic Roots):** |
| `witness2_one_root` | Machine-checked infinite theorem `witness2_one_root` proved in pure Lean 4 `Init`. |
| `witness3_quad_lift_concrete` | Machine-checked infinite theorem `witness3_quad_lift_concrete` proved in pure Lean 4 `Init`. |
| `sharpness1_even_mask` | Machine-checked infinite theorem `sharpness1_even_mask` proved in pure Lean 4 `Init`. |
| `sharpness3_below_mask_threshold` | Machine-checked infinite theorem `sharpness3_below_mask_threshold` proved in pure Lean 4 `Init`. |

## Prior-Art Context

- - **Classical Literature:** Classical Hensel's Lemma (e.g., for $P(x) \in \mathbb{Z} _ 2[x]$) requires differentiability via formal polynomial derivatives $P'(x)$ and does not apply to expressions mixing bitwise $\land, \lor, \oplus$. Klimov–Shamir (2002) and Anashin–Khrennikov (2009, *Applied Algebraic Dynamics*, de Gruyter) characterized *bijectivity* (measure-preservation) and *transitivity* of 1-Lipschitz T-functions over $\mathbb{Z} _ 2$ via 1-bit coordinate derivatives, and the MBA deobfuscation literature — Zhou et al. (2007), Eyrolles (2017), and Liu et al. (2021, *MBA-Blast: Unveiling and Simplifying Mixed Boolean-Arithmetic Obfuscat
- Hostile-verified PASS by `referee-4`; pure `leanprover/lean4:v4.34.1` `Init` stack with `enable_nanoda: true` and exact integer Python replay in `scripts/explore_and_verify.py`.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).