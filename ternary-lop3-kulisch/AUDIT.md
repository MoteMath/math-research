# Verification & Soundness Audit (`ternary-lop3-kulisch`)

## 1. Environment & Package Hygiene
- **Toolchain:** `leanprover/lean4:v4.34.1` (`lean-toolchain`)
- **Dependencies:** Pure `Init` ONLY (`packages: []` in `lake-manifest.json`; zero Mathlib, zero external libraries).
- **Comparator Config:** `comparator.json` with `"enable_nanoda": true`, `"permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]`.
- **Forbidden Token Audit (outside `Challenge.lean`):**
  - `sorry` / `admit`: **0 occurrences**
  - `axiom`: **0 occurrences**
  - `native_decide`: **0 occurrences**
  - `lemma`: **0 occurrences** (strict `theorem`-only style)

---

## 2. Kernel-Checked Axiom Footprint (`scripts/PrintAxioms.lean`)

Every one of the 6 headline theorems in `TernaryLop3KulischChallenge` depends exclusively on the three standard Lean 4 axioms:

1. `TernaryLop3KulischChallenge.ternary_k2_4_lop3_exact_and_lb` → `[propext, Classical.choice, Quot.sound]`
2. `TernaryLop3KulischChallenge.ternary_k3_7_lop3_exact` → `[propext, Classical.choice, Quot.sound]`
3. `TernaryLop3KulischChallenge.harley_seal_n7_8_lop3_exact_and_lb` → `[propext, Classical.choice, Quot.sound]`
4. `TernaryLop3KulischChallenge.fp8_e4m3_exact_kulisch_49bit_int64_theorem` → `[propext, Classical.choice, Quot.sound]`
5. `TernaryLop3KulischChallenge.swar64_ternary_int2_dot_zero_overflow` → `[propext, Classical.choice, Quot.sound]`
6. `TernaryLop3KulischChallenge.fp8_e5m2_vs_e4m3_kulisch_width_gap` → `[propext, Classical.choice, Quot.sound]`

---

## 3. Non-Vacuity & Precision Verification

- **DAG Lower Bounds (`Lop3Circuits.lean`):**
  - Every `Lop3Dag` is automatically acyclic via sequential wire evaluation `evalDagGo`, so the lower bounds (`dag.length ≥ 4` for `K=2` ternary, `dag.length ≥ 5` for `K=3` ternary and `N=7` Harley–Seal) hold unconditionally over ALL `Lop3Dag`s with no side conditions.
  - Non-vacuity is directly witnessed inside each theorem by constructing the concrete `Lop3Dag` (`ternaryK2Dag` of length 4, `ternaryK3Dag` of length 7, `harleySealN7Dag` of length 8) satisfying the exact same specification predicate.
- **Exact Kulisch Threshold Refinement (`Kulisch.lean`):**
  - Exact integer division in Lean's kernel verified that the exact maximum safe `int64` length for OCP FP8-E4M3 is:
    ```math
    K_{\max} = \left\lfloor \frac{2^{63} - 1}{52{,}613{,}349{,}376} \right\rfloor = 175{,}304{,}787
    ```
    with $175{,}304{,}787 \times 52{,}613{,}349{,}376 = 9{,}223{,}372{,}005{,}716{,}262{,}912 < 2^{63}$ and $175{,}304{,}788 \times 52{,}613{,}349{,}376 = 9{,}223{,}372{,}058{,}329{,}612{,}288 \ge 2^{63}$.
  - Tightness witnesses `0x7E` (E4M3 max finite = `448`, scaled `229,376`) and `0x7B` (E5M2 max finite = `57,344`, scaled `3,758,096,384`) are kernel-checked.
- **SWAR64 Packing & Tightness (`Swar.lean`):**
  - The general lane-isolation theorem holds for all `P * S ≤ 64` and arbitrary `L`, instantiated to both RX 7900 XTX kernels (`P=6, S=10, L≤255` for ternary and `P=5, S=12, L≤455` for INT2).
  - Explicit carry-bleed counterexamples at `S=9` (`L=255`, lane 0 ≠ `1020`) and `S=11` (`L=455`, lane 0 ≠ `4095`) prove the bit-strides are exact and tight.
- **External GPU Campaign Cross-Reference:**
  - Source artifacts: `ai-math-continuous-20261126/wave4/w4-int-ternary-matmul/REPORT.md` and `results.json` (`1,135` GPU launches, `3.976 × 10^12` exact evaluations, `0` CPU replay mismatches).
  - The Lean 4 proofs are 100% self-contained and do not rely on any GPU output as an axiom; GPU-exhaustive impossibility results beyond the general fan-in bounds (`6 LOP3` for `K=3` over `1.653B` DAGs; `7 LOP3` for `N=7` over `507M` minimal-parity DAGs) are clearly distinguished in `README.md` as external GPU campaign results.
