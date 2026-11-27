/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrayCarryMonodromyFreezing.Defs

/-!
# Trusted Challenge Statements (`gray-carry-monodromy-freezing`)

Headline infinite theorems; proofs are supplied in `Solution.lean`.
-/

namespace GrayCarryMonodromyFreezingChallenge

open DualGrayCarry

/-- **BDFTR Soundness & Exact Bijection Theorem**:
    For ANY finite-state transducer `M`, shift `k ≥ 1`, auxiliary stream `aux`, and width `w ≥ k`,
    the bidirectional fixed-point solutions `x < 2^w` of `x >>> k = transducerEval M aux x w`
    are in exact bijection with the MSB-zero-flushed seeds `r < 2^k`. -/
theorem bdftr_exact_count {Q Aux : Type} (M : BitTransducer Q Aux) (k : Nat) (hk : 0 < k)
    (aux : Nat → Aux) (w : Nat) (hw : k ≤ w) :
    countBelow (fun x => decide (x >>> k = transducerEval M aux x w)) (2 ^ w) =
    countBelow (dfsrFlush M k hk aux w) (2 ^ k) := by
  sorry

/-- **Corollary I.1b (Untruncated $\mathbb{N}$-Stabilization)**:
    Every seed `r < 2^k` generates a finite natural number `z < 2^(L + 2*k + 1)`
    satisfying the UNTRUNCATED equation `(z ^^^ (z >>> k)) + c = z ^^^ m` in `ℕ`! -/
theorem grayRight_nat_stabilization (k L c m r : Nat) (hk : 0 < k)
    (hc : c < 2 ^ L) (hm : m < 2 ^ L) :
    let w0 := L + 2 * k + 1
    let z := evalBits (dfsrBit borrowTransducer k hk (fun i => (c.testBit i, m.testBit i)) r) w0
    z < 2 ^ w0 ∧ (z ^^^ (z >>> k)) + c = z ^^^ m := by
  sorry

/-- **THEOREM I.3 (Sign-Asymmetry Complete Annihilation Law via Carry-Trap Sink)**:
    For EVERY `k ≥ 1`, letting `d = 2^(2*k+1) - 2^k`, EVERY seed `r < 2^k` enters the
    absorbing carry-trap sink `⟨true, 1^k⟩` at step `2*k + 1`. Consequently, for EVERY `w ≥ 2*k + 1`,
    the carry-driven dual `(x ^^^ (x >>> k)) = (x + d) % 2^w` has **EXACTLY ZERO solutions**
    (in contrast, the variant `(x ^^^ (x >>> k)) = (x - d) % 2^w`, with `x - d` in place of `x + d`, has `2^k` solutions for all `w ≥ 4*k + 2`; checked by brute force for `k = 1, 2, 3`, not proved here). -/
theorem grayRight_sub_complete_annihilation (k w : Nat) (hk : 0 < k) (hw : 2 * k + 1 ≤ w) :
    let d := 2 ^ (2 * k + 1) - 2 ^ k
    countBelow (fun x => decide ((x ^^^ (x >>> k)) = (x + d) % 2 ^ w)) (2 ^ w) = 0 := by
  sorry

/-- **THEOREM II.0b (CPMF Full Cycle-Spectrum Freezing Compiler)**:
    If a finite base-width certificate `certs` passes `checkBaseCert k c0 w0 certs = true`
    (verified by the Lean kernel!), then for ALL `c ≡ c0 (mod 2^w0)` and ALL `d : Nat`
    (width `w = w0 + d`), `lstep k c w` decomposes `{0, ..., 2^w - 1}` into **EXACTLY**
    the `certs.length` disjoint cycles of lengths `{r.2 * 2^d | r ∈ certs}`! -/
theorem cpmf_full_partition_lift (k c0 w0 : Nat) (hk : 0 < k) (certs : List (Nat × Nat))
    (hcert : checkBaseCert k c0 w0 certs = true) :
    ∀ c, c % 2 ^ w0 = c0 % 2 ^ w0 → ∀ d : Nat,
      let w := w0 + d
      let f := lstep k c w
      (∀ r ∈ certs, HasMinPeriod f r.1 (r.2 * 2 ^ d)) ∧
      (∀ r₁ ∈ certs, ∀ r₂ ∈ certs, r₁ ≠ r₂ → ∀ a b, iterFn f a r₁.1 ≠ iterFn f b r₂.1) ∧
      (∀ y < 2 ^ w, ∃ r ∈ certs, ∃ j < r.2 * 2 ^ d, iterFn f j r.1 = y) := by
  sorry

/-- **THEOREM II.1 (Complete Frozen 5-Cycle Spectrum for `c ≡ 9 mod 32`)**:
    For EVERY `c` with `c % 32 = 9` and EVERY width `w ≥ 5`, `L_{1,c}(x) = ((x ^^^ (x <<< 1)) + c) % 2^w`
    decomposes `{0, ..., 2^w - 1}` into **EXACTLY 5 disjoint cycles**:
    `x = 0` of exact length `2^(w - 1)`, and `x ∈ {2, 3, 6, 7}` each of exact length `2^(w - 3)`. -/
theorem lgray1_mod32_9_exact_five_cycles (c w : Nat) (hc : c % 32 = 9) (hw : 5 ≤ w) :
    let f := lstep 1 c w
    HasMinPeriod f 0 (2 ^ (w - 1)) ∧
    HasMinPeriod f 2 (2 ^ (w - 3)) ∧
    HasMinPeriod f 3 (2 ^ (w - 3)) ∧
    HasMinPeriod f 6 (2 ^ (w - 3)) ∧
    HasMinPeriod f 7 (2 ^ (w - 3)) ∧
    (∀ r₁ ∈ cert_mod32_9, ∀ r₂ ∈ cert_mod32_9, r₁ ≠ r₂ → ∀ a b, iterFn f a r₁.1 ≠ iterFn f b r₂.1) ∧
    (∀ y < 2 ^ w, ∃ r ∈ cert_mod32_9, ∃ j < r.2 * 2 ^ (w - 5), iterFn f j r.1 = y) := by
  sorry

/-- **THEOREM II.2 (Complete Frozen 7-Cycle Spectrum for `c ≡ 19 mod 64`)**:
    For EVERY `c` with `c % 64 = 19` and EVERY width `w ≥ 6`, `L_{1,c}` decomposes `{0, ..., 2^w - 1}`
    into **EXACTLY 7 disjoint cycles**: `x ∈ {0, 1, 2}` of exact length `2^(w - 2)`,
    and `x ∈ {4, 7, 12, 15}` of exact length `2^(w - 4)`. -/
theorem lgray1_mod64_19_exact_seven_cycles (c w : Nat) (hc : c % 64 = 19) (hw : 6 ≤ w) :
    let f := lstep 1 c w
    HasMinPeriod f 0 (2 ^ (w - 2)) ∧
    HasMinPeriod f 1 (2 ^ (w - 2)) ∧
    HasMinPeriod f 2 (2 ^ (w - 2)) ∧
    HasMinPeriod f 4 (2 ^ (w - 4)) ∧
    HasMinPeriod f 7 (2 ^ (w - 4)) ∧
    HasMinPeriod f 12 (2 ^ (w - 4)) ∧
    HasMinPeriod f 15 (2 ^ (w - 4)) ∧
    (∀ r₁ ∈ cert_mod64_19, ∀ r₂ ∈ cert_mod64_19, r₁ ≠ r₂ → ∀ a b, iterFn f a r₁.1 ≠ iterFn f b r₂.1) ∧
    (∀ y < 2 ^ w, ∃ r ∈ cert_mod64_19, ∃ j < r.2 * 2 ^ (w - 6), iterFn f j r.1 = y) := by
  sorry

/-! ### Instantiation II.3: Universal Single-Cycle Law for `k ≥ 2`, Odd `c`, ALL `w ≥ 1` -/

/-- **THEOREM II.3 (Universal Single-Cycle Law for Left-Shift Gray + Increment)**:
    For EVERY shift `k ≥ 2`, EVERY odd increment `c` (`c % 2 = 1`), and EVERY width `w ≥ 1`,
    `L_{k,c}(x) = ((x ^^^ (x <<< k)) + c) % 2^w` is a **SINGLE FULL CYCLE of length `2^w`**
    covering every element of `{0, ..., 2^w - 1}`! -/
theorem lgray_ge2_odd_single_cycle (k c w : Nat) (hk : 2 ≤ k) (hc : c % 2 = 1) (hw : 1 ≤ w) :
    HasMinPeriod (lstep k c w) 0 (2 ^ w) ∧
    ∀ y < 2 ^ w, ∃ j < 2 ^ w, iterFn (lstep k c w) j 0 = y := by
  sorry

end GrayCarryMonodromyFreezingChallenge
