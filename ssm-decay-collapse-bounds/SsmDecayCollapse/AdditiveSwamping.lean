/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmDecayCollapse.DecayStall

/-!
# Theorem 3: Exact Linear Additive Swamping Divergence

Proves that when `h_0 = 1`, `a_t = 1`, and `b_t = 2^(-(p + 1))` (exact half-ULP of `1.0`),
IEEE-754 RNE tie-to-even stalls sequential accumulation permanently at `1.0`
(`seqAccum p (2^(-(p + 1))) T = 1`), whereas exact / binary-tree (Blelloch) accumulation
grows linearly as `1 + T * 2^(-(p + 1))`, yielding the exact divergence:
  `|exactAccum (2^(-(p + 1))) T - seqAccum p (2^(-(p + 1))) T| = T * 2^(-(p + 1))`
for every `p ≥ 1` and every horizon `T : Nat`.
-/

namespace SsmDecayCollapse

theorem ieeeRne_one_add_half_ulp (p : Nat) (hp : 1 ≤ p) :
    ieeeRne p (1 + zpow2 (-((p + 1 : Nat) : Int))) = 1 := by
  have hblo : zpow2 0 ≤ 1 + zpow2 (-((p + 1 : Nat) : Int)) := by
    rw [zpow2_zero]
    have hpos := zpow2_pos (-((p + 1 : Nat) : Int))
    grind
  have hbhi : 1 + zpow2 (-((p + 1 : Nat) : Int)) < zpow2 (0 + 1) := by
    have h1 : (0 : Int) + 1 = ((1 : Nat) : Int) := rfl
    rw [h1, zpow2_ofNat]
    have hlt : zpow2 (-((p + 1 : Nat) : Int)) < zpow2 0 := zpow2_lt_zpow2 (by omega)
    rw [zpow2_zero] at hlt
    have h2 : ((2 ^ 1 : Nat) : Rat) = 2 := rfl
    rw [h2]
    grind
  rw [ieeeRne_eq_of_binade p hblo hbhi]
  have hexp1 : (p : Int) - 0 = (p : Int) := by omega
  have hexp2 : 0 - (p : Int) = -(p : Int) := by omega
  rw [hexp1, hexp2]
  have hscale : (1 + zpow2 (-((p + 1 : Nat) : Int))) * zpow2 (p : Int) =
      (((2 ^ p : Nat) : Int) : Rat) + 1 / 2 := by
    rw [Rat.add_mul, Rat.one_mul, ← zpow2_add]
    have hsub : -((p + 1 : Nat) : Int) + (p : Int) = -1 := by omega
    rw [hsub, zpow2_ofNat, zpow2_neg_one]
    rfl
  rw [hscale, rneInt_midpoint]
  have heven : ((2 ^ p : Nat) : Int) % 2 = 0 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Nat.pow_succ]
    omega
  have hbeq : (((2 ^ p : Nat) : Int) % 2 == 0) = true := beq_iff_eq.mpr heven
  rw [hbeq]
  simp only [↓reduceIte]
  have hcast : (((2 ^ p : Nat) : Int) : Rat) = zpow2 (p : Int) := by
    rw [zpow2_ofNat]; rfl
  rw [hcast, zpow2_mul_cancel]

theorem seqAccum_half_ulp_eq_one (p : Nat) (hp : 1 ≤ p) (T : Nat) :
    seqAccum p (zpow2 (-((p + 1 : Nat) : Int))) T = 1 := by
  induction T with
  | zero => rfl
  | succ t ih =>
    simp only [seqAccum, ih]
    exact ieeeRne_one_add_half_ulp p hp

/-- Headline Theorem 3 (`additive_swamping_exact_divergence`). -/
theorem additive_swamping_exact_divergence :
    (∀ (p : Nat), 1 ≤ p → ∀ (T : Nat),
      seqAccum p (zpow2 (-((p + 1 : Nat) : Int))) T = 1 ∧
      ratAbs (exactAccum (zpow2 (-((p + 1 : Nat) : Int))) T -
        seqAccum p (zpow2 (-((p + 1 : Nat) : Int))) T) =
        (T : Rat) * zpow2 (-((p + 1 : Nat) : Int))) ∧
    (exactAccum (zpow2 (-8)) 1024 = 5 ∧ seqAccum 7 (zpow2 (-8)) 1024 = 1 ∧
      ratAbs (exactAccum (zpow2 (-8)) 1024 - seqAccum 7 (zpow2 (-8)) 1024) = 4) ∧
    (exactAccum (zpow2 (-8)) 131072 = 513 ∧ seqAccum 7 (zpow2 (-8)) 131072 = 1 ∧
      ratAbs (exactAccum (zpow2 (-8)) 131072 - seqAccum 7 (zpow2 (-8)) 131072) = 512) := by
  have huniv : ∀ (p : Nat), 1 ≤ p → ∀ (T : Nat),
      seqAccum p (zpow2 (-((p + 1 : Nat) : Int))) T = 1 ∧
      ratAbs (exactAccum (zpow2 (-((p + 1 : Nat) : Int))) T -
        seqAccum p (zpow2 (-((p + 1 : Nat) : Int))) T) =
        (T : Rat) * zpow2 (-((p + 1 : Nat) : Int)) := by
    intro p hp T
    have hseq := seqAccum_half_ulp_eq_one p hp T
    refine ⟨hseq, ?_⟩
    rw [hseq]
    unfold exactAccum
    have hdiff : (1 + (T : Rat) * zpow2 (-((p + 1 : Nat) : Int))) - 1 =
        (T : Rat) * zpow2 (-((p + 1 : Nat) : Int)) := by grind
    rw [hdiff]
    have hnonneg : (0 : Rat) ≤ (T : Rat) * zpow2 (-((p + 1 : Nat) : Int)) := by
      have hT : (0 : Rat) ≤ (T : Rat) := Rat.natCast_le_natCast.mpr (Nat.zero_le T)
      exact rat_mul_nonneg hT (Rat.le_of_lt (zpow2_pos _))
    exact ratAbs_of_nonneg hnonneg
  refine ⟨huniv, ?_, ?_⟩
  · have h := huniv 7 (by decide) 1024
    have hseq : seqAccum 7 (zpow2 (-8)) 1024 = 1 := h.1
    have hgap : ratAbs (exactAccum (zpow2 (-8)) 1024 - seqAccum 7 (zpow2 (-8)) 1024) =
        ((1024 : Nat) : Rat) * zpow2 (-8) := h.2
    have hval : ((1024 : Nat) : Rat) * zpow2 (-8) = 4 := by
      rw [show (-8 : Int) = -((8 : Nat) : Int) from rfl, zpow2_neg_ofNat]
      grind
    refine ⟨?_, hseq, by rw [hgap, hval]⟩
    unfold exactAccum
    rw [hval]
    grind
  · have h := huniv 7 (by decide) 131072
    have hseq : seqAccum 7 (zpow2 (-8)) 131072 = 1 := h.1
    have hgap : ratAbs (exactAccum (zpow2 (-8)) 131072 - seqAccum 7 (zpow2 (-8)) 131072) =
        ((131072 : Nat) : Rat) * zpow2 (-8) := h.2
    have hval : ((131072 : Nat) : Rat) * zpow2 (-8) = 512 := by
      rw [show (-8 : Int) = -((8 : Nat) : Int) from rfl, zpow2_neg_ofNat]
      grind
    refine ⟨?_, hseq, by rw [hgap, hval]⟩
    unfold exactAccum
    rw [hval]
    grind

end SsmDecayCollapse
