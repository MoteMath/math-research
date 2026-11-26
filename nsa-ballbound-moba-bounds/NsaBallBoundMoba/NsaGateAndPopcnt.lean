/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NsaBallBoundMoba.BallBoundExact
import NsaBallBoundMoba.MobaBlindspot

/-!
# Theorems 5 & 6: NSA 3-Branch Convex-Gate Breakdown & 2-Bitplane POPCNT Dominance

Proves:
- **Theorem 5 (`nsa_three_branch_convex_gate_antipodal_breakdown`):** Exact algebraic
  analysis of NSA's 3-branch convex gate `O_NSA = g_1 O_cmp + g_2 O_slc + g_3 O_win`
  (`g ∈ Δ_2`): proves that when a distant antipodal needle block sits outside the sliding
  window `W` and is missed by all three branches (`Compressed`, `Mean-Key Selected`, and
  `Sliding-Window`), EVERY convex gate `g ∈ Δ_2` suffers error `‖O_NSA - O*‖_2^2 ≥ E_0^2`,
  whereas swapping Mean-Key for Zero-Sqrt Ball-Bound catches the needle block and collapses
  optimal 3-branch error to `0`.
- **Theorem 6 (`popcnt_twoplane_summary_bandwidth_dominance`):** Exact bit-level dot-product
  conservation for `2-Bitplane POPCNT` summaries (`{-3, -1, +1, +3}^d`), exact magnitude-bucket
  partition conservation, exact `4×` / `8×` bit-bandwidth reduction vs `INT8` / `FP16` (`2d` vs
  `8d` / `16d` bits, `16 B` vs `64 B` / `128 B` at `d = 64`), and zero per-coordinate multiplications.
-/

namespace NsaBallBoundMoba

/-! ### Theorem 5 Helpers: NSA 3-Branch Convex Gate -/

theorem vecSubRat_nsaGate {d : Nat} {g1 g2 g3 : Rat} (hg : g1 + g2 + g3 = 1)
    (oStar oCmp oSlc oWin : Fin d → Rat) :
    vecSubRat oStar (nsaGate g1 g2 g3 oCmp oSlc oWin) =
    fun c => g1 * vecSubRat oStar oCmp c +
             g2 * vecSubRat oStar oSlc c +
             g3 * vecSubRat oStar oWin c := by
  funext c
  unfold vecSubRat nsaGate
  have h1 : oStar c = (g1 + g2 + g3) * oStar c := by rw [hg, Rat.one_mul]
  grind

theorem dotRat_nsaGate_sub {d : Nat} {g1 g2 g3 : Rat} (hg : g1 + g2 + g3 = 1)
    (oStar oCmp oSlc oWin u : Fin d → Rat) :
    dotRat (vecSubRat oStar (nsaGate g1 g2 g3 oCmp oSlc oWin)) u =
    g1 * dotRat (vecSubRat oStar oCmp) u +
    g2 * dotRat (vecSubRat oStar oSlc) u +
    g3 * dotRat (vecSubRat oStar oWin) u := by
  rw [vecSubRat_nsaGate hg]
  unfold dotRat
  have hcongr : finSum (fun c =>
      (g1 * vecSubRat oStar oCmp c + g2 * vecSubRat oStar oSlc c + g3 * vecSubRat oStar oWin c) * u c) =
      finSum (fun c =>
        (g1 * (vecSubRat oStar oCmp c * u c) + g2 * (vecSubRat oStar oSlc c * u c)) +
        g3 * (vecSubRat oStar oWin c * u c)) := by
    apply finSum_congr
    intro c
    grind
  rw [hcongr, finSum_add, finSum_add, finSum_mul_left, finSum_mul_left, finSum_mul_left]

theorem nsaGate_const {d : Nat} {g1 g2 g3 : Rat} (hg : g1 + g2 + g3 = 1)
    (oBg : Fin d → Rat) :
    nsaGate g1 g2 g3 oBg oBg oBg = oBg := by
  funext c
  unfold nsaGate
  have h : g1 * oBg c + g2 * oBg c + g3 * oBg c = (g1 + g2 + g3) * oBg c := by grind
  rw [h, hg, Rat.one_mul]

theorem nsaGate_select_slc {d : Nat} (oCmp oSlc oWin : Fin d → Rat) :
    nsaGate 0 1 0 oCmp oSlc oWin = oSlc := by
  funext c
  unfold nsaGate
  grind

theorem normSqRat_sub_self {d : Nat} (v : Fin d → Rat) :
    normSqRat (vecSubRat v v) = 0 := by
  unfold normSqRat dotRat vecSubRat
  have hcongr : finSum (fun c : Fin d => (v c - v c) * (v c - v c)) =
      finSum (fun _ : Fin d => (0 : Rat)) := by
    apply finSum_congr
    intro c
    grind
  rw [hcongr, finSum_zero]

/-- Headline Theorem 5 (`nsa_three_branch_convex_gate_antipodal_breakdown`):
    Exact algebraic breakdown of NSA's 3-branch convex gate under a distant antipodal needle:
    1. **Universal Simplex Lower Bound (`‖O_NSA - O*‖_2^2 ≥ E_0^2`):** Whenever all three
       branches (`O_cmp`, `O_slc`, `O_win`) miss a needle along a unit direction `u`
       (`‖u‖_2^2 = 1`) by at least `E_0 ≥ 0`, EVERY convex gate `(g_1, g_2, g_3) ∈ Δ_2`
       satisfies `‖O* - O_NSA(g)‖_2^2 ≥ E_0^2`.
    2. **Equal-Background Invariance:** When all three branches output the same background
       vector `O_bg` (missing the distant needle block), EVERY convex gate `g ∈ Δ_2` outputs
       `O_bg` identically with exact squared error `‖O* - O_bg‖_2^2`.
    3. **Ball-Bound Collapse to `0` Error:** Swapping `O_slc` to Ball-Bound (which catches the
       needle so `O_slc = O*`) admits the valid gate `(0, 1, 0) ∈ Δ_2` with exact `0` error.
    4. **Antipodal Trigger Bridge:** For any `d`, `B ≥ 2`, and nonzero `q`, the antipodal block
       `antipodalBlock B q` fails Mean-Key (`q^T S_b = 0 < 2‖q‖_2^2`) while passing
       Zero-Sqrt Ball-Bound (`ballBoundPass B q S_b R_b^2 (2‖q‖_2^2)`). -/
theorem nsa_three_branch_convex_gate_antipodal_breakdown :
    (∀ (d : Nat) (oStar oCmp oSlc oWin u : Fin d → Rat) (g1 g2 g3 E0 : Rat),
      isSimplex3 g1 g2 g3 → (0 : Rat) ≤ E0 → normSqRat u = 1 →
      E0 ≤ dotRat (vecSubRat oStar oCmp) u →
      E0 ≤ dotRat (vecSubRat oStar oSlc) u →
      E0 ≤ dotRat (vecSubRat oStar oWin) u →
      E0 ≤ dotRat (vecSubRat oStar (nsaGate g1 g2 g3 oCmp oSlc oWin)) u ∧
      E0 * E0 ≤ normSqRat (vecSubRat oStar (nsaGate g1 g2 g3 oCmp oSlc oWin))) ∧
    (∀ (d : Nat) (oStar oBg : Fin d → Rat) (g1 g2 g3 : Rat),
      isSimplex3 g1 g2 g3 →
      nsaGate g1 g2 g3 oBg oBg oBg = oBg ∧
      normSqRat (vecSubRat oStar (nsaGate g1 g2 g3 oBg oBg oBg)) =
        normSqRat (vecSubRat oStar oBg)) ∧
    (∀ (d : Nat) (oStar oCmp oWin : Fin d → Rat),
      isSimplex3 0 1 0 ∧
      nsaGate 0 1 0 oCmp oStar oWin = oStar ∧
      normSqRat (vecSubRat oStar (nsaGate 0 1 0 oCmp oStar oWin)) = 0) ∧
    (∀ (d B : Nat) (q : Fin d → Int), 2 ≤ B → 0 < normSqInt q →
      dotInt q (blockSum (antipodalBlock B q)) = 0 ∧
      dotInt q (blockSum (antipodalBlock B q)) < 2 * normSqInt q ∧
      ballBoundPass B q (blockSum (antipodalBlock B q))
        (blockSqRadius (antipodalBlock B q)) (2 * normSqInt q)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d oStar oCmp oSlc oWin u g1 g2 g3 E0 ⟨hg1, hg2, hg3, hsum⟩ hE0 hu h1 h2 h3
    have hdot : E0 ≤ dotRat (vecSubRat oStar (nsaGate g1 g2 g3 oCmp oSlc oWin)) u := by
      rw [dotRat_nsaGate_sub hsum]
      have hm1 : g1 * E0 ≤ g1 * dotRat (vecSubRat oStar oCmp) u :=
        rat_mul_le_mul_of_nonneg_left h1 hg1
      have hm2 : g2 * E0 ≤ g2 * dotRat (vecSubRat oStar oSlc) u :=
        rat_mul_le_mul_of_nonneg_left h2 hg2
      have hm3 : g3 * E0 ≤ g3 * dotRat (vecSubRat oStar oWin) u :=
        rat_mul_le_mul_of_nonneg_left h3 hg3
      have htot := rat_add_le_add (rat_add_le_add hm1 hm2) hm3
      have hlhs : g1 * E0 + g2 * E0 + g3 * E0 = E0 := by
        have h : g1 * E0 + g2 * E0 + g3 * E0 = (g1 + g2 + g3) * E0 := by grind
        rw [h, hsum, Rat.one_mul]
      rw [hlhs] at htot
      exact htot
    refine ⟨hdot, ?_⟩
    have hsq := rat_sq_le_sq_of_nonneg hE0 hdot
    have hcs := cauchy_schwarz_rat (vecSubRat oStar (nsaGate g1 g2 g3 oCmp oSlc oWin)) u
    rw [hu, Rat.mul_one] at hcs
    exact Rat.le_trans hsq hcs
  · intro d oStar oBg g1 g2 g3 ⟨_, _, _, hsum⟩
    have heq := nsaGate_const hsum oBg
    exact ⟨heq, by rw [heq]⟩
  · intro d oStar oCmp oWin
    refine ⟨⟨Rat.le_refl, by decide, Rat.le_refl, by grind⟩,
            nsaGate_select_slc oCmp oStar oWin, ?_⟩
    rw [nsaGate_select_slc, normSqRat_sub_self]
  · intro d B q hB hq
    have hsum := antipodalBlock_mean_score_zero hB q
    have hpass := zero_sqrt_ball_bound_exact_soundness_zero_fn.2.2.1
      d B q (antipodalBlock B q) (2 * normSqInt q) (by omega)
      ⟨⟨0, by omega⟩, by rw [antipodalBlock_needle_score hB q]; exact Int.le_refl _⟩
    exact ⟨hsum, by omega, hpass⟩

/-! ### Theorem 6 Helpers: 2-Bitplane POPCNT Summary -/

theorem twoPlane_pointwise (a b c e : Bool) :
    decodeTwoPlane a b * decodeTwoPlane c e =
    9 * (2 * (if (b && e) && (a == c) then (1 : Int) else 0) - (if b && e then 1 else 0)) +
    3 * (2 * (if (xor b e) && (a == c) then (1 : Int) else 0) - (if xor b e then 1 else 0)) +
    1 * (2 * (if (!(b || e)) && (a == c) then (1 : Int) else 0) - (if !(b || e) then 1 else 0)) := by
  unfold decodeTwoPlane
  cases a <;> cases b <;> cases c <;> cases e <;> rfl

theorem twoPlane_dot_conserved {d : Nat} (sq mq sk mk : Fin d → Bool) :
    dotInt (fun i => decodeTwoPlane (sq i) (mq i))
           (fun i => decodeTwoPlane (sk i) (mk i)) =
    twoPlaneDotPopcnt sq mq sk mk := by
  unfold dotInt twoPlaneDotPopcnt boolCount
  dsimp only
  rw [← intFinSum_mul_left 2, ← intFinSum_sub, ← intFinSum_mul_left 9]
  rw [← intFinSum_mul_left 2, ← intFinSum_sub, ← intFinSum_mul_left 3]
  rw [← intFinSum_mul_left 2, ← intFinSum_sub, ← intFinSum_mul_left 1]
  rw [← intFinSum_add, ← intFinSum_add]
  apply intFinSum_congr
  intro i
  exact twoPlane_pointwise (sq i) (mq i) (sk i) (mk i)

theorem twoPlane_bucket_pointwise (b e : Bool) :
    (if b && e then (1 : Int) else 0) +
    (if xor b e then (1 : Int) else 0) +
    (if !(b || e) then (1 : Int) else 0) = 1 := by
  cases b <;> cases e <;> rfl

theorem twoPlane_bucket_partition {d : Nat} (mq mk : Fin d → Bool) :
    boolCount (fun i => mq i && mk i) +
    boolCount (fun i => xor (mq i) (mk i)) +
    boolCount (fun i => !(mq i || mk i)) = (d : Int) := by
  unfold boolCount
  rw [← intFinSum_add, ← intFinSum_add]
  have hcongr : intFinSum (fun i : Fin d =>
      (if mq i && mk i then (1 : Int) else 0) +
      (if xor (mq i) (mk i) then (1 : Int) else 0) +
      (if !(mq i || mk i) then (1 : Int) else 0)) =
      intFinSum (fun _ : Fin d => (1 : Int)) := by
    apply intFinSum_congr
    intro i
    exact twoPlane_bucket_pointwise (mq i) (mk i)
  rw [hcongr, intFinSum_const]
  grind

theorem twoPlane_ratio_int8 (d : Nat) (hd : 1 ≤ d) :
    ((twoPlaneBits d : Rat) / (int8Bits d : Rat)) = 1 / 4 := by
  unfold twoPlaneBits int8Bits
  have hd0 : (d : Rat) ≠ 0 := by
    intro h0
    have hpos : (0 : Rat) < (d : Rat) := nat_cast_rat_pos hd
    exact Rat.ne_of_gt hpos h0
  have h8d : ((8 * d : Nat) : Rat) ≠ 0 := by
    have heq : ((8 * d : Nat) : Rat) = 8 * (d : Rat) := by grind
    rw [heq]
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact absurd h (by decide)
    | inr h => exact hd0 h
  have hmul : (((2 * d : Nat) : Rat) / ((8 * d : Nat) : Rat)) * ((8 * d : Nat) : Rat) =
      (1 / 4 : Rat) * ((8 * d : Nat) : Rat) := by
    rw [rat_div_mul_cancel h8d]
    have h1 : ((2 * d : Nat) : Rat) = 2 * (d : Rat) := by grind
    have h2 : ((8 * d : Nat) : Rat) = 8 * (d : Rat) := by grind
    rw [h1, h2]
    grind
  have hsub : ((((2 * d : Nat) : Rat) / ((8 * d : Nat) : Rat)) - (1 / 4 : Rat)) *
      ((8 * d : Nat) : Rat) = 0 := by grind
  cases Rat.mul_eq_zero.mp hsub with
  | inl h => grind
  | inr h => exact absurd h h8d

theorem twoPlane_ratio_fp16 (d : Nat) (hd : 1 ≤ d) :
    ((twoPlaneBits d : Rat) / (fp16Bits d : Rat)) = 1 / 8 := by
  unfold twoPlaneBits fp16Bits
  have hd0 : (d : Rat) ≠ 0 := by
    intro h0
    have hpos : (0 : Rat) < (d : Rat) := nat_cast_rat_pos hd
    exact Rat.ne_of_gt hpos h0
  have h16d : ((16 * d : Nat) : Rat) ≠ 0 := by
    have heq : ((16 * d : Nat) : Rat) = 16 * (d : Rat) := by grind
    rw [heq]
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact absurd h (by decide)
    | inr h => exact hd0 h
  have hmul : (((2 * d : Nat) : Rat) / ((16 * d : Nat) : Rat)) * ((16 * d : Nat) : Rat) =
      (1 / 8 : Rat) * ((16 * d : Nat) : Rat) := by
    rw [rat_div_mul_cancel h16d]
    have h1 : ((2 * d : Nat) : Rat) = 2 * (d : Rat) := by grind
    have h2 : ((16 * d : Nat) : Rat) = 16 * (d : Rat) := by grind
    rw [h1, h2]
    grind
  have hsub : ((((2 * d : Nat) : Rat) / ((16 * d : Nat) : Rat)) - (1 / 8 : Rat)) *
      ((16 * d : Nat) : Rat) = 0 := by grind
  cases Rat.mul_eq_zero.mp hsub with
  | inl h => grind
  | inr h => exact absurd h h16d

/-- Headline Theorem 6 (`popcnt_twoplane_summary_bandwidth_dominance`):
    Exact bit-level dot-product conservation and bandwidth dominance for `2-Bitplane POPCNT`:
    1. **Exact Dot-Product Conservation (0 per-coordinate multiplies):** For ALL `d : Nat`
       and ALL `(sq, mq, sk, mk : Fin d → Bool)`, the exact integer inner product of the
       decoded `{-3, -1, +1, +3}^d` vectors equals `twoPlaneDotPopcnt sq mq sk mk`.
    2. **Exact Magnitude-Bucket Partition:** `popcnt(hh) + popcnt(hl) + popcnt(ll) = d`.
    3. **Exact `4×` / `8×` Bandwidth Reduction:** For all `d ≥ 1`, `int8Bits d = 4 * twoPlaneBits d`,
       `fp16Bits d = 8 * twoPlaneBits d`, with exact ratios `1/4` and `1/8`, and at `d = 64`
       exact byte footprints `16 B` vs `64 B` (`INT8`) and `128 B` (`FP16`). -/
theorem popcnt_twoplane_summary_bandwidth_dominance :
    (∀ (d : Nat) (sq mq sk mk : Fin d → Bool),
      dotInt (fun i => decodeTwoPlane (sq i) (mq i))
             (fun i => decodeTwoPlane (sk i) (mk i)) =
      twoPlaneDotPopcnt sq mq sk mk) ∧
    (∀ (d : Nat) (mq mk : Fin d → Bool),
      boolCount (fun i => mq i && mk i) +
      boolCount (fun i => xor (mq i) (mk i)) +
      boolCount (fun i => !(mq i || mk i)) = (d : Int)) ∧
    (∀ d : Nat, 1 ≤ d →
      int8Bits d = 4 * twoPlaneBits d ∧
      fp16Bits d = 8 * twoPlaneBits d ∧
      ((twoPlaneBits d : Rat) / (int8Bits d : Rat)) = 1 / 4 ∧
      ((twoPlaneBits d : Rat) / (fp16Bits d : Rat)) = 1 / 8) ∧
    (twoPlaneBits 64 / 8 = 16 ∧ int8Bits 64 / 8 = 64 ∧ fp16Bits 64 / 8 = 128) := by
  refine ⟨fun _ => twoPlane_dot_conserved,
          fun _ => twoPlane_bucket_partition,
          fun d hd => ⟨by unfold int8Bits twoPlaneBits; omega,
                       by unfold fp16Bits twoPlaneBits; omega,
                       twoPlane_ratio_int8 d hd,
                       twoPlane_ratio_fp16 d hd⟩,
          ⟨rfl, rfl, rfl⟩⟩

end NsaBallBoundMoba
