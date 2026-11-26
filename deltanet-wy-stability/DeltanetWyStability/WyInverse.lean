/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltanetWyStability.RatAlg

/-!
# Theorem 3: Exact Chunkwise WY Inverse Identity & Aligned Contraction vs Quantized Blowup
-/

namespace DeltanetWyStability

/-- Telescoping finite sum over `m ∈ [lo, hi)` inside `Fin C`. -/
theorem sumFin_telescope (C lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ C) (g : Nat → Rat) :
    sumFin (fun m : Fin C => if lo ≤ m.val ∧ m.val < hi then g (m.val + 1) - g m.val else 0) =
      g hi - g lo := by
  induction hi with
  | zero =>
    have hlo0 : lo = 0 := Nat.eq_zero_of_le_zero hlo
    subst hlo0
    rw [sumFin_congr (g := fun _ => 0)]
    · rw [sumFin_zero]; grind
    · intro m; simp
  | succ k ih =>
    by_cases hlk : lo = k + 1
    · subst hlk
      rw [sumFin_congr (g := fun _ => 0)]
      · rw [sumFin_zero]; grind
      · intro m
        have hfalse : ¬ (k + 1 ≤ m.val ∧ m.val < k + 1) := by omega
        simp [hfalse]
    · have hlo_le : lo ≤ k := by omega
      have hk_lt : k < C := by omega
      let mk : Fin C := ⟨k, hk_lt⟩
      have hsplit : sumFin (fun m : Fin C => if lo ≤ m.val ∧ m.val < k + 1 then g (m.val + 1) - g m.val else 0) =
          sumFin (fun m : Fin C =>
            (if lo ≤ m.val ∧ m.val < k then g (m.val + 1) - g m.val else 0) +
            (if m = mk then g (k + 1) - g k else 0)) := by
        apply sumFin_congr
        intro m
        by_cases hmk : m = mk
        · subst hmk
          have h1 : lo ≤ k ∧ k < k + 1 := ⟨hlo_le, Nat.lt_succ_self k⟩
          simp only [mk, h1, ↓reduceIte]; grind
        · have hne : m.val ≠ k := fun hv => hmk (Fin.ext hv)
          have heqv : (lo ≤ m.val ∧ m.val < k + 1) ↔ (lo ≤ m.val ∧ m.val < k) := by omega
          by_cases hc : lo ≤ m.val ∧ m.val < k
          · have hc' : lo ≤ m.val ∧ m.val < k + 1 := heqv.mpr hc
            simp only [hc, hc', hmk, ↓reduceIte]; grind
          · have hc' : ¬ (lo ≤ m.val ∧ m.val < k + 1) := fun h => hc (heqv.mp h)
            simp only [hc, hc', hmk, ↓reduceIte]; grind
      rw [hsplit, sumFin_add_fn, ih hlo_le (Nat.le_of_lt hk_lt)]
      have hsingle : sumFin (fun m : Fin C => if m = mk then g (k + 1) - g k else 0) = g (k + 1) - g k := by
        rw [sumFin_single mk]
        · simp
        · intro m hm; simp [hm]
      rw [hsingle]
      grind

/-- Universal exact chunkwise WY inverse identity `(I + L) * T = I` for ALL `C, d, α, betas, keys`. -/
theorem wy_inverse_exact (C d : Nat) (α : Rat) (betas : Fin C → Rat) (keys : Fin C → Fin d → Rat) :
    matMul (matAdd (idMat C) (wyL C d α betas keys)) (wyT C d α betas keys) = idMat C := by
  funext i j
  unfold matMul matAdd idMat
  by_cases hij : i = j
  · subst hij
    rw [sumFin_single i]
    · simp only [↓reduceIte, wyL, wyT, Nat.lt_irrefl]; grind
    · intro m hm
      have hne : m.val ≠ i.val := fun hv => hm (Fin.ext hv)
      by_cases hlt : m.val < i.val
      · have hnot : ¬ i.val < m.val := by omega
        have hmi : m ≠ i := hm
        simp only [wyT, hmi, hnot, ↓reduceIte]; grind
      · have hgt : i.val < m.val := by omega
        have him : i ≠ m := fun h => hm h.symm
        have hnot : ¬ m.val < i.val := by omega
        simp only [him, wyL, hnot, ↓reduceIte]; grind
  · simp only [hij, ↓reduceIte]
    by_cases hlt : i.val < j.val
    · rw [sumFin_congr (g := fun _ => 0)]
      · exact sumFin_zero C
      · intro m
        by_cases hmi : m.val ≤ i.val
        · have hmj : m ≠ j := fun h => by subst h; omega
          have hnot : ¬ j.val < m.val := by omega
          simp only [wyT, hmj, hnot, ↓reduceIte]; grind
        · have him : i ≠ m := fun h => by subst h; omega
          have hnot : ¬ m.val < i.val := by omega
          simp only [him, wyL, hnot, ↓reduceIte]; grind
    · have hjlt : j.val < i.val := by
        have hne : i.val ≠ j.val := fun hv => hij (Fin.ext hv)
        omega
      -- Split sum over m into m = i, m = j, and j < m < i
      let u : Nat → (Fin d → Rat) := fun n => hhChain betas keys (j.val + 1) (n - (j.val + 1)) (keys j)
      let g : Nat → Rat := fun n => dot (keys i) (u n)
      have hdecomp : sumFin (fun m : Fin C =>
            ((if i = m then (1 : Rat) else 0) + wyL C d α betas keys i m) * wyT C d α betas keys m j) =
          sumFin (fun m : Fin C =>
            (if m = i then wyT C d α betas keys i j else 0) +
            (if m = j then wyL C d α betas keys i j else 0) +
            (if j.val + 1 ≤ m.val ∧ m.val < i.val then
              betas i * ratPow α (i.val - j.val) * (g (m.val + 1) - g m.val) else 0)) := by
        apply sumFin_congr
        intro m
        by_cases hmi : m = i
        · subst hmi
          simp only [↓reduceIte, hij, wyL, Nat.lt_irrefl]; grind
        · by_cases hmj : m = j
          · subst hmj
            have him : i ≠ m := hij
            have hnot : ¬ (m.val + 1 ≤ m.val ∧ m.val < i.val) := by omega
            simp only [him, hmi, ↓reduceIte, wyT, hnot]; grind
          · by_cases hmid : j.val + 1 ≤ m.val ∧ m.val < i.val
            · have him : i ≠ m := fun h => hmi h.symm
              have hjm : j.val < m.val := by omega
              simp only [him, hmi, hmj, hmid, ↓reduceIte, wyL, wyT, hjm]
              -- Show `g (m + 1) - g m = -β_m * ⟨k_m, u m⟩ * ⟨k_i, k_m⟩`
              have hstep : u (m.val + 1) = hhStep (betas m) (keys m) (u m.val) := by
                have hsub : m.val + 1 - (j.val + 1) = (m.val - (j.val + 1)) + 1 := by omega
                have hadd : (j.val + 1) + (m.val - (j.val + 1)) = m.val := by omega
                show hhChain betas keys (j.val + 1) (m.val + 1 - (j.val + 1)) (keys j) =
                  hhStep (betas m) (keys m) (hhChain betas keys (j.val + 1) (m.val - (j.val + 1)) (keys j))
                rw [hsub, hhChain]
                have hltC : j.val + 1 + (m.val - (j.val + 1)) < C := by rw [hadd]; exact m.isLt
                simp only [hltC, ↓reduceDIte]
                have hfin : (⟨j.val + 1 + (m.val - (j.val + 1)), hltC⟩ : Fin C) = m := Fin.ext hadd
                rw [hfin]
              have hgdiff : g (m.val + 1) - g m.val =
                  -(betas m * dot (keys m) (u m.val) * dot (keys i) (keys m)) := by
                show dot (keys i) (u (m.val + 1)) - dot (keys i) (u m.val) = _
                rw [hstep]
                unfold hhStep
                rw [dot_sub_right, dot_scale_right]
                grind
              have hpow : ratPow α (i.val - m.val) * ratPow α (m.val - j.val) =
                  ratPow α (i.val - j.val) := by
                rw [← ratPow_add]
                congr 1
                omega
              have hsub2 : m.val - j.val - 1 = m.val - (j.val + 1) := by omega
              rw [hgdiff]
              have hu_eq : hhChain betas keys (j.val + 1) (m.val - j.val - 1) (keys j) = u m.val := by
                show hhChain betas keys (j.val + 1) (m.val - j.val - 1) (keys j) =
                  hhChain betas keys (j.val + 1) (m.val - (j.val + 1)) (keys j)
                rw [hsub2]
              rw [hu_eq]
              have hmul : (0 + betas i * ratPow α (i.val - m.val) * dot (keys i) (keys m)) *
                  -(betas m * ratPow α (m.val - j.val) * dot (keys m) (u m.val)) =
                  -(betas i * (ratPow α (i.val - m.val) * ratPow α (m.val - j.val)) *
                    (betas m * dot (keys m) (u m.val) * dot (keys i) (keys m))) := by grind
              rw [hmul, hpow]
              grind
            · -- Outside (j, i) and not equal to i or j
              have him : i ≠ m := fun h => hmi h.symm
              simp only [him, hmi, hmj, hmid, ↓reduceIte]
              by_cases hmlt : m.val < j.val
              · have hnot : ¬ j.val < m.val := by omega
                simp only [wyT, hmj, hnot, ↓reduceIte]; grind
              · have hnot : ¬ m.val < i.val := by omega
                simp only [wyL, hnot, ↓reduceIte]; grind
      rw [hdecomp, sumFin_add_fn, sumFin_add_fn]
      have hs1 : sumFin (fun m : Fin C => if m = i then wyT C d α betas keys i j else 0) =
          wyT C d α betas keys i j := by
        rw [sumFin_single i]
        · simp
        · intro m hm; simp [hm]
      have hs2 : sumFin (fun m : Fin C => if m = j then wyL C d α betas keys i j else 0) =
          wyL C d α betas keys i j := by
        rw [sumFin_single j]
        · simp
        · intro m hm; simp [hm]
      have hs3 : sumFin (fun m : Fin C => if j.val + 1 ≤ m.val ∧ m.val < i.val then
            betas i * ratPow α (i.val - j.val) * (g (m.val + 1) - g m.val) else 0) =
          betas i * ratPow α (i.val - j.val) * (g i.val - g (j.val + 1)) := by
        have hpull : sumFin (fun m : Fin C => if j.val + 1 ≤ m.val ∧ m.val < i.val then
              betas i * ratPow α (i.val - j.val) * (g (m.val + 1) - g m.val) else 0) =
            sumFin (fun m : Fin C => betas i * ratPow α (i.val - j.val) *
              (if j.val + 1 ≤ m.val ∧ m.val < i.val then g (m.val + 1) - g m.val else 0)) := by
          apply sumFin_congr
          intro m
          by_cases hc : j.val + 1 ≤ m.val ∧ m.val < i.val <;> simp [hc]
        rw [hpull, sumFin_mul_left, sumFin_telescope C (j.val + 1) i.val (by omega) (Nat.le_of_lt i.isLt) g]
      rw [hs1, hs2, hs3]
      have hT : wyT C d α betas keys i j = -(betas i * ratPow α (i.val - j.val) * g i.val) := by
        unfold wyT
        simp only [hij, hjlt, ↓reduceIte]
        have hsub : i.val - j.val - 1 = i.val - (j.val + 1) := by omega
        show -(betas i * ratPow α (i.val - j.val) *
            dot (keys i) (hhChain betas keys (j.val + 1) (i.val - j.val - 1) (keys j))) =
          -(betas i * ratPow α (i.val - j.val) *
            dot (keys i) (hhChain betas keys (j.val + 1) (i.val - (j.val + 1)) (keys j)))
        rw [hsub]
      have hL : wyL C d α betas keys i j = betas i * ratPow α (i.val - j.val) * g (j.val + 1) := by
        unfold wyL
        simp only [hjlt, ↓reduceIte]
        show betas i * ratPow α (i.val - j.val) * dot (keys i) (keys j) =
          betas i * ratPow α (i.val - j.val) *
            dot (keys i) (hhChain betas keys (j.val + 1) (j.val + 1 - (j.val + 1)) (keys j))
        rw [Nat.sub_self, hhChain]
      rw [hT, hL]
      grind

/-- Exact action of `n` aligned Householder factors on `k`:
    `(I - β k k^T)^n k = (1 - β ‖k‖²)^n k`. -/
theorem hhChain_aligned {C d : Nat} (β : Rat) (k : Fin d → Rat) (start n : Nat)
    (hbound : start + n ≤ C) :
    hhChain (C := C) (fun _ => β) (fun _ => k) start n k =
      fun a => ratPow (1 - β * normSq k) n * k a := by
  induction n with
  | zero =>
    funext a
    simp only [hhChain, ratPow]
    grind
  | succ m ih =>
    funext a
    simp only [hhChain]
    have hlt : start + m < C := by omega
    simp only [hlt, ↓reduceDIte]
    rw [ih (by omega)]
    unfold hhStep
    rw [dot_scale_right]
    have hnorm : dot k k = normSq k := rfl
    rw [hnorm, ratPow]
    grind

/-- Exact closed form of `wyT` for aligned keys `k_m = k` and constant `β, α`. -/
theorem wyT_aligned_entry (C d : Nat) (α β : Rat) (k : Fin d → Rat)
    (i j : Fin C) (hji : j.val < i.val) :
    wyT C d α (fun _ => β) (fun _ => k) i j =
      -(β * normSq k * ratPow α (i.val - j.val) * ratPow (1 - β * normSq k) (i.val - j.val - 1)) := by
  have hij : i ≠ j := fun h => by subst h; omega
  unfold wyT
  simp only [hij, hji, ↓reduceIte]
  have hbound : (j.val + 1) + (i.val - j.val - 1) ≤ C := by
    have := i.isLt; omega
  rw [hhChain_aligned β k (j.val + 1) (i.val - j.val - 1) hbound, dot_scale_right]
  have hnorm : dot k k = normSq k := rfl
  rw [hnorm]
  grind

/-- Headline Theorem 3: Universal closed-form chunkwise WY inverse identity,
    aligned-key contraction (zero explosion for `0 ≤ β r ≤ 2`), and quantized-key
    exponential blowup (`β = 2, α = 1, r > 1`). -/
theorem wy_inverse_closed_form_and_aligned_contraction :
    (∀ (C d : Nat) (α : Rat) (betas : Fin C → Rat) (keys : Fin C → Fin d → Rat),
      matMul (matAdd (idMat C) (wyL C d α betas keys)) (wyT C d α betas keys) = idMat C) ∧
    (∀ (C d : Nat) (α β : Rat) (k : Fin d → Rat) (i j : Fin C), j.val < i.val →
      wyT C d α (fun _ => β) (fun _ => k) i j =
        -(β * normSq k * ratPow α (i.val - j.val) * ratPow (1 - β * normSq k) (i.val - j.val - 1))) ∧
    (∀ (C d : Nat) (α β : Rat) (k : Fin d → Rat),
      0 < α → α ≤ 1 → 0 ≤ β → β * normSq k ≤ 2 →
      (∀ i j : Fin C, j.val < i.val →
        ratAbs (wyT C d α (fun _ => β) (fun _ => k) i j) ≤ β * normSq k) ∧
      (∀ i : Fin C,
        sumFin (fun j : Fin C => ratAbs (wyT C d α (fun _ => β) (fun _ => k) i j)) ≤
          1 + ((C - 1 : Nat) : Rat) * (β * normSq k) ∧
        sumFin (fun j : Fin C => ratAbs (wyT C d α (fun _ => β) (fun _ => k) i j)) ≤
          2 * (C : Rat) - 1)) ∧
    (∀ (C d : Nat) (hC : 2 ≤ C) (k : Fin d → Rat), 1 < normSq k →
      ratAbs (wyT C d 1 (fun _ => 2) (fun _ => k) ⟨C - 1, by omega⟩ ⟨0, by omega⟩) =
        2 * normSq k * ratPow (2 * normSq k - 1) (C - 2)) := by
  refine ⟨wy_inverse_exact, wyT_aligned_entry, ?_, ?_⟩
  · intro C d α β k hα0 hα1 hβ0 hbr2
    have hr0 : 0 ≤ normSq k := normSq_nonneg k
    have hbr0 : 0 ≤ β * normSq k := rat_mul_nonneg hβ0 hr0
    have hentry : ∀ i j : Fin C, j.val < i.val →
        ratAbs (wyT C d α (fun _ => β) (fun _ => k) i j) ≤ β * normSq k := by
      intro i j hji
      rw [wyT_aligned_entry C d α β k i j hji, ratAbs_neg, ratAbs_mul, ratAbs_mul,
          ratAbs_of_nonneg hbr0, ratAbs_ratPow, ratAbs_ratPow, ratAbs_of_nonneg (by grind : 0 ≤ α)]
      have hαp : ratPow α (i.val - j.val) ≤ 1 := ratPow_le_one (by grind) hα1 _
      have hαp0 : 0 ≤ ratPow α (i.val - j.val) := ratPow_nonneg (by grind) _
      have h1br : ratAbs (1 - β * normSq k) ≤ 1 := by
        rw [ratAbs_le_iff]; grind
      have h1brp : ratPow (ratAbs (1 - β * normSq k)) (i.val - j.val - 1) ≤ 1 :=
        ratPow_le_one (ratAbs_nonneg _) h1br _
      have hprod : ratPow α (i.val - j.val) * ratPow (ratAbs (1 - β * normSq k)) (i.val - j.val - 1) ≤ 1 := by
        have h := rat_mul_le_mul_nonneg hαp0 (ratPow_nonneg (ratAbs_nonneg _) _) hαp h1brp
        grind
      have hmul := Rat.mul_le_mul_of_nonneg_left hprod hbr0
      grind
    refine ⟨hentry, ?_⟩
    intro i
    have hC1 : 1 ≤ C := by have := i.isLt; omega
    have hCcast : ((C - 1 : Nat) : Rat) = (C : Rat) - 1 := by
      have hadd : (C - 1) + 1 = C := Nat.sub_add_cancel hC1
      have hcast : (((C - 1) + 1 : Nat) : Rat) = (C : Rat) := by rw [hadd]
      rw [Rat.natCast_add] at hcast
      grind
    have hsplit := sumFin_split_at i (fun j : Fin C => ratAbs (wyT C d α (fun _ => β) (fun _ => k) i j))
    have hdiag : ratAbs (wyT C d α (fun _ => β) (fun _ => k) i i) = 1 := by
      simp only [wyT, ↓reduceIte, ratAbs]; grind
    have hrest : sumFin (fun j : Fin C => if j = i then (0 : Rat) else
          ratAbs (wyT C d α (fun _ => β) (fun _ => k) i j)) ≤
        sumFin (fun j : Fin C => if j = i then (0 : Rat) else β * normSq k) := by
      apply sumFin_le_sumFin
      intro j
      by_cases hji : j = i
      · simp [hji]
      · simp only [hji, ↓reduceIte]
        by_cases hlt : j.val < i.val
        · exact hentry i j hlt
        · have hij : i ≠ j := fun h => hji h.symm
          simp only [wyT, hij, hlt, ↓reduceIte, ratAbs]
          grind
    have hconst : sumFin (fun j : Fin C => if j = i then (0 : Rat) else β * normSq k) =
        ((C : Rat) - 1) * (β * normSq k) := by
      have h := sumFin_split_at i (fun _ : Fin C => β * normSq k)
      rw [sumFin_const] at h
      grind
    have hbound1 : sumFin (fun j : Fin C => ratAbs (wyT C d α (fun _ => β) (fun _ => k) i j)) ≤
        1 + ((C - 1 : Nat) : Rat) * (β * normSq k) := by
      rw [hsplit, hdiag, hCcast]
      grind
    have hC1nonneg : (0 : Rat) ≤ ((C - 1 : Nat) : Rat) := by exact_mod_cast Nat.zero_le (C - 1)
    have hbound2 : 1 + ((C - 1 : Nat) : Rat) * (β * normSq k) ≤ 2 * (C : Rat) - 1 := by
      have h := Rat.mul_le_mul_of_nonneg_left hbr2 hC1nonneg
      rw [hCcast] at h ⊢
      grind
    exact ⟨hbound1, Rat.le_trans hbound1 hbound2⟩
  · intro C d hC k hk
    have hlt : (0 : Nat) < C - 1 := by omega
    rw [wyT_aligned_entry C d 1 2 k ⟨C - 1, by omega⟩ ⟨0, by omega⟩ hlt]
    simp only [Nat.sub_zero, ratPow_one_base]
    have hsub : C - 1 - 1 = C - 2 := by omega
    rw [hsub]
    have hneg : -(2 * normSq k * 1 * ratPow (1 - 2 * normSq k) (C - 2)) =
        -(2 * normSq k * ratPow (1 - 2 * normSq k) (C - 2)) := by grind
    rw [hneg, ratAbs_neg, ratAbs_mul, ratAbs_of_nonneg (by grind : 0 ≤ 2 * normSq k),
        ratAbs_ratPow, ratAbs_of_nonpos (by grind : 1 - 2 * normSq k ≤ 0)]
    have hflip : -(1 - 2 * normSq k) = 2 * normSq k - 1 := by grind
    rw [hflip]

end DeltanetWyStability
