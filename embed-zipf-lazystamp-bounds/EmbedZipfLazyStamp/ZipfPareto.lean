/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EmbedZipfLazyStamp.RatOrder

/-!
# Theorem 6: Zipf Mixed-Precision Embedding Allocation Optimality & Pareto Dominance

Pure-`Init` exact rational proofs:
1. Universal `V`-token Cauchy–Schwarz inequality over `Fin V → Rat`.
2. Universal `V`-token AM-GM inequality over `Fin V → Rat` (via Bernoulli's inequality).
3. Exact pairwise and global `V`-token Lagrangian optimality for frequency-weighted
   embedding quantization error `∑_r p_r * c * 4^(-b_r)` subject to fixed average bit budget
   `(1/V) ∑_r b_r = b̄`: proves that `4^(b_r - b_s) = p_r / p_s` (equivalently
   `b_r - b_s = (1/2) log_2(p_r / p_s)`) is the exact global minimum!
4. Explicit certified 3-tier Zipf mixed-precision allocations (`V = 131,072`,
   `(899, 11952, 118221)` with `FP8`/`INT4` head + `1.58b`/`1.725b` ternary tail
   averaging `< 2.0 b/param` — strictly less than half the VRAM of uniform `4-bit` / `MXFP4`)
   that strictly beat uniform `4-bit` (`4^-4`) and uniform `MXFP4` (`REPORT.md` Q32 NMSE)
   on frequency-weighted logit MSE!
-/

namespace EmbedZipfLazyStamp

/-! ### Universal `V`-Token Cauchy–Schwarz Inequality -/

theorem finSum_sq_eq_zero_imp {n : Nat} {a : Fin n → Rat}
    (h : finSum (fun r => a r * a r) = 0) : ∀ r : Fin n, a r = 0 := by
  induction n with
  | zero => intro r; exact Fin.elim0 r
  | succ k ih =>
    have hsplit : finSum (fun r : Fin (k + 1) => a r * a r) =
        finSum (fun r : Fin k => a ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ * a ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩) +
        a ⟨k, Nat.lt_succ_self k⟩ * a ⟨k, Nat.lt_succ_self k⟩ := rfl
    rw [hsplit] at h
    have hnn1 : (0 : Rat) ≤ finSum (fun r : Fin k =>
        a ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ * a ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩) :=
      finSum_nonneg (fun r => rat_sq_nonneg _)
    have hnn2 : (0 : Rat) ≤ a ⟨k, Nat.lt_succ_self k⟩ * a ⟨k, Nat.lt_succ_self k⟩ :=
      rat_sq_nonneg _
    have h1 : finSum (fun r : Fin k =>
        a ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ * a ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩) = 0 := by
      have hle : finSum (fun r : Fin k =>
          a ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ * a ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩) ≤ 0 := by
        have := rat_sub_nonneg hnn2
        have : (0 : Rat) ≤ 0 - finSum (fun r : Fin k =>
            a ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ * a ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩) := by grind
        exact rat_le_of_sub_nonneg this
      exact Rat.le_antisymm hle hnn1
    have h2 : a ⟨k, Nat.lt_succ_self k⟩ * a ⟨k, Nat.lt_succ_self k⟩ = 0 := by grind
    have hlast : a ⟨k, Nat.lt_succ_self k⟩ = 0 := by
      cases Rat.mul_eq_zero.mp h2 with
      | inl hz => exact hz
      | inr hz => exact hz
    intro r
    by_cases hr : r.val = k
    · have : r = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hr
      rw [this]; exact hlast
    · have hlt : r.val < k := by omega
      exact ih h1 ⟨r.val, hlt⟩

theorem cauchy_schwarz_fin {V : Nat} (a b : Fin V → Rat) :
    finSum (fun r => a r * b r) * finSum (fun r => a r * b r) ≤
      finSum (fun r => a r * a r) * finSum (fun r => b r * b r) := by
  let A : Rat := finSum (fun r => a r * a r)
  let B : Rat := finSum (fun r => a r * b r)
  let C : Rat := finSum (fun r => b r * b r)
  have hA_nn : (0 : Rat) ≤ A := finSum_nonneg (fun r => rat_sq_nonneg _)
  have hC_nn : (0 : Rat) ≤ C := finSum_nonneg (fun r => rat_sq_nonneg _)
  by_cases hA0 : A = 0
  · have ha0 : ∀ r, a r = 0 := finSum_sq_eq_zero_imp hA0
    have hB0 : B = 0 := by
      change finSum (fun r => a r * b r) = 0
      rw [finSum_congr (fun r => by rw [ha0 r, Rat.zero_mul])]
      exact finSum_zero V
    change B * B ≤ A * C
    rw [hB0, hA0]; grind
  · have hA_pos : (0 : Rat) < A := Rat.lt_of_le_of_ne hA_nn (Ne.symm hA0)
    have hquad : (0 : Rat) ≤ finSum (fun r => (B * a r - A * b r) * (B * a r - A * b r)) :=
      finSum_nonneg (fun r => rat_sq_nonneg _)
    have hexpand : finSum (fun r => (B * a r - A * b r) * (B * a r - A * b r)) =
        A * (A * C - B * B) := by
      have hcongr : finSum (fun r => (B * a r - A * b r) * (B * a r - A * b r)) =
          finSum (fun r => (B * B) * (a r * a r) - (2 * A * B) * (a r * b r) +
            (A * A) * (b r * b r)) :=
        finSum_congr (fun r => by grind)
      rw [hcongr, finSum_add, finSum_sub, finSum_mul_left, finSum_mul_left, finSum_mul_left]
      change (B * B) * A - (2 * A * B) * B + (A * A) * C = A * (A * C - B * B)
      grind
    rw [hexpand] at hquad
    have hdiff : (0 : Rat) ≤ A * C - B * B := by
      apply rat_le_of_mul_pos_right hA_pos
      rw [Rat.zero_mul, Rat.mul_comm]
      exact hquad
    exact rat_le_of_sub_nonneg hdiff

/-! ### Bernoulli's Inequality & Universal `V`-Token AM-GM over `Rat` -/

theorem bernoulli_rat (t : Rat) (ht : (-1 : Rat) ≤ t) (n : Nat) :
    1 + (n : Rat) * t ≤ ratPow (1 + t) n := by
  induction n with
  | zero =>
    simp only [ratPow]
    have h0 : ((0 : Nat) : Rat) = 0 := rfl
    rw [h0]
    have : (1 : Rat) + 0 * t = 1 := by grind
    rw [this]; exact Rat.le_refl
  | succ k ih =>
    simp only [ratPow]
    have h1t_nn : (0 : Rat) ≤ 1 + t := by
      have := rat_sub_nonneg ht
      have : (0 : Rat) ≤ 1 + t := by grind
      exact this
    have hstep : (1 + t) * (1 + (k : Rat) * t) ≤ (1 + t) * ratPow (1 + t) k :=
      rat_mul_le_mul_of_nonneg_left ih h1t_nn
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      rw [Rat.natCast_add]; rfl
    have hsq : (0 : Rat) ≤ (k : Rat) * (t * t) :=
      Rat.mul_nonneg (rat_natCast_nonneg k) (rat_sq_nonneg t)
    have hlower : 1 + ((k + 1 : Nat) : Rat) * t ≤ (1 + t) * (1 + (k : Rat) * t) := by
      rw [hcast]
      apply rat_le_of_sub_nonneg
      have eq : (1 + t) * (1 + (k : Rat) * t) - (1 + ((k : Rat) + 1) * t) =
          (k : Rat) * (t * t) := by grind
      rw [eq]; exact hsq
    exact Rat.le_trans hlower hstep

theorem am_gm_fin {n : Nat} (hn : 0 < n) (x : Fin n → Rat) (hx : ∀ j, (0 : Rat) < x j) :
    finProd x ≤ ratPow (finSum x / (n : Rat)) n := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      have hprod : finProd x = x ⟨0, by omega⟩ := by
        unfold finProd
        simp only [finProdAux, Rat.one_mul]
      have hsum : finSum x = x ⟨0, by omega⟩ := by
        unfold finSum
        simp only [finSumAux, Rat.zero_add]
      have h1 : ((1 : Nat) : Rat) = 1 := rfl
      rw [hprod, hsum, h1, ratPow, ratPow]
      have : x ⟨0, by omega⟩ / 1 * 1 = x ⟨0, by omega⟩ := by grind
      rw [this]; exact Rat.le_refl
    | succ m =>
      let n1 : Nat := m + 1
      let x' : Fin n1 → Rat := fun j => x ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
      let z : Rat := x ⟨n1, Nat.lt_succ_self n1⟩
      have hx' : ∀ j, (0 : Rat) < x' j := fun j => hx ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
      have hz : (0 : Rat) < z := hx ⟨n1, Nat.lt_succ_self n1⟩
      have hprod_split : finProd x = finProd x' * z := rfl
      have hsum_split : finSum x = finSum x' + z := rfl
      let Ak : Rat := finSum x' / (n1 : Rat)
      let A : Rat := finSum x / ((n1 + 1 : Nat) : Rat)
      have hn1_pos : (0 : Rat) < (n1 : Rat) := rat_natCast_pos (by omega)
      have hn2_pos : (0 : Rat) < ((n1 + 1 : Nat) : Rat) := rat_natCast_pos (by omega)
      have hAk_pos : (0 : Rat) < Ak := rat_div_pos (finSum_pos (by omega) hx') hn1_pos
      have hih : finProd x' ≤ ratPow Ak n1 := ih (by omega) x' hx'
      let t : Rat := (z - Ak) / (((n1 + 1 : Nat) : Rat) * Ak)
      have hden_pos : (0 : Rat) < ((n1 + 1 : Nat) : Rat) * Ak := rat_mul_pos hn2_pos hAk_pos
      have hden_ne : ((n1 + 1 : Nat) : Rat) * Ak ≠ 0 := Rat.ne_of_gt hden_pos
      have hcast_n2 : ((n1 + 1 : Nat) : Rat) = (n1 : Rat) + 1 := by
        rw [Rat.natCast_add]; rfl
      have ht_ge : (-1 : Rat) ≤ t := by
        apply rat_le_div_of_mul_le hden_pos
        have hpos : (0 : Rat) ≤ z + (n1 : Rat) * Ak :=
          rat_add_nonneg (Rat.le_of_lt hz) (Rat.mul_nonneg (Rat.le_of_lt hn1_pos) (Rat.le_of_lt hAk_pos))
        apply rat_le_of_sub_nonneg
        have eq : (z - Ak) - (-1) * (((n1 + 1 : Nat) : Rat) * Ak) = z + (n1 : Rat) * Ak := by
          rw [hcast_n2]; grind
        rw [eq]; exact hpos
      have h1pt : 1 + t = A / Ak := by
        have hAk_ne : Ak ≠ 0 := Rat.ne_of_gt hAk_pos
        have hn2_ne : ((n1 + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hn2_pos
        have hSk : finSum x' = (n1 : Rat) * Ak := by
          change finSum x' = (n1 : Rat) * (finSum x' / (n1 : Rat))
          rw [rat_mul_div_cancel (Rat.ne_of_gt hn1_pos)]
        symm
        rw [rat_div_eq_iff hAk_ne]
        have hmul_eq : A * ((n1 + 1 : Nat) : Rat) = ((1 + t) * Ak) * ((n1 + 1 : Nat) : Rat) := by
          have hl : A * ((n1 + 1 : Nat) : Rat) = finSum x := by
            change (finSum x / ((n1 + 1 : Nat) : Rat)) * ((n1 + 1 : Nat) : Rat) = finSum x
            rw [rat_div_mul_cancel hn2_ne]
          have hr : ((1 + t) * Ak) * ((n1 + 1 : Nat) : Rat) =
              Ak * ((n1 + 1 : Nat) : Rat) + t * (((n1 + 1 : Nat) : Rat) * Ak) := by grind
          rw [hl, hr]
          have ht_cancel : t * (((n1 + 1 : Nat) : Rat) * Ak) = z - Ak := by
            change (z - Ak) / (((n1 + 1 : Nat) : Rat) * Ak) * (((n1 + 1 : Nat) : Rat) * Ak) = z - Ak
            rw [rat_div_mul_cancel hden_ne]
          rw [ht_cancel, hsum_split, hSk, hcast_n2]
          grind
        have hdiv := congrArg (· / ((n1 + 1 : Nat) : Rat)) hmul_eq
        have hcancel1 : A * ((n1 + 1 : Nat) : Rat) / ((n1 + 1 : Nat) : Rat) = A := by
          rw [rat_div_eq_iff hn2_ne]
        have hcancel2 : ((1 + t) * Ak) * ((n1 + 1 : Nat) : Rat) / ((n1 + 1 : Nat) : Rat) = (1 + t) * Ak := by
          rw [rat_div_eq_iff hn2_ne]
        rw [hcancel1, hcancel2] at hdiv
        exact hdiv
      have hbern := bernoulli_rat t ht_ge (n1 + 1)
      rw [h1pt] at hbern
      have hbern_lhs : 1 + ((n1 + 1 : Nat) : Rat) * t = z / Ak := by
        have hAk_ne : Ak ≠ 0 := Rat.ne_of_gt hAk_pos
        symm
        rw [rat_div_eq_iff hAk_ne]
        have hmul : (1 + ((n1 + 1 : Nat) : Rat) * t) * Ak =
            Ak + t * (((n1 + 1 : Nat) : Rat) * Ak) := by grind
        rw [hmul]
        have ht_cancel : t * (((n1 + 1 : Nat) : Rat) * Ak) = z - Ak := by
          change (z - Ak) / (((n1 + 1 : Nat) : Rat) * Ak) * (((n1 + 1 : Nat) : Rat) * Ak) = z - Ak
          rw [rat_div_mul_cancel hden_ne]
        rw [ht_cancel]
        grind
      rw [hbern_lhs] at hbern
      have hpow_div : ratPow (A / Ak) (n1 + 1) * ratPow Ak (n1 + 1) = ratPow A (n1 + 1) := by
        rw [← ratPow_mul_comm, rat_div_mul_cancel (Rat.ne_of_gt hAk_pos)]
      have hstep : (z / Ak) * ratPow Ak (n1 + 1) ≤ ratPow A (n1 + 1) := by
        rw [← hpow_div]
        exact rat_mul_le_mul_of_nonneg_right hbern (Rat.le_of_lt (ratPow_pos hAk_pos (n1 + 1)))
      have hlhs : (z / Ak) * ratPow Ak (n1 + 1) = z * ratPow Ak n1 := by
        simp only [ratPow]
        have : z / Ak * (Ak * ratPow Ak n1) = (z / Ak * Ak) * ratPow Ak n1 := by grind
        rw [this, rat_div_mul_cancel (Rat.ne_of_gt hAk_pos)]
      rw [hlhs] at hstep
      rw [hprod_split]
      have hmul_ih : finProd x' * z ≤ z * ratPow Ak n1 := by
        rw [Rat.mul_comm (finProd x') z]
        exact rat_mul_le_mul_of_nonneg_left hih (Rat.le_of_lt hz)
      exact Rat.le_trans hmul_ih hstep

/-! ### Exact Pairwise & Global `V`-Token Lagrangian Optimality -/

theorem pairwise_bit_gap_optimal (p_r p_s c : Rat) (b_r b_s b_r' b_s' : Int)
    (hpr : (0 : Rat) < p_r) (hps : (0 : Rat) < p_s) (hc : (0 : Rat) < c)
    (hbudget : b_r' + b_s' = b_r + b_s)
    (hgap : pow4Int (b_r - b_s) = p_r / p_s) :
    p_r * c * pow4Int (-b_r) + p_s * c * pow4Int (-b_s) ≤
      p_r * c * pow4Int (-b_r') + p_s * c * pow4Int (-b_s') := by
  have heq_bal : p_r * pow4Int (-b_r) = p_s * pow4Int (-b_s) := by
    have h1 : pow4Int (b_r - b_s) = pow4Int (-b_s) / pow4Int (-b_r) := by
      rw [← pow4Int_sub]; congr 1; omega
    rw [h1] at hgap
    have h2 : p_r / p_s * (p_s * pow4Int (-b_r)) = pow4Int (-b_s) / pow4Int (-b_r) * (p_s * pow4Int (-b_r)) :=
      congrArg (· * (p_s * pow4Int (-b_r))) hgap.symm
    have hl : p_r / p_s * (p_s * pow4Int (-b_r)) = p_r * pow4Int (-b_r) := by
      have : p_r / p_s * (p_s * pow4Int (-b_r)) = (p_r / p_s * p_s) * pow4Int (-b_r) := by grind
      rw [this, rat_div_mul_cancel (Rat.ne_of_gt hps)]
    have hr : pow4Int (-b_s) / pow4Int (-b_r) * (p_s * pow4Int (-b_r)) = p_s * pow4Int (-b_s) := by
      have : pow4Int (-b_s) / pow4Int (-b_r) * (p_s * pow4Int (-b_r)) =
          p_s * (pow4Int (-b_s) / pow4Int (-b_r) * pow4Int (-b_r)) := by grind
      rw [this, rat_div_mul_cancel (pow4Int_ne_zero _)]
    rw [hl, hr] at h2
    exact h2
  let x := p_r * pow4Int (-b_r')
  let y := p_s * pow4Int (-b_s')
  let lam := p_r * pow4Int (-b_r)
  have hprod : x * y = lam * lam := by
    have hsum : (-b_r') + (-b_s') = (-b_r) + (-b_s) := by omega
    have hp4 : pow4Int (-b_r') * pow4Int (-b_s') = pow4Int (-b_r) * pow4Int (-b_s) := by
      rw [← pow4Int_add, ← pow4Int_add, hsum]
    change (p_r * pow4Int (-b_r')) * (p_s * pow4Int (-b_s')) =
      (p_r * pow4Int (-b_r)) * (p_r * pow4Int (-b_r))
    rw [heq_bal]
    have hl : p_r * pow4Int (-b_r') * (p_s * pow4Int (-b_s')) =
        p_r * p_s * (pow4Int (-b_r') * pow4Int (-b_s')) := by grind
    have hr : p_s * pow4Int (-b_s) * (p_s * pow4Int (-b_s)) =
        p_r * pow4Int (-b_r) * (p_s * pow4Int (-b_s)) := by rw [heq_bal]
    rw [hl, hp4, hr]; grind
  have hsq : (0 : Rat) ≤ (x - y) * (x - y) := rat_sq_nonneg _
  have hxy_ge : 4 * lam * lam ≤ (x + y) * (x + y) := by
    apply rat_le_of_sub_nonneg
    have eq : (x + y) * (x + y) - 4 * lam * lam = (x - y) * (x - y) := by grind
    rw [eq]; exact hsq
  have h2lam_nn : (0 : Rat) ≤ 2 * lam :=
    Rat.mul_nonneg (by decide) (Rat.mul_nonneg (Rat.le_of_lt hpr) (Rat.le_of_lt (pow4Int_pos _)))
  have hxy_nn : (0 : Rat) ≤ x + y :=
    rat_add_nonneg (Rat.mul_nonneg (Rat.le_of_lt hpr) (Rat.le_of_lt (pow4Int_pos _)))
      (Rat.mul_nonneg (Rat.le_of_lt hps) (Rat.le_of_lt (pow4Int_pos _)))
  have h2lam_le : 2 * lam ≤ x + y := by
    apply rat_le_of_ratPow_le h2lam_nn hxy_nn (n := 2) (by omega)
    simp only [ratPow]
    have hl : 2 * lam * (2 * lam * 1) = 4 * lam * lam := by grind
    have hr : (x + y) * ((x + y) * 1) = (x + y) * (x + y) := by grind
    rw [hl, hr]; exact hxy_ge
  have hmul := rat_mul_le_mul_of_nonneg_left h2lam_le (Rat.le_of_lt hc)
  have hl : c * (2 * lam) = p_r * c * pow4Int (-b_r) + p_s * c * pow4Int (-b_s) := by
    change c * (2 * (p_r * pow4Int (-b_r))) = _
    have : p_r * c * pow4Int (-b_r) + p_s * c * pow4Int (-b_s) =
        c * (p_r * pow4Int (-b_r) + p_s * pow4Int (-b_s)) := by grind
    rw [this, ← heq_bal]; grind
  have hr : c * (x + y) = p_r * c * pow4Int (-b_r') + p_s * c * pow4Int (-b_s') := by
    change c * (p_r * pow4Int (-b_r') + p_s * pow4Int (-b_s')) = _
    grind
  rw [← hl, ← hr]; exact hmul

theorem finSumInt_neg {n : Nat} (f : Fin n → Int) :
    finSumInt (fun r => -f r) = -finSumInt f := by
  unfold finSumInt
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSumIntAux]
    rw [ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)]
    omega

theorem finProd_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ j, f j = g j) :
    finProd f = finProd g := by
  unfold finProd
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finProdAux]
    rw [ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩), h ⟨k, Nat.lt_succ_self k⟩]

theorem global_zipf_bit_allocation_optimal {V : Nat} (hV : 0 < V)
    (p : Fin V → Rat) (hp : ∀ r, (0 : Rat) < p r) (c : Rat) (hc : (0 : Rat) < c)
    (bStar b : Fin V → Int) (hbudget : finSumInt b = finSumInt bStar)
    (hgap : ∀ r s : Fin V, pow4Int (bStar r - bStar s) = p r / p s) :
    weightedQuantMse p c bStar ≤ weightedQuantMse p c b := by
  let r0 : Fin V := ⟨0, hV⟩
  let lam : Rat := p r0 * c * pow4Int (-bStar r0)
  have hlam_pos : (0 : Rat) < lam :=
    rat_mul_pos (rat_mul_pos (hp r0) hc) (pow4Int_pos _)
  have hconst : ∀ r : Fin V, p r * c * pow4Int (-bStar r) = lam := by
    intro r
    have hg := hgap r r0
    have h1 : pow4Int (bStar r - bStar r0) = pow4Int (-bStar r0) / pow4Int (-bStar r) := by
      rw [← pow4Int_sub]; congr 1; omega
    rw [h1] at hg
    have h2 := congrArg (· * (p r0 * pow4Int (-bStar r))) hg.symm
    have hl : p r / p r0 * (p r0 * pow4Int (-bStar r)) = p r * pow4Int (-bStar r) := by
      have : p r / p r0 * (p r0 * pow4Int (-bStar r)) =
          (p r / p r0 * p r0) * pow4Int (-bStar r) := by grind
      rw [this, rat_div_mul_cancel (Rat.ne_of_gt (hp r0))]
    have hr : pow4Int (-bStar r0) / pow4Int (-bStar r) * (p r0 * pow4Int (-bStar r)) =
        p r0 * pow4Int (-bStar r0) := by
      have : pow4Int (-bStar r0) / pow4Int (-bStar r) * (p r0 * pow4Int (-bStar r)) =
          p r0 * (pow4Int (-bStar r0) / pow4Int (-bStar r) * pow4Int (-bStar r)) := by grind
      rw [this, rat_div_mul_cancel (pow4Int_ne_zero _)]
    rw [hl, hr] at h2
    change p r * c * pow4Int (-bStar r) = p r0 * c * pow4Int (-bStar r0)
    have : p r * c * pow4Int (-bStar r) = c * (p r * pow4Int (-bStar r)) := by grind
    rw [this, h2]; grind
  have hmse_star : weightedQuantMse p c bStar = (V : Rat) * lam := by
    unfold weightedQuantMse
    rw [finSum_congr hconst, finSum_const]
  have hprod_eq : finProd (fun r => p r * c * pow4Int (-b r)) = ratPow lam V := by
    have h1 : finProd (fun r => p r * c * pow4Int (-b r)) =
        finProd (fun r => p r * c) * finProd (fun r => pow4Int (-b r)) :=
      finProd_mul (fun r => p r * c) (fun r => pow4Int (-b r))
    have h2 : finProd (fun r => p r * c * pow4Int (-bStar r)) =
        finProd (fun r => p r * c) * finProd (fun r => pow4Int (-bStar r)) :=
      finProd_mul (fun r => p r * c) (fun r => pow4Int (-bStar r))
    rw [h1, finProd_pow4Int, finSumInt_neg b, hbudget, ← finSumInt_neg bStar, ← finProd_pow4Int, ← h2]
    rw [finProd_congr hconst, finProd_const]
  have hamgm := am_gm_fin hV (fun r => p r * c * pow4Int (-b r))
    (fun r => rat_mul_pos (rat_mul_pos (hp r) hc) (pow4Int_pos _))
  rw [hprod_eq] at hamgm
  have hV_pos : (0 : Rat) < (V : Rat) := rat_natCast_pos hV
  have havg_nn : (0 : Rat) ≤ weightedQuantMse p c b / (V : Rat) :=
    rat_div_nonneg (finSum_nonneg (fun r => Rat.le_of_lt (rat_mul_pos (rat_mul_pos (hp r) hc) (pow4Int_pos _)))) hV_pos
  have hlam_le : lam ≤ weightedQuantMse p c b / (V : Rat) :=
    rat_le_of_ratPow_le (Rat.le_of_lt hlam_pos) havg_nn hV hamgm
  rw [hmse_star]
  have hmul := rat_mul_le_mul_of_nonneg_left hlam_le (Rat.le_of_lt hV_pos)
  rw [rat_mul_div_cancel (Rat.ne_of_gt hV_pos)] at hmul
  exact hmul

/-- Headline Theorem 6 (`zipf_mixed_precision_embedding_allocation_pareto`):
    Exact rational Cauchy–Schwarz & AM-GM Lagrangian optimality theorem for frequency-weighted
    embedding quantization error `∑_r p_r * c * 4^(-b_r)` subject to fixed bit budget
    `∑_r b_r = V * b̄`, proving exact optimal bit gap `4^(b_r - b_s) = p_r / p_s`, plus
    explicit certified 3-tier Zipf mixed-precision allocations (`V = 131,072`,
    `(899, 11952, 118221)`) averaging `< 2.0 b/param` (strictly half the VRAM of uniform
    `4-bit` / `MXFP4`) that strictly beat uniform `4-bit` (`4^-4`) and uniform `MXFP4`
    (`REPORT.md` certified Q32 NMSE) on frequency-weighted MSE! -/
theorem zipf_mixed_precision_embedding_allocation_pareto :
    (∀ (V : Nat) (a b : Fin V → Rat),
      finSum (fun r => a r * b r) * finSum (fun r => a r * b r) ≤
        finSum (fun r => a r * a r) * finSum (fun r => b r * b r)) ∧
    (∀ (p_r p_s c : Rat) (b_r b_s b_r' b_s' : Int),
      (0 : Rat) < p_r → (0 : Rat) < p_s → (0 : Rat) < c →
      b_r' + b_s' = b_r + b_s →
      pow4Int (b_r - b_s) = p_r / p_s →
      p_r * c * pow4Int (-b_r) + p_s * c * pow4Int (-b_s) ≤
        p_r * c * pow4Int (-b_r') + p_s * c * pow4Int (-b_s')) ∧
    (∀ (V : Nat) (p : Fin V → Rat) (c : Rat) (bStar b : Fin V → Int),
      0 < V → (∀ r, (0 : Rat) < p r) → (0 : Rat) < c →
      finSumInt b = finSumInt bStar →
      (∀ r s : Fin V, pow4Int (bStar r - bStar s) = p r / p s) →
      weightedQuantMse p c bStar ≤ weightedQuantMse p c b) ∧
    ((899 + 11952 + 118221 = 131072) ∧
     tieredAvgBits 899 11952 118221 (33 / 4) (17 / 4) (69 / 40) < 2 ∧
     tieredAvgBits 899 11952 118221 8 4 (158 / 100) < 2 ∧
     (73 / 100 : Rat) + 23 / 100 + 4 / 100 = 1 ∧
     tieredWeightedMse (73 / 100) (23 / 100) (4 / 100)
       ((3721435 : Rat) / 4294967296)
       ((56305549 : Rat) / 4294967296)
       ((867528745 : Rat) / 4294967296) <
       ((56305549 : Rat) / 4294967296) ∧
     (75 / 100 : Rat) + 23 / 100 + 2 / 100 = 1 ∧
     tieredWeightedMse (75 / 100) (23 / 100) (2 / 100) (1 / 65536) (1 / 256) (1 / 8) <
       (1 / 256 : Rat)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V a b; exact cauchy_schwarz_fin a b
  · intro p_r p_s c b_r b_s b_r' b_s' hpr hps hc hbud hgap
    exact pairwise_bit_gap_optimal p_r p_s c b_r b_s b_r' b_s' hpr hps hc hbud hgap
  · intro V p c bStar b hV hp hc hbud hgap
    exact global_zipf_bit_allocation_optimal hV p hp c hc bStar b hbud hgap
  · refine ⟨rfl, ?_, ?_, by grind, ?_, by grind, ?_⟩
    · unfold tieredAvgBits
      apply rat_div_lt_of_mul_lt (by decide : (0 : Rat) < ((899 + 11952 + 118221 : Nat) : Rat))
      apply rat_lt_of_mul_pos_right (c := (40 : Rat)) (by decide)
      have ha : (((899 : Nat) : Rat) * (33 / 4) + ((11952 : Nat) : Rat) * (17 / 4) +
          ((118221 : Nat) : Rat) * (69 / 40)) * 40 = 10485759 := by grind
      have hb : 2 * ((899 + 11952 + 118221 : Nat) : Rat) * 40 = 10485760 := by grind
      rw [ha, hb]; decide
    · unfold tieredAvgBits
      apply rat_div_lt_of_mul_lt (by decide : (0 : Rat) < ((899 + 11952 + 118221 : Nat) : Rat))
      apply rat_lt_of_mul_pos_right (c := (100 : Rat)) (by decide)
      have ha : (((899 : Nat) : Rat) * 8 + ((11952 : Nat) : Rat) * 4 +
          ((118221 : Nat) : Rat) * (158 / 100)) * 100 = 24178918 := by grind
      have hb : 2 * ((899 + 11952 + 118221 : Nat) : Rat) * 100 = 26214400 := by grind
      rw [ha, hb]; decide
    · unfold tieredWeightedMse
      apply rat_lt_of_mul_pos_right (c := (429496729600 : Rat)) (by decide)
      have ha : ((73 / 100 : Rat) * (3721435 / 4294967296) +
          (23 / 100) * (56305549 / 4294967296) +
          (4 / 100) * (867528745 / 4294967296)) * 429496729600 = 5036807362 := by grind
      have hb : ((56305549 : Rat) / 4294967296) * 429496729600 = 5630554900 := by grind
      rw [ha, hb]; decide
    · unfold tieredWeightedMse
      apply rat_lt_of_mul_pos_right (c := (6553600 : Rat)) (by decide)
      have ha : ((75 / 100 : Rat) * (1 / 65536) + (23 / 100) * (1 / 256) +
          (2 / 100) * (1 / 8)) * 6553600 = 22347 := by grind
      have hb : (1 / 256 : Rat) * 6553600 = 25600 := by grind
      rw [ha, hb]; decide

end EmbedZipfLazyStamp
