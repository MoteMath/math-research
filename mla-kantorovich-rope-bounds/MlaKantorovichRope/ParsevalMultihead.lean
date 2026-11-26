/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MlaKantorovichRope.KantorovichGL

/-!
# Theorem 4: Parseval Tight-Frame Multi-Head Interference Cap & Walsh-Hadamard Witnesses

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. Universal Parseval tight-frame identity: `W^T W = c I_{d_c}` implies
   `multiheadDistSq W e = c * normSq e` for every error vector `e`.
2. Universal Bessel inequality for row-orthogonal heads (`W W^T = s I_H`, `s > 0`):
   `multiheadDistSq W e ≤ s * normSq e` for every `e` (independent of `H`!).
3. Exact coherent rank-1 worst-case: `multiheadDistSq (coherentHeads H d_c) (allOnesVec d_c) = H * d_c^2`.
4. Inductive Walsh-Hadamard orthogonality for all `d_c = 2^k` and `H ≤ 2^k`, with exact
   constructive witnesses at `d_c = 64` for `H ∈ {8, 16, 32, 64}` (`4096` vs `32768, 65536, 131072, 262144`).
-/

namespace MlaKantorovichRope

/-- Universal Parseval tight-frame identity: if `W^T W = c I_{d_c}`, then
    `∑_h ⟨w_h, e⟩^2 = c * ‖e‖_2^2` for all `e`. -/
theorem tight_frame_distSq_exact {H d_c : Nat} (W : Fin H → Fin d_c → Rat) (c : Rat)
    (hTF : isTightFrame W c) (e : Fin d_c → Rat) :
    multiheadDistSq W e = c * normSq e := by
  unfold multiheadDistSq normSq
  rw [← dot_matVec_transpose W (matVec W e) e]
  have h1 : dot (matVec (matTranspose W) (matVec W e)) e =
      dot (matVec (matMul (matTranspose W) W) e) e := by
    rw [matVec_matMul]
  rw [h1]
  unfold isTightFrame at hTF
  rw [hTF]
  have hmv : matVec (fun i j => if i = j then c else 0) e = fun i => c * e i := by
    funext i
    unfold matVec
    have hcongr : finSum d_c (fun j => (if i = j then c else 0) * e j) =
        finSum d_c (fun j => if i = j then c * e j else 0) := by
      apply finSum_congr; intro j
      by_cases hij : i = j <;> simp [hij]
    rw [hcongr, finSum_ite_eq_right]
  rw [hmv]
  unfold dot
  have hcongr : finSum d_c (fun i => (c * e i) * e i) = finSum d_c (fun i => c * (e i * e i)) := by
    apply finSum_congr; intro i; grind
  rw [hcongr, finSum_const_mul]

/-- Universal Bessel inequality for row-orthogonal heads (`W W^T = s I_H`, `0 < s`):
    `∑_h ⟨w_h, e⟩^2 ≤ s * ‖e‖_2^2` for all `e`, independent of `H`. -/
theorem row_orthogonal_bessel_cap {H d_c : Nat} (W : Fin H → Fin d_c → Rat) (s : Rat)
    (hs : 0 < s) (hRO : isRowOrthogonal W s) (e : Fin d_c → Rat) :
    multiheadDistSq W e ≤ s * normSq e := by
  let u : Fin H → Rat := matVec W e
  let p : Fin d_c → Rat := matVec (matTranspose W) u
  let r : Fin d_c → Rat := fun j => s * e j - p j
  have hr0 : (0 : Rat) ≤ normSq r := normSq_nonneg r
  -- Compute normSq r = s * s * normSq e - 2 * s * normSq u + normSq p
  have hnorm_r : normSq r = s * s * normSq e - 2 * s * dot e p + normSq p := by
    unfold normSq dot
    dsimp only [r]
    have hexp : ∀ j : Fin d_c, (s * e j - p j) * (s * e j - p j) =
        ((s * s) * (e j * e j) - (2 * s) * (e j * p j)) + p j * p j := by
      intro j; grind
    rw [finSum_congr hexp, finSum_add, finSum_sub, finSum_const_mul, finSum_const_mul]
  -- dot e p = normSq u
  have hdot_ep : dot e p = normSq u := by
    dsimp only [p, u]
    have hcomm : dot e (matVec (matTranspose W) (matVec W e)) =
        dot (matVec (matTranspose W) (matVec W e)) e := by
      unfold dot; apply finSum_congr; intro j; grind
    rw [hcomm, dot_matVec_transpose]
    rfl
  -- normSq p = s * normSq u
  have hnorm_p : normSq p = s * normSq u := by
    unfold normSq
    dsimp only [p]
    rw [dot_matVec_transpose W u (matVec (matTranspose W) u)]
    rw [← matVec_matMul]
    unfold isRowOrthogonal at hRO
    rw [hRO]
    have hmv : matVec (fun i j => if i = j then s else 0) u = fun i => s * u i := by
      funext i
      unfold matVec
      have hcongr : finSum H (fun j => (if i = j then s else 0) * u j) =
          finSum H (fun j => if i = j then s * u j else 0) := by
        apply finSum_congr; intro j
        by_cases hij : i = j <;> simp [hij]
      rw [hcongr, finSum_ite_eq_right]
    rw [hmv]
    unfold dot
    have hcongr : finSum H (fun i => u i * (s * u i)) = finSum H (fun i => s * (u i * u i)) := by
      apply finSum_congr; intro i; grind
    rw [hcongr, finSum_const_mul]
  rw [hnorm_r, hdot_ep, hnorm_p] at hr0
  have hfact : s * s * normSq e - 2 * s * normSq u + s * normSq u =
      s * (s * normSq e - normSq u) := by grind
  rw [hfact] at hr0
  have hdiv := rat_div_nonneg hr0 hs
  have hsimp : (s * (s * normSq e - normSq u)) / s = s * normSq e - normSq u := by
    rw [Rat.mul_comm, rat_mul_div_cancel (Rat.ne_of_gt hs)]
  rw [hsimp] at hdiv
  exact rat_le_of_sub_nonneg hdiv

/-- Exact coherent rank-1 multi-head worst-case squared distortion `H * d_c^2`. -/
theorem coherent_heads_worst_case (H d_c : Nat) :
    multiheadDistSq (coherentHeads H d_c) (allOnesVec d_c) =
      (H : Rat) * ((d_c : Rat) * (d_c : Rat)) := by
  unfold multiheadDistSq normSq dot matVec coherentHeads allOnesVec
  have hinner : ∀ _ : Fin H, finSum d_c (fun _ => (1 : Rat) * 1) = (d_c : Rat) := by
    intro _
    have h1 : finSum d_c (fun _ => (1 : Rat) * 1) = finSum d_c (fun _ => (1 : Rat)) := by
      apply finSum_congr; intro _; grind
    rw [h1, finSum_const, Rat.mul_one]
  have houter : finSum H (fun h =>
      finSum d_c (fun _ => (1 : Rat) * 1) * finSum d_c (fun _ => (1 : Rat) * 1)) =
      finSum H (fun _ => (d_c : Rat) * (d_c : Rat)) := by
    apply finSum_congr; intro h; rw [hinner h]
  rw [houter, finSum_const]

/-- Any Rademacher vector `z ∈ {-1, +1}^{d_c}` has `normSq z = d_c`. -/
theorem rademacher_normSq {d_c : Nat} (z : Fin d_c → Rat) (hz : ∀ j, z j * z j = 1) :
    normSq z = (d_c : Rat) := by
  unfold normSq dot
  rw [finSum_congr hz, finSum_const, Rat.mul_one]

/-! ### Inductive Walsh-Hadamard orthogonality for all `d_c = 2^k` -/

theorem finSum_double (m : Nat) (f : Fin (2 * m) → Rat) :
    finSum (2 * m) f =
      finSum m (fun q => f ⟨2 * q.val, by omega⟩ + f ⟨2 * q.val + 1, by omega⟩) := by
  induction m with
  | zero => simp [finSum]
  | succ k ih =>
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    -- Compute directly by unfolding finSum twice on 2*k + 2
    have hstep : ∀ (g : Fin (2 * k + 2) → Rat),
        finSum (2 * k + 2) g =
          finSum (2 * k) (fun i => g ⟨i.val, by omega⟩) +
            (g ⟨2 * k, by omega⟩ + g ⟨2 * k + 1, by omega⟩) := by
      intro g
      simp only [finSum]
      grind
    have hcast : finSum (2 * (k + 1)) f =
        finSum (2 * k + 2) (fun i => f ⟨i.val, by omega⟩) := by
      cases h2
      rfl
    rw [hcast, hstep]
    rw [ih (fun i => f ⟨i.val, by omega⟩)]
    simp only [finSum]

theorem walshEntry_symm (k i j : Nat) : walshEntry k i j = walshEntry k j i := by
  induction k generalizing i j with
  | zero => rfl
  | succ k ih =>
    simp only [walshEntry]
    rw [ih (i / 2) (j / 2)]
    by_cases hi : i % 2 = 1 <;> by_cases hj : j % 2 = 1 <;> simp [hi, hj]

theorem finSum_eq_of_eq {m n : Nat} (h : m = n) (f : Nat → Rat) :
    finSum m (fun j => f j.val) = finSum n (fun j => f j.val) := by
  subst h; rfl

theorem walsh_row_dot (k : Nat) :
    ∀ i1 i2 : Nat, i1 < 2 ^ k → i2 < 2 ^ k →
      finSum (2 ^ k) (fun j => walshEntry k i1 j.val * walshEntry k i2 j.val) =
        if i1 = i2 then ((2 ^ k : Nat) : Rat) else 0 := by
  induction k with
  | zero =>
    intro i1 i2 h1 h2
    have hi1 : i1 = 0 := by omega
    have hi2 : i2 = 0 := by omega
    subst hi1; subst hi2
    simp [finSum, walshEntry]; grind
  | succ k ih =>
    intro i1 i2 h1 h2
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [finSum_eq_of_eq hpow (fun j => walshEntry (k + 1) i1 j * walshEntry (k + 1) i2 j)]
    rw [finSum_double]
    have hpair : ∀ q : Fin (2 ^ k),
        walshEntry (k + 1) i1 (2 * q.val) * walshEntry (k + 1) i2 (2 * q.val) +
        walshEntry (k + 1) i1 (2 * q.val + 1) * walshEntry (k + 1) i2 (2 * q.val + 1) =
        (if i1 % 2 = i2 % 2 then (2 : Rat) else 0) *
          (walshEntry k (i1 / 2) q.val * walshEntry k (i2 / 2) q.val) := by
      intro q
      simp only [walshEntry]
      have h2q_mod : (2 * q.val) % 2 = 0 := by omega
      have h2q_div : (2 * q.val) / 2 = q.val := by omega
      have h2q1_mod : (2 * q.val + 1) % 2 = 1 := by omega
      have h2q1_div : (2 * q.val + 1) / 2 = q.val := by omega
      rw [h2q_mod, h2q_div, h2q1_mod, h2q1_div]
      have hmod1 : i1 % 2 = 0 ∨ i1 % 2 = 1 := by omega
      have hmod2 : i2 % 2 = 0 ∨ i2 % 2 = 1 := by omega
      rcases hmod1 with hm1 | hm1 <;> rcases hmod2 with hm2 | hm2 <;>
        simp [hm1, hm2] <;> grind
    rw [finSum_congr hpair, finSum_const_mul]
    have hd1 : i1 / 2 < 2 ^ k := by omega
    have hd2 : i2 / 2 < 2 ^ k := by omega
    rw [ih (i1 / 2) (i2 / 2) hd1 hd2]
    by_cases heq : i1 = i2
    · subst heq
      simp only [↓reduceIte]
      have hnat : ((2 ^ (k + 1) : Nat) : Rat) = 2 * ((2 ^ k : Nat) : Rat) := by
        rw [hpow, Rat.natCast_mul]
        rfl
      rw [hnat]
    · simp only [heq, ↓reduceIte]
      by_cases hmod : i1 % 2 = i2 % 2
      · have hdiv_ne : i1 / 2 ≠ i2 / 2 := by omega
        simp [hmod, hdiv_ne]
      · simp [hmod]

theorem walshHeads_row_orthogonal (k H : Nat) (hH : H ≤ 2 ^ k) :
    isRowOrthogonal (walshHeads k H) ((2 ^ k : Nat) : Rat) := by
  funext h1 h2
  unfold matMul matTranspose walshHeads
  have h1lt : h1.val < 2 ^ k := Nat.lt_of_lt_of_le h1.isLt hH
  have h2lt : h2.val < 2 ^ k := Nat.lt_of_lt_of_le h2.isLt hH
  rw [walsh_row_dot k h1.val h2.val h1lt h2lt]
  by_cases heq : h1 = h2
  · subst heq; simp
  · have hval : h1.val ≠ h2.val := fun h => heq (Fin.ext h)
    simp [heq, hval]

theorem walshHeads_full_tight_frame (k : Nat) :
    isTightFrame (walshHeads k (2 ^ k)) ((2 ^ k : Nat) : Rat) := by
  funext i j
  unfold matMul matTranspose walshHeads
  have hcongr : finSum (2 ^ k) (fun h => walshEntry k h.val i.val * walshEntry k h.val j.val) =
      finSum (2 ^ k) (fun h => walshEntry k i.val h.val * walshEntry k j.val h.val) := by
    apply finSum_congr; intro h
    rw [walshEntry_symm k h.val i.val, walshEntry_symm k h.val j.val]
  rw [hcongr, walsh_row_dot k i.val j.val i.isLt j.isLt]
  by_cases heq : i = j
  · subst heq; simp
  · have hval : i.val ≠ j.val := fun h => heq (Fin.ext h)
    simp [heq, hval]

/-- Theorem 4 (Exact Parseval Tight-Frame Multi-Head Interference Cap):
    Proves universal Parseval tight-frame distortion `c * ‖e‖_2^2` (in particular `(H / d_c) * ‖e‖_2^2`),
    universal row-orthogonal Bessel cap `s * ‖e‖_2^2` (giving `d_c^2` independent of `H` for
    Rademacher errors vs `H * d_c^2` for coherent heads — exact `H×` contraction), and constructive
    Walsh-Hadamard witnesses at `d_c = 64` for `H ∈ {8, 16, 32, 64}` (`4096` vs `32768, 65536, 131072, 262144`). -/
theorem parseval_tight_frame_multihead_interference_cap :
    (∀ (H d_c : Nat) (W : Fin H → Fin d_c → Rat) (c : Rat) (e : Fin d_c → Rat),
      isTightFrame W c → multiheadDistSq W e = c * normSq e) ∧
    (∀ (H d_c : Nat) (W : Fin H → Fin d_c → Rat) (s : Rat) (e : Fin d_c → Rat),
      0 < s → isRowOrthogonal W s → multiheadDistSq W e ≤ s * normSq e) ∧
    (∀ (H d_c : Nat) (W : Fin H → Fin d_c → Rat) (z : Fin d_c → Rat),
      0 < d_c → isRowOrthogonal W (d_c : Rat) → (∀ j, z j * z j = 1) →
      multiheadDistSq W z ≤ (d_c : Rat) * (d_c : Rat) ∧
      multiheadDistSq (coherentHeads H d_c) (allOnesVec d_c) =
        (H : Rat) * ((d_c : Rat) * (d_c : Rat))) ∧
    ((isRowOrthogonal (walshHeads 6 8) 64 ∧
      (∀ z : Fin 64 → Rat, (∀ j, z j * z j = 1) → multiheadDistSq (walshHeads 6 8) z ≤ 4096) ∧
      multiheadDistSq (coherentHeads 8 64) (allOnesVec 64) = 32768 ∧
      (32768 : Rat) / 4096 = 8) ∧
     (isRowOrthogonal (walshHeads 6 16) 64 ∧
      (∀ z : Fin 64 → Rat, (∀ j, z j * z j = 1) → multiheadDistSq (walshHeads 6 16) z ≤ 4096) ∧
      multiheadDistSq (coherentHeads 16 64) (allOnesVec 64) = 65536 ∧
      (65536 : Rat) / 4096 = 16) ∧
     (isRowOrthogonal (walshHeads 6 32) 64 ∧
      (∀ z : Fin 64 → Rat, (∀ j, z j * z j = 1) → multiheadDistSq (walshHeads 6 32) z ≤ 4096) ∧
      multiheadDistSq (coherentHeads 32 64) (allOnesVec 64) = 131072 ∧
      (131072 : Rat) / 4096 = 32) ∧
     (isRowOrthogonal (walshHeads 6 64) 64 ∧
      isTightFrame (walshHeads 6 64) 64 ∧
      (∀ z : Fin 64 → Rat, (∀ j, z j * z j = 1) → multiheadDistSq (walshHeads 6 64) z = 4096) ∧
      multiheadDistSq (coherentHeads 64 64) (allOnesVec 64) = 262144 ∧
      (262144 : Rat) / 4096 = 64)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H d_c W c e hTF
    exact tight_frame_distSq_exact W c hTF e
  · intro H d_c W s e hs hRO
    exact row_orthogonal_bessel_cap W s hs hRO e
  · intro H d_c W z hdc hRO hz
    have hcap := row_orthogonal_bessel_cap W (d_c : Rat) (rat_natCast_pos hdc) hRO z
    rw [rademacher_normSq z hz] at hcap
    exact ⟨hcap, coherent_heads_worst_case H d_c⟩
  · have h64 : ((2 ^ 6 : Nat) : Rat) = 64 := by grind
    have h8ro : isRowOrthogonal (walshHeads 6 8) 64 := by
      have h := walshHeads_row_orthogonal 6 8 (by decide); rwa [h64] at h
    have h16ro : isRowOrthogonal (walshHeads 6 16) 64 := by
      have h := walshHeads_row_orthogonal 6 16 (by decide); rwa [h64] at h
    have h32ro : isRowOrthogonal (walshHeads 6 32) 64 := by
      have h := walshHeads_row_orthogonal 6 32 (by decide); rwa [h64] at h
    have h64ro : isRowOrthogonal (walshHeads 6 64) 64 := by
      have h := walshHeads_row_orthogonal 6 64 (by decide); rwa [h64] at h
    have h64tf : isTightFrame (walshHeads 6 64) 64 := by
      have h := walshHeads_full_tight_frame 6; rwa [h64] at h
    refine ⟨⟨h8ro, ?_, ?_, by grind⟩, ⟨h16ro, ?_, ?_, by grind⟩,
            ⟨h32ro, ?_, ?_, by grind⟩, ⟨h64ro, h64tf, ?_, ?_, by grind⟩⟩
    · intro z hz
      have h := row_orthogonal_bessel_cap (walshHeads 6 8) 64 (by decide) h8ro z
      rw [rademacher_normSq z hz] at h
      have h4096 : (64 : Rat) * ((64 : Nat) : Rat) = 4096 := by grind
      rwa [h4096] at h
    · rw [coherent_heads_worst_case 8 64]; grind
    · intro z hz
      have h := row_orthogonal_bessel_cap (walshHeads 6 16) 64 (by decide) h16ro z
      rw [rademacher_normSq z hz] at h
      have h4096 : (64 : Rat) * ((64 : Nat) : Rat) = 4096 := by grind
      rwa [h4096] at h
    · rw [coherent_heads_worst_case 16 64]; grind
    · intro z hz
      have h := row_orthogonal_bessel_cap (walshHeads 6 32) 64 (by decide) h32ro z
      rw [rademacher_normSq z hz] at h
      have h4096 : (64 : Rat) * ((64 : Nat) : Rat) = 4096 := by grind
      rwa [h4096] at h
    · rw [coherent_heads_worst_case 32 64]; grind
    · intro z hz
      rw [tight_frame_distSq_exact (walshHeads 6 64) 64 h64tf z, rademacher_normSq z hz]
      grind
    · rw [coherent_heads_worst_case 64 64]; grind

end MlaKantorovichRope
