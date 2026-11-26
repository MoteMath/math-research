/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmTustinPade.Pade02Laws

/-!
# Theorem 6: SSM Trajectory Energy Conservation & Nyquist Blowup (`ssm_trajectory_energy_conservation_and_nyquist_blowup`)

Exact inductive trajectory laws for `h_{t+1} = a * h_t + b * u_t`, `h_0 = 0`:
- (a) Tustin Nyquist snap (`a = -1`) under alternating input `u_t = (-1)^t`:
      `|h_T| = T * |b|` (linear unbounded growth) and `h_T^2 = T^2 * b^2` (`O(T^2)` energy blowup).
- (b) Infinite-memory stall (`a = 1`) under constant input `u_t = 1`:
      `h_T = T * b` (linear unbounded growth) and `h_T^2 = T^2 * b^2`.
- (c) Strictly contractive positive pole (`0 < a < 1`, instantiated by `Padé-(0,2)`):
      `|h_T| ≤ |b| / (1 - a)` uniformly for all `T : Nat` whenever `|u_t| ≤ 1`.
-/

namespace SsmTustinPade

theorem altSign_sq (t : Nat) : altSign t * altSign t = 1 := by
  induction t with
  | zero => unfold altSign; grind
  | succ k ih =>
    simp only [altSign]
    grind

theorem ratAbs_altSign (t : Nat) : ratAbs (altSign t) = 1 := by
  induction t with
  | zero => unfold altSign ratAbs; decide
  | succ k ih =>
    simp only [altSign]
    rw [ratAbs_neg, ih]

theorem ssmState_nyquist_exact (b : Rat) (T : Nat) :
    ssmState (-1) b altSign T = -(altSign T) * (T : Rat) * b := by
  induction T with
  | zero =>
    simp [ssmState, altSign]
  | succ k ih =>
    simp only [ssmState, altSign, ih]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by simp
    rw [hcast]
    grind

theorem ssmState_nyquist_abs_and_energy (b : Rat) (T : Nat) :
    ratAbs (ssmState (-1) b altSign T) = (T : Rat) * ratAbs b ∧
    ssmState (-1) b altSign T * ssmState (-1) b altSign T = (T : Rat) * (T : Rat) * (b * b) := by
  rw [ssmState_nyquist_exact]
  constructor
  · rw [ratAbs_mul, ratAbs_mul, ratAbs_neg, ratAbs_altSign,
        ratAbs_of_nonneg (natCast_rat_nonneg T)]
    grind
  · have hsq := altSign_sq T
    grind

theorem ssmState_stall_exact (b : Rat) (T : Nat) :
    ssmState 1 b (fun _ => 1) T = (T : Rat) * b := by
  induction T with
  | zero =>
    simp [ssmState]
  | succ k ih =>
    simp only [ssmState, ih]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by simp
    rw [hcast]
    grind

theorem ssmState_contractive_uniform_bound {a b : Rat} {u : Nat → Rat}
    (ha0 : (0 : Rat) < a) (ha1 : a < 1) (hu : ∀ t : Nat, ratAbs (u t) ≤ 1) :
    ∀ T : Nat, ratAbs (ssmState a b u T) ≤ ratAbs b / (1 - a) := by
  have h1a : (0 : Rat) < 1 - a := rat_sub_pos ha1
  have h1a_ne : 1 - a ≠ 0 := Rat.ne_of_gt h1a
  intro T
  induction T with
  | zero =>
    simp only [ssmState]
    have h0 : ratAbs 0 = 0 := by decide
    rw [h0]
    exact rat_div_nonneg (ratAbs_nonneg b) h1a
  | succ k ih =>
    simp only [ssmState]
    have htri : ratAbs (a * ssmState a b u k + b * u k) ≤
        ratAbs (a * ssmState a b u k) + ratAbs (b * u k) := ratAbs_add_le _ _
    rw [ratAbs_mul, ratAbs_mul, ratAbs_of_nonneg (Rat.le_of_lt ha0)] at htri
    have h1 : a * ratAbs (ssmState a b u k) ≤ a * (ratAbs b / (1 - a)) :=
      rat_mul_le_mul_of_nonneg_left ih (Rat.le_of_lt ha0)
    have h2 : ratAbs b * ratAbs (u k) ≤ ratAbs b * 1 :=
      rat_mul_le_mul_of_nonneg_left (hu k) (ratAbs_nonneg b)
    have h3 := rat_add_le_add h1 h2
    have hcomb : a * (ratAbs b / (1 - a)) + ratAbs b * 1 = ratAbs b / (1 - a) := by
      have hmul : (ratAbs b / (1 - a)) * (1 - a) = ratAbs b := rat_div_mul_cancel h1a_ne
      symm
      rw [rat_div_eq_iff h1a_ne]
      grind
    rw [hcomb] at h3
    exact Rat.le_trans htri h3

/-- Headline Theorem 6 (`ssm_trajectory_energy_conservation_and_nyquist_blowup`). -/
theorem ssm_trajectory_energy_conservation_and_nyquist_blowup :
    (∀ (b : Rat) (T : Nat),
      ssmState (-1) b altSign T = -(altSign T) * (T : Rat) * b ∧
      ratAbs (ssmState (-1) b altSign T) = (T : Rat) * ratAbs b ∧
      ssmState (-1) b altSign T * ssmState (-1) b altSign T =
        (T : Rat) * (T : Rat) * (b * b)) ∧
    (∀ (b : Rat) (T : Nat),
      ssmState 1 b (fun _ => 1) T = (T : Rat) * b ∧
      ratAbs (ssmState 1 b (fun _ => 1) T) = (T : Rat) * ratAbs b ∧
      ssmState 1 b (fun _ => 1) T * ssmState 1 b (fun _ => 1) T =
        (T : Rat) * (T : Rat) * (b * b)) ∧
    (∀ (a b : Rat) (u : Nat → Rat),
      (0 : Rat) < a → a < 1 → (∀ t : Nat, ratAbs (u t) ≤ 1) →
      ∀ T : Nat, ratAbs (ssmState a b u T) ≤ ratAbs b / (1 - a)) ∧
    (∀ (z : Rat) (u : Nat → Rat),
      (0 : Rat) < z → (∀ t : Nat, ratAbs (u t) ≤ 1) →
      ∀ T : Nat, ratAbs (ssmState (pade02A z) (pade02B z) u T) ≤
        pade02B z / (1 - pade02A z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b T
    have h := ssmState_nyquist_abs_and_energy b T
    exact ⟨ssmState_nyquist_exact b T, h.1, h.2⟩
  · intro b T
    have h := ssmState_stall_exact b T
    refine ⟨h, ?_, ?_⟩
    · rw [h, ratAbs_mul, ratAbs_of_nonneg (natCast_rat_nonneg T)]
    · rw [h]; grind
  · intro a b u ha0 ha1 hu
    exact ssmState_contractive_uniform_bound ha0 ha1 hu
  · intro z u hz hu T
    have ha := pade02A_pos_and_lt_one hz
    have hb := pade02B_pos_and_le_one (Rat.le_of_lt hz)
    have hbound := ssmState_contractive_uniform_bound (b := pade02B z) ha.1 ha.2 hu T
    rw [ratAbs_of_nonneg (Rat.le_of_lt hb.1)] at hbound
    exact hbound

end SsmTustinPade
