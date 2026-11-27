/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MortonCarryMonodromyRenorm.Defs

/-!
# Theorems (`MortonCarryMonodromyRenorm`)

# Carry-Monodromy Renormalization (CMR): A Reusable Infinite Proof Mechanism for
# Morton / Radix-B Digit-Permutation + Carry-Arithmetic Dynamics

Worker: `dynsil-4` (Thread 2: Bitwise Dynamics, T-Functions & Reversible Silicon Orbit Mechanisms)
Standalone Lean 4.36.0 — ZERO Mathlib, ZERO external dependencies, ZERO `sorry`, ZERO custom axioms.
-/


namespace Dynsil4.CMR
@[simp] theorem iter_zero {α : Type} (f : α → α) (x : α) : iter f 0 x = x := rfl
@[simp] theorem iter_succ {α : Type} (f : α → α) (k : Nat) (x : α) :
    iter f (k + 1) x = f (iter f k x) := rfl

theorem iter_succ_inner {α : Type} (f : α → α) (k : Nat) (x : α) :
    iter f (k + 1) x = iter f k (f x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iter_succ, ih, iter_succ]

theorem iter_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f a (iter f b x) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, iter_succ, ih, iter_succ]

theorem iter_mul {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a * b) x = iter (iter f b) a x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Nat.add_comm (a * b) b, iter_add, ih, iter_succ]

theorem iter_congr {α : Type} {f g : α → α} {P : α → Prop}
    (hf : ∀ x, P x → P (f x))
    (hfg : ∀ x, P x → f x = g x)
    (k : Nat) (x : α) (hx : P x) :
    iter f k x = iter g k x ∧ P (iter f k x) := by
  induction k with
  | zero => exact ⟨rfl, hx⟩
  | succ k ih =>
    obtain ⟨heq, hp⟩ := ih
    refine ⟨?_, hf _ hp⟩
    rw [iter_succ, iter_succ, ← heq, hfg _ hp]

theorem hasExactPeriod_of_congr {α : Type} {f g : α → α} {P_inv : α → Prop}
    {x : α} {P : Nat}
    (hf : ∀ y, P_inv y → P_inv (f y))
    (hfg : ∀ y, P_inv y → f y = g y)
    (hx : P_inv x)
    (hper : HasExactPeriod f x P) :
    HasExactPeriod g x P := by
  refine ⟨hper.1, ?_, ?_⟩
  · rw [← (iter_congr hf hfg P x hx).1]; exact hper.2.1
  · intro t ht1 ht2
    rw [← (iter_congr hf hfg t x hx).1]
    exact hper.2.2 t ht1 ht2

theorem iter_mod_period {α : Type} (f : α → α) (x : α) (P : Nat)
    (_hP : 0 < P) (hfix : iter f P x = x) (t : Nat) :
    iter f t x = iter f (t % P) x := by
  have hdiv : t = t % P + P * (t / P) := by
    have := Nat.div_add_mod t P
    omega
  have hmul : iter f (P * (t / P)) x = x := by
    rw [Nat.mul_comm, iter_mul]
    generalize t / P = q
    induction q with
    | zero => rfl
    | succ k ih => rw [iter_succ, ih, hfix]
  calc iter f t x = iter f (t % P + P * (t / P)) x := by rw [← hdiv]
    _ = iter f (t % P) (iter f (P * (t / P)) x) := iter_add f (t % P) (P * (t / P)) x
    _ = iter f (t % P) x := by rw [hmul]

theorem period_dvd_of_iter_eq {α : Type} {f : α → α} {x : α} {P t : Nat}
    (hper : HasExactPeriod f x P) (heq : iter f t x = x) :
    P ∣ t := by
  have hmod := iter_mod_period f x P hper.1 hper.2.1 t
  rw [heq] at hmod
  by_cases h0 : t % P = 0
  · exact Nat.dvd_of_mod_eq_zero h0
  · exfalso
    have hlt : t % P < P := Nat.mod_lt t hper.1
    exact hper.2.2 (t % P) (Nat.pos_of_ne_zero h0) hlt hmod.symm

namespace DigitPerm
theorem pow_toFun_eq_iter {B : Nat} (π : DigitPerm B) (k a : Nat) :
    (π.pow k).toFun a = iter π.toFun k a := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow, comp, iter_succ, ih]

theorem toFun_inj {B : Nat} (π : DigitPerm B) {a b : Nat} (ha : a < B) (hb : b < B)
    (h : π.toFun a = π.toFun b) : a = b := by
  have := congrArg π.invFun h
  rw [π.h_left a ha, π.h_left b hb] at this
  exact this

end DigitPerm
theorem tau_lt (B : Nat) (hB : 0 < B) (π : DigitPerm B) (a : Nat) :
    tau B π a < B :=
  Nat.mod_lt _ hB

theorem tau_iter_lt (B : Nat) (hB : 0 < B) (π : DigitPerm B) (r a : Nat) (ha : a < B) :
    iter (tau B π) r a < B := by
  cases r with
  | zero => exact ha
  | succ r => exact Nat.mod_lt _ hB

theorem wordPerm_lt (B : Nat) (hB : 0 < B) (π : DigitPerm B) (n z : Nat) :
    wordPerm B π n z < B ^ n := by
  induction n generalizing z with
  | zero => simp [wordPerm]
  | succ n ih =>
    simp only [wordPerm, Nat.pow_succ]
    have h1 : π.toFun (z % B) < B := π.h_lt (z % B) (Nat.mod_lt z hB)
    have h2 : wordPerm B π n (z / B) < B ^ n := ih (z / B)
    have hmul : B * wordPerm B π n (z / B) + B ≤ B * (B ^ n) := by
      have : wordPerm B π n (z / B) + 1 ≤ B ^ n := h2
      have := Nat.mul_le_mul_left B this
      rw [Nat.mul_add, Nat.mul_one] at this
      exact this
    rw [Nat.mul_comm (B ^ n) B]
    omega

theorem wordPerm_add_mul (B : Nat) (hB : 0 < B) (π : DigitPerm B) (n a h : Nat) (ha : a < B) :
    wordPerm B π (n + 1) (a + B * h) = π.toFun a + B * wordPerm B π n h := by
  simp only [wordPerm]
  have hmod : (a + B * h) % B = a := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have hdiv : (a + B * h) / B = h := by
    rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha, Nat.zero_add]
  rw [hmod, hdiv]

theorem wordPerm_congr (B : Nat) (hB : 0 < B) {π₁ π₂ : DigitPerm B}
    (h : ∀ a, a < B → π₁.toFun a = π₂.toFun a) (n z : Nat) :
    wordPerm B π₁ n z = wordPerm B π₂ n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [wordPerm]
    rw [h (z % B) (Nat.mod_lt z hB), ih (z / B)]

theorem wordPerm_id (B : Nat) (_hB : 0 < B) (n z : Nat) (hz : z < B ^ n) :
    wordPerm B (DigitPerm.id B) n z = z := by
  induction n generalizing z with
  | zero =>
    simp only [Nat.pow_zero] at hz
    simp only [wordPerm]; omega
  | succ n ih =>
    rw [wordPerm]
    have hdiv_lt : z / B < B ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm] at hz
      exact Nat.div_lt_of_lt_mul hz
    rw [ih (z / B) hdiv_lt]
    change z % B + B * (z / B) = z
    have := Nat.div_add_mod z B
    omega

theorem wordPerm_comp (B : Nat) (hB : 0 < B) (π₁ π₂ : DigitPerm B) (n z : Nat) :
    wordPerm B π₁ n (wordPerm B π₂ n z) = wordPerm B (DigitPerm.comp π₁ π₂) n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [wordPerm]
    have hlt : π₂.toFun (z % B) < B := π₂.h_lt _ (Nat.mod_lt z hB)
    have hmod : (π₂.toFun (z % B) + B * wordPerm B π₂ n (z / B)) % B = π₂.toFun (z % B) := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have hdiv : (π₂.toFun (z % B) + B * wordPerm B π₂ n (z / B)) / B = wordPerm B π₂ n (z / B) := by
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hlt, Nat.zero_add]
    rw [hmod, hdiv, ih (z / B)]
    rfl

theorem wordPerm_iter (B : Nat) (hB : 0 < B) (π : DigitPerm B) (n k z : Nat) (hz : z < B ^ n) :
    iter (wordPerm B π n) k z = wordPerm B (π.pow k) n z := by
  induction k with
  | zero =>
    simp only [iter_zero, DigitPerm.pow]
    exact (wordPerm_id B hB n z hz).symm
  | succ k ih =>
    rw [iter_succ, ih, wordPerm_comp B hB]
    rfl

theorem wordPerm_inj (B : Nat) (hB : 0 < B) (π : DigitPerm B) (n : Nat)
    {x y : Nat} (hx : x < B ^ n) (hy : y < B ^ n)
    (heq : wordPerm B π n x = wordPerm B π n y) : x = y := by
  induction n generalizing x y with
  | zero =>
    simp only [Nat.pow_zero] at hx hy; omega
  | succ n ih =>
    simp only [wordPerm] at heq
    have hmx : π.toFun (x % B) < B := π.h_lt _ (Nat.mod_lt x hB)
    have hmy : π.toFun (y % B) < B := π.h_lt _ (Nat.mod_lt y hB)
    have hmod_eq : π.toFun (x % B) = π.toFun (y % B) := by
      have h1 := congrArg (· % B) heq
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmx,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmy] at h1
      exact h1
    have hdiv_eq : wordPerm B π n (x / B) = wordPerm B π n (y / B) := by
      have h1 := congrArg (· / B) heq
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hmx, Nat.zero_add,
          Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hmy, Nat.zero_add] at h1
      exact h1
    have hxmod : x % B = y % B :=
      π.toFun_inj (Nat.mod_lt x hB) (Nat.mod_lt y hB) hmod_eq
    have hxdiv_lt : x / B < B ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm] at hx; exact Nat.div_lt_of_lt_mul hx
    have hydiv_lt : y / B < B ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm] at hy; exact Nat.div_lt_of_lt_mul hy
    have hxdiv : x / B = y / B := ih hxdiv_lt hydiv_lt hdiv_eq
    have hdx := Nat.div_add_mod x B
    have hdy := Nat.div_add_mod y B
    rw [← hdx, ← hdy, hxdiv, hxmod]

theorem step_lt (B : Nat) (hB : 0 < B) (π : DigitPerm B) (n z : Nat) :
    step B π n z < B ^ n :=
  Nat.mod_lt _ (Nat.pow_pos hB)

theorem step_congr (B : Nat) (hB : 0 < B) {π₁ π₂ : DigitPerm B}
    (h : ∀ a, a < B → π₁.toFun a = π₂.toFun a) (n z : Nat) :
    step B π₁ n z = step B π₂ n z := by
  simp only [step, wordPerm_congr B hB h n z]

/-- Splitting `step B π (n + 1) (a + B * h)` when NO carry exits digit 0 (`π(a) < B - 1`). -/
theorem step_add_mul_no_carry (B : Nat) (hB : 2 ≤ B) (π : DigitPerm B) (n a h : Nat)
    (ha : a < B) (hnc : π.toFun a < B - 1) :
    step B π (n + 1) (a + B * h) = tau B π a + B * wordPerm B π n h := by
  have hBpos : 0 < B := by omega
  simp only [step, tau]
  rw [wordPerm_add_mul B hBpos π n a h ha]
  have hpi_succ : π.toFun a + 1 < B := by omega
  have hwp_lt : wordPerm B π n h < B ^ n := wordPerm_lt B hBpos π n h
  have htot : π.toFun a + B * wordPerm B π n h + 1 < B ^ (n + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm (B ^ n) B]
    have hle : B * (wordPerm B π n h + 1) ≤ B * B ^ n := Nat.mul_le_mul_left B hwp_lt
    rw [Nat.mul_add, Nat.mul_one] at hle
    omega
  rw [Nat.mod_eq_of_lt htot, Nat.mod_eq_of_lt hpi_succ]
  omega

/-- Splitting `step B π (n + 1) (a + B * h)` when a CARRY exits digit 0 (`π(a) = B - 1`). -/
theorem step_add_mul_carry (B : Nat) (hB : 2 ≤ B) (π : DigitPerm B) (n a h : Nat)
    (ha : a < B) (hc : π.toFun a = B - 1) :
    step B π (n + 1) (a + B * h) = B * step B π n h := by
  have hBpos : 0 < B := by omega
  simp only [step]
  rw [wordPerm_add_mul B hBpos π n a h ha, hc]
  have hrew : B - 1 + B * wordPerm B π n h + 1 = B * (wordPerm B π n h + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [hrew, Nat.pow_succ, Nat.mul_comm (B ^ n) B, Nat.mul_mod_mul_left]

theorem CarryCycleCert.tau_pos_ne_zero {B : Nat} (hB : 2 ≤ B) {π : DigitPerm B} {L : Nat}
    (cert : CarryCycleCert B π L) {r : Nat} (hr1 : 0 < r) (hr2 : r < L) :
    iter (tau B π) r 0 ≠ 0 := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr1)
  have hlt : r' < L - 1 := by omega
  have hnc := cert.h_no_carry r' hlt
  rw [iter_succ, tau]
  have hltB : π.toFun (iter (tau B π) r' 0) + 1 < B := by omega
  rw [Nat.mod_eq_of_lt hltB]
  omega

theorem CarryCycleCert.tau_period {B : Nat} (hB : 2 ≤ B) {π : DigitPerm B} {L : Nat}
    (cert : CarryCycleCert B π L) :
    iter (tau B π) L 0 = 0 := by
  have hL : L = (L - 1) + 1 := by have := cert.hL; omega
  rw [hL, iter_succ, tau, cert.h_carry]
  have : B - 1 + 1 = B := by omega
  rw [this, Nat.mod_self]

/-- **CMR Theorem 1 (Carry-Free Phase Formula):**
For `0 ≤ r < L`, starting from the fiber basepoint `B * h`, `r` steps of `step B π (n + 1)`
advance digit 0 along `τ^r(0)` and apply `π^r` purely (carry-free) to the high word `h`. -/
theorem cmr_fiber_phase {B : Nat} (hB : 2 ≤ B) {π : DigitPerm B} {L : Nat}
    (cert : CarryCycleCert B π L) (n h : Nat) (hh : h < B ^ n) :
    ∀ r, r < L →
      iter (step B π (n + 1)) r (B * h) =
        iter (tau B π) r 0 + B * wordPerm B (π.pow r) n h := by
  have hBpos : 0 < B := by omega
  intro r hr
  induction r with
  | zero =>
    simp only [iter_zero, Nat.zero_add, DigitPerm.pow]
    rw [wordPerm_id B hBpos n h hh]
  | succ r ih =>
    have hr_lt : r < L := by omega
    have hr_nc : r < L - 1 := by omega
    rw [iter_succ, ih hr_lt]
    have ha_lt : iter (tau B π) r 0 < B := tau_iter_lt B hBpos π r 0 hBpos
    rw [step_add_mul_no_carry B hB π n _ _ ha_lt (cert.h_no_carry r hr_nc)]
    rw [wordPerm_comp B hBpos π (π.pow r) n h]
    rfl

/-- **CMR Theorem 2 (Carry-Monodromy Return Conjugacy):**
After `L` steps of `step B π (n + 1)`, the fiber `{0} × Fin (B^n)` returns to itself,
and the exact Poincaré return map on the high word `h` is the renormalized system
`step B (π.pow L) n h`. -/
theorem cmr_fiber_return {B : Nat} (hB : 2 ≤ B) {π : DigitPerm B} {L : Nat}
    (cert : CarryCycleCert B π L) (n h : Nat) (hh : h < B ^ n) :
    iter (step B π (n + 1)) L (B * h) = B * step B (π.pow L) n h := by
  have hBpos : 0 < B := by omega
  have hL : L = (L - 1) + 1 := by have := cert.hL; omega
  have hpred : L - 1 < L := by have := cert.hL; omega
  have ha_lt : iter (tau B π) (L - 1) 0 < B := tau_iter_lt B hBpos π (L - 1) 0 hBpos
  have hpow : DigitPerm.comp π (π.pow (L - 1)) = π.pow L := by
    calc DigitPerm.comp π (π.pow (L - 1)) = π.pow ((L - 1) + 1) := rfl
      _ = π.pow L := by rw [← hL]
  calc iter (step B π (n + 1)) L (B * h)
      = iter (step B π (n + 1)) ((L - 1) + 1) (B * h) := by rw [← hL]
    _ = step B π (n + 1) (iter (step B π (n + 1)) (L - 1) (B * h)) := rfl
    _ = step B π (n + 1) (iter (tau B π) (L - 1) 0 + B * wordPerm B (π.pow (L - 1)) n h) := by
          rw [cmr_fiber_phase hB cert n h hh (L - 1) hpred]
    _ = B * step B π n (wordPerm B (π.pow (L - 1)) n h) :=
          step_add_mul_carry B hB π n _ _ ha_lt cert.h_carry
    _ = B * step B (π.pow L) n h := by
          congr 1; simp only [step]
          rw [wordPerm_comp B hBpos π (π.pow (L - 1)) n h, hpow]

/-- **CMR Theorem 3 (Iterated Fiber Monodromy):**
For every `k : Nat`, `k * L` steps on the basepoint fiber equal `k` steps of the renormalized map. -/
theorem cmr_fiber_iter {B : Nat} (hB : 2 ≤ B) {π : DigitPerm B} {L : Nat}
    (cert : CarryCycleCert B π L) (n h : Nat) (hh : h < B ^ n) (k : Nat) :
    iter (step B π (n + 1)) (k * L) (B * h) = B * iter (step B (π.pow L) n) k h := by
  have hBpos : 0 < B := by omega
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.add_comm (k * L) L, iter_add, ih]
    have hlt : iter (step B (π.pow L) n) k h < B ^ n := by
      cases k with
      | zero => exact hh
      | succ k' => exact step_lt B hBpos (π.pow L) n _
    rw [cmr_fiber_return hB cert n _ hlt, iter_succ]

/-- **CMR Theorem 4 (General Step Decomposition on the Basepoint Fiber):**
For EVERY `t : Nat` and `h < B^n`, `t` steps of `step B π (n + 1)` split into `t / L`
renormalized coarse steps and `t % L` carry-free fine steps. -/
theorem cmr_fiber_general {B : Nat} (hB : 2 ≤ B) {π : DigitPerm B} {L : Nat}
    (cert : CarryCycleCert B π L) (n h : Nat) (hh : h < B ^ n) (t : Nat) :
    iter (step B π (n + 1)) t (B * h) =
      iter (tau B π) (t % L) 0 +
        B * wordPerm B (π.pow (t % L)) n (iter (step B (π.pow L) n) (t / L) h) := by
  have hBpos : 0 < B := by omega
  have hsplit : t = t % L + (t / L) * L := by
    have := Nat.div_add_mod t L
    rw [Nat.mul_comm] at this
    omega
  have hlt : iter (step B (π.pow L) n) (t / L) h < B ^ n := by
    cases (t / L) with
    | zero => exact hh
    | succ k' => exact step_lt B hBpos (π.pow L) n _
  calc iter (step B π (n + 1)) t (B * h)
      = iter (step B π (n + 1)) (t % L + (t / L) * L) (B * h) := by rw [← hsplit]
    _ = iter (step B π (n + 1)) (t % L) (iter (step B π (n + 1)) ((t / L) * L) (B * h)) :=
          iter_add _ _ _ _
    _ = iter (step B π (n + 1)) (t % L) (B * iter (step B (π.pow L) n) (t / L) h) := by
          rw [cmr_fiber_iter hB cert n h hh (t / L)]
    _ = iter (tau B π) (t % L) 0 +
          B * wordPerm B (π.pow (t % L)) n (iter (step B (π.pow L) n) (t / L) h) :=
          cmr_fiber_phase hB cert n _ hlt (t % L) (Nat.mod_lt t cert.hL)

/-- **CMR Theorem 5 (Exact Minimal Period Lifting Theorem):**
If `π` has carry-cycle length `L` and the renormalized map `step B (π.pow L) n` has exact minimal
period `P` at `0`, then `step B π (n + 1)` has exact minimal period `L * P` at `0`. -/
theorem cmr_exact_period_lift {B : Nat} (hB : 2 ≤ B) {π : DigitPerm B} {L n P : Nat}
    (cert : CarryCycleCert B π L)
    (hP : HasExactPeriod (step B (π.pow L) n) 0 P) :
    HasExactPeriod (step B π (n + 1)) 0 (L * P) := by
  have hBpos : 0 < B := by omega
  have h0lt : 0 < B ^ n := Nat.pow_pos hBpos
  refine ⟨Nat.mul_pos cert.hL hP.1, ?_, ?_⟩
  · have h := cmr_fiber_iter hB cert n 0 h0lt P
    rw [Nat.mul_zero] at h
    rw [Nat.mul_comm L P, h, hP.2.1, Nat.mul_zero]
  · intro t ht1 ht2 heq
    have hgen := cmr_fiber_general hB cert n 0 h0lt t
    rw [Nat.mul_zero] at hgen
    rw [hgen] at heq
    have hmod_lt : iter (tau B π) (t % L) 0 < B := tau_iter_lt B hBpos π (t % L) 0 hBpos
    have hrem0 : iter (tau B π) (t % L) 0 = 0 := by
      have h1 := congrArg (· % B) heq
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmod_lt, Nat.zero_mod] at h1
      exact h1
    have htmod : t % L = 0 := by
      by_cases h0 : t % L = 0
      · exact h0
      · exfalso
        exact cert.tau_pos_ne_zero hB (Nat.pos_of_ne_zero h0) (Nat.mod_lt t cert.hL) hrem0
    have hdiv_pos : 0 < t / L := by
      have hdm := Nat.div_add_mod t L
      rw [htmod, Nat.add_zero] at hdm
      by_cases hq : t / L = 0
      · rw [hq, Nat.mul_zero] at hdm; omega
      · exact Nat.pos_of_ne_zero hq
    have hdiv_lt : t / L < P := by
      have hdm := Nat.div_add_mod t L
      rw [htmod, Nat.add_zero] at hdm
      have hmul : L * (t / L) < L * P := by omega
      exact Nat.lt_of_mul_lt_mul_left hmul
    have hdiv0 : wordPerm B (π.pow 0) n (iter (step B (π.pow L) n) (t / L) 0) = 0 := by
      rw [htmod, iter_zero, Nat.zero_add] at heq
      have h1 := congrArg (· / B) heq
      rw [Nat.mul_div_cancel_left _ hBpos, Nat.zero_div] at h1
      exact h1
    rw [DigitPerm.pow] at hdiv0
    have hlt_iter : iter (step B (π.pow L) n) (t / L) 0 < B ^ n := by
      cases hq : t / L with
      | zero => omega
      | succ k' => exact step_lt B hBpos (π.pow L) n _
    rw [wordPerm_id B hBpos n _ hlt_iter] at hdiv0
    exact hP.2.2 (t / L) hdiv_pos hdiv_lt hdiv0

/-- Base case `n = 0`: `step B π 0` has exact period 1 at `0`. -/
theorem step_zero_exact_period (B : Nat) (π : DigitPerm B) :
    HasExactPeriod (step B π 0) 0 1 := by
  refine ⟨by omega, ?_, ?_⟩
  · simp [iter_succ, step, wordPerm]
  · intro t ht1 ht2; omega

/-- **CMR Theorem 6 (Finite Renormalization Automaton → Infinite-Width Lifting Compiler):**
ANY finite `RenormAutomaton B S` automatically proves the exact minimal period `A.orbitProd s n`
for EVERY state `s : Fin S` and EVERY word width `n : Nat` (`∀ n ≥ 0`). -/
theorem cmr_automaton_lift {B S : Nat} (hB : 2 ≤ B) (A : RenormAutomaton B S) :
    ∀ n (s : Fin S), HasExactPeriod (step B (A.perm s) n) 0 (A.orbitProd s n) := by
  have hBpos : 0 < B := by omega
  intro n
  induction n with
  | zero =>
    intro s
    exact step_zero_exact_period B (A.perm s)
  | succ n ih =>
    intro s
    simp only [RenormAutomaton.orbitProd]
    have hnext := ih (A.next s)
    have hcongr : HasExactPeriod (step B ((A.perm s).pow (A.len s)) n) 0 (A.orbitProd (A.next s) n) := by
      refine hasExactPeriod_of_congr (P_inv := fun _ => True) (fun _ _ => trivial) ?_ trivial hnext
      intro y _
      exact (step_congr B hBpos (A.closure s) n y).symm
    exact cmr_exact_period_lift hB (A.cert s) hcongr

/-- **CMR Corollary (Universal Full-Period Compiler):**
If every state in `A : RenormAutomaton B S` has carry-cycle length `B`, then for EVERY `n : Nat`,
`step B (A.perm s) n` is a single full-period Hamiltonian cycle of length `B ^ n`. -/
theorem cmr_full_period_compiler {B S : Nat} (hB : 2 ≤ B) (A : RenormAutomaton B S)
    (hfull : ∀ s, A.len s = B) (s : Fin S) (n : Nat) :
    HasExactPeriod (step B (A.perm s) n) 0 (B ^ n) := by
  have hprod : ∀ m (t : Fin S), A.orbitProd t m = B ^ m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro t
      simp only [RenormAutomaton.orbitProd, hfull t, ih (A.next t), Nat.pow_succ, Nat.mul_comm]
  rw [← hprod n s]
  exact cmr_automaton_lift hB A n s

/-- **CMR Theorem 7 (Carry-Free Strip Decoupling):**
If `a < B` lies in a carry-free `τ`-orbit (`∀ r, π(τ^r(a)) < B - 1`), then NO carry ever exits
digit 0, and `step B π (n + 1)` completely decouples into `τ^t(a)` and `wordPerm B (π^t) n h`. -/
theorem cmr_carry_free_strip {B : Nat} (hB : 2 ≤ B) (π : DigitPerm B) (n a h : Nat)
    (ha : a < B) (hh : h < B ^ n)
    (hcf : ∀ r, π.toFun (iter (tau B π) r a) < B - 1) (t : Nat) :
    iter (step B π (n + 1)) t (a + B * h) =
      iter (tau B π) t a + B * wordPerm B (π.pow t) n h := by
  have hBpos : 0 < B := by omega
  induction t with
  | zero =>
    simp only [iter_zero, DigitPerm.pow]
    rw [wordPerm_id B hBpos n h hh]
  | succ t ih =>
    rw [iter_succ, ih]
    have hlt : iter (tau B π) t a < B := tau_iter_lt B hBpos π t a ha
    rw [step_add_mul_no_carry B hB π n _ _ hlt (hcf t)]
    rw [wordPerm_comp B hBpos π (π.pow t) n h]
    rfl

/-- **CMR Theorem 8 (Carry-Free Strip Exact Period via `Nat.lcm`):**
On a carry-free strip, the exact period of `a + B * h` is `Nat.lcm L M`, where `L` is the
`τ`-period of `a` and `M` is the `wordPerm`-period of `h`. -/
theorem cmr_carry_free_period {B : Nat} (hB : 2 ≤ B) (π : DigitPerm B) (n a h L M : Nat)
    (ha : a < B) (hh : h < B ^ n)
    (hcf : ∀ r, π.toFun (iter (tau B π) r a) < B - 1)
    (hL : HasExactPeriod (tau B π) a L)
    (hM : HasExactPeriod (wordPerm B π n) h M) :
    HasExactPeriod (step B π (n + 1)) (a + B * h) (Nat.lcm L M) := by
  have hBpos : 0 < B := by omega
  have hlcm_pos : 0 < Nat.lcm L M := by
    have hne : Nat.lcm L M ≠ 0 := by
      intro h0
      have hmul := Nat.gcd_mul_lcm L M
      rw [h0, Nat.mul_zero] at hmul
      have : 0 < L * M := Nat.mul_pos hL.1 hM.1
      omega
    exact Nat.pos_of_ne_zero hne
  refine ⟨hlcm_pos, ?_, ?_⟩
  · rw [cmr_carry_free_strip hB π n a h ha hh hcf (Nat.lcm L M)]
    rw [← wordPerm_iter B hBpos π n (Nat.lcm L M) h hh]
    have hdL : L ∣ Nat.lcm L M := Nat.dvd_lcm_left L M
    have hdM : M ∣ Nat.lcm L M := Nat.dvd_lcm_right L M
    have h1 : iter (tau B π) (Nat.lcm L M) a = a := by
      rw [iter_mod_period (tau B π) a L hL.1 hL.2.1 (Nat.lcm L M),
          Nat.mod_eq_zero_of_dvd hdL, iter_zero]
    have h2 : iter (wordPerm B π n) (Nat.lcm L M) h = h := by
      rw [iter_mod_period (wordPerm B π n) h M hM.1 hM.2.1 (Nat.lcm L M),
          Nat.mod_eq_zero_of_dvd hdM, iter_zero]
    rw [h1, h2]
  · intro t ht1 ht2 heq
    rw [cmr_carry_free_strip hB π n a h ha hh hcf t] at heq
    rw [← wordPerm_iter B hBpos π n t h hh] at heq
    have hlt_t : iter (tau B π) t a < B := tau_iter_lt B hBpos π t a ha
    have hmod_eq : iter (tau B π) t a = a := by
      have h1 := congrArg (· % B) heq
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_t,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha] at h1
      exact h1
    have hdiv_eq : iter (wordPerm B π n) t h = h := by
      have h1 := congrArg (· / B) heq
      rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hlt_t, Nat.zero_add,
          Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt ha, Nat.zero_add] at h1
      exact h1
    have hdL : L ∣ t := period_dvd_of_iter_eq hL hmod_eq
    have hdM : M ∣ t := period_dvd_of_iter_eq hM hdiv_eq
    have hd : Nat.lcm L M ∣ t := Nat.lcm_dvd hdL hdM
    have hle : Nat.lcm L M ≤ t := Nat.le_of_dvd ht1 hd
    omega

/-- Bit-level justification: `rotDigit d a` moves bit `i` of `a` to bit `(i + 1) mod d`. -/
theorem rotDigit_testBit_zero (d : Nat) (hd : 1 ≤ d) (a : Nat) (ha : a < 2 ^ d) :
    Nat.testBit (rotDigit d a) 0 = Nat.testBit a (d - 1) := by
  rw [rotDigit_eq_branch d hd a ha]
  have hpow := two_pow_eq_two_mul_pred d hd
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  split
  · rename_i hhi
    rw [Nat.div_eq_of_lt hhi]
    have hmod0 : (2 * a) % 2 = 0 := by omega
    simp [Nat.and_comm 1, Nat.and_one_is_mod, hmod0]
  · rename_i hhi
    have hdiv1 : a / 2 ^ (d - 1) = 1 := nat_div_eq_one (by omega) (by omega)
    rw [hdiv1]
    have hmod1 : (2 * a - 2 ^ d + 1) % 2 = 1 := by omega
    simp [Nat.and_comm 1, Nat.and_one_is_mod, hmod1]

theorem rotDigit_testBit_succ (d : Nat) (hd : 1 ≤ d) (a i : Nat)
    (ha : a < 2 ^ d) (hi : i + 1 < d) :
    Nat.testBit (rotDigit d a) (i + 1) = Nat.testBit a i := by
  rw [rotDigit_eq_branch d hd a ha]
  have hpow_d := two_pow_eq_two_mul_pred d hd
  have hpow_i : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  split
  · rename_i hhi
    rw [hpow_i, Nat.mul_div_mul_left a (2 ^ i) (by omega)]
  · rename_i hhi
    have hge : 2 ^ d ≤ 2 * a := by omega
    have hpos_i : 0 < 2 ^ (i + 1) := Nat.pow_pos (by omega)
    have h2dvd : 2 ^ (i + 2) ∣ 2 ^ d := Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨k, hk⟩ := h2dvd
    have hpow2 : 2 ^ (i + 2) = 2 * 2 ^ (i + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have heven_div : (2 * a - 2 ^ d + 1) / 2 ^ (i + 1) = (2 * a - 2 ^ d) / 2 ^ (i + 1) := by
      have hge2 : 2 ≤ 2 ^ (i + 1) := by
        have : 1 ≤ 2 ^ i := Nat.pow_pos (by omega)
        omega
      have h2a_even : (2 * a - 2 ^ d) % 2 = 0 := by omega
      have hmod_lt : (2 * a - 2 ^ d) % 2 ^ (i + 1) + 1 < 2 ^ (i + 1) := by
        have hmlt := Nat.mod_lt (2 * a - 2 ^ d) hpos_i
        have hmeven : ((2 * a - 2 ^ d) % 2 ^ (i + 1)) % 2 = 0 := by
          have := Nat.div_add_mod (2 * a - 2 ^ d) (2 ^ (i + 1))
          have h2q : (2 ^ (i + 1) * ((2 * a - 2 ^ d) / 2 ^ (i + 1))) % 2 = 0 := by
            rw [hpow_i, Nat.mul_assoc]; omega
          omega
        have hpeven : (2 ^ (i + 1)) % 2 = 0 := by rw [hpow_i]; omega
        omega
      have := Nat.div_add_mod (2 * a - 2 ^ d) (2 ^ (i + 1))
      have hrew : 2 * a - 2 ^ d + 1 =
          ((2 * a - 2 ^ d) % 2 ^ (i + 1) + 1) + 2 ^ (i + 1) * ((2 * a - 2 ^ d) / 2 ^ (i + 1)) := by
        omega
      rw [hrew, Nat.add_mul_div_left _ _ hpos_i, Nat.div_eq_of_lt hmod_lt, Nat.zero_add]
    rw [heven_div]
    have hkd : 2 ^ d = 2 ^ (i + 1) * (2 * k) := by rw [hk, hpow2]; ac_rfl
    have hsub_div : (2 * a - 2 ^ d) / 2 ^ (i + 1) + 2 * k = a / 2 ^ i := by
      have hadd : (2 * a - 2 ^ d) + 2 ^ (i + 1) * (2 * k) = 2 * a := by omega
      calc (2 * a - 2 ^ d) / 2 ^ (i + 1) + 2 * k
          = ((2 * a - 2 ^ d) + 2 ^ (i + 1) * (2 * k)) / 2 ^ (i + 1) :=
              (Nat.add_mul_div_left _ _ hpos_i).symm
        _ = (2 * a) / 2 ^ (i + 1) := by rw [hadd]
        _ = (2 * a) / (2 * 2 ^ i) := by rw [hpow_i]
        _ = a / 2 ^ i := Nat.mul_div_mul_left a (2 ^ i) (by omega)
    have hmod2 : ((2 * a - 2 ^ d) / 2 ^ (i + 1)) % 2 = (a / 2 ^ i) % 2 := by omega
    rw [Nat.and_comm 1, Nat.and_one_is_mod, Nat.and_comm 1, Nat.and_one_is_mod, hmod2]

/-- Native `BitVec (d * n)` Morton cyclic coordinate rotation. -/
def mortonRotBV (d : Nat) (hd : 1 ≤ d) (n : Nat) (z : BitVec (d * n)) : BitVec (d * n) :=
  BitVec.ofNat (d * n) (wordPerm (2 ^ d) (rotDigitPerm d hd) n z.toNat)

/-- Native `BitVec (d * n)` Morton cyclic coordinate rotation composed with modular `+ 1`. -/
def mortonRotIncBV (d : Nat) (hd : 1 ≤ d) (n : Nat) (z : BitVec (d * n)) : BitVec (d * n) :=
  mortonRotBV d hd n z + BitVec.ofNat (d * n) 1

theorem mortonRotIncBV_toNat (d : Nat) (hd : 1 ≤ d) (n : Nat) (z : BitVec (d * n)) :
    (mortonRotIncBV d hd n z).toNat = step (2 ^ d) (rotDigitPerm d hd) n z.toNat := by
  simp only [mortonRotIncBV, mortonRotBV, step]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.pow_mul]
  have hwp : wordPerm (2 ^ d) (rotDigitPerm d hd) n z.toNat < (2 ^ d) ^ n :=
    wordPerm_lt (2 ^ d) (Nat.pow_pos (by omega)) (rotDigitPerm d hd) n z.toNat
  rw [Nat.mod_eq_of_lt hwp]
  by_cases h1 : 1 < (2 ^ d) ^ n
  · rw [Nat.mod_eq_of_lt h1]
  · have hpow1 : (2 ^ d) ^ n = 1 := by
      have hpos : 0 < (2 ^ d) ^ n := Nat.pow_pos (Nat.pow_pos (by omega))
      omega
    rw [hpow1]
    simp

theorem mortonRotIncBV_iter_toNat (d : Nat) (hd : 1 ≤ d) (n t : Nat) (z : BitVec (d * n)) :
    (iter (mortonRotIncBV d hd n) t z).toNat =
      iter (step (2 ^ d) (rotDigitPerm d hd) n) t z.toNat := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [iter_succ, iter_succ, mortonRotIncBV_toNat, ih]

/-! ## Section 4: Infinite Theorem A — Infinite-Dimension d-D Morton Flag-Helix Theorem -/

theorem rotDigit_pow_two_sub_one (d : Nat) (hd : 1 ≤ d) (r : Nat) (hr : r < d) :
    rotDigit d (2 ^ r - 1) = 2 ^ (r + 1) - 2 := by
  have hpow_r : 2 ^ r ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt_half : 2 ^ r - 1 < 2 ^ (d - 1) := by
    have : 1 ≤ 2 ^ r := Nat.pow_pos (by omega); omega
  have hlt_d : 2 ^ r - 1 < 2 ^ d := by
    have : 2 ^ (d - 1) < 2 ^ d := Nat.pow_lt_pow_right (by omega) (by omega); omega
  rw [rotDigit_eq_branch d hd _ hlt_d]
  simp only [hlt_half, ↓reduceIte]
  rw [Nat.pow_succ, Nat.mul_comm]
  have : 1 ≤ 2 ^ r := Nat.pow_pos (by omega)
  omega

/-- Symbolic orbit of `0` under `tau (2^d) (rotDigitPerm d)`:
    for all `0 ≤ r ≤ d`, `τ^r(0) = 2^r - 1`. -/
theorem rotDigit_tau_iter (d : Nat) (hd : 1 ≤ d) :
    ∀ r, r ≤ d → iter (tau (2 ^ d) (rotDigitPerm d hd)) r 0 = 2 ^ r - 1 := by
  intro r hr
  induction r with
  | zero => simp
  | succ r ih =>
    have hr_lt : r < d := by omega
    rw [iter_succ, ih (by omega), tau]
    simp only [rotDigitPerm]
    rw [rotDigit_pow_two_sub_one d hd r hr_lt]
    have hge2 : 2 ≤ 2 ^ (r + 1) := by
      have : 1 ≤ 2 ^ r := Nat.pow_pos (by omega)
      rw [Nat.pow_succ]; omega
    have hlt : 2 ^ (r + 1) - 2 + 1 < 2 ^ d := by
      have hle : 2 ^ (r + 1) ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

/-- `rotDigit d (2^d - 1) = 2^d - 1` (all-ones digit is fixed by rotation). -/
theorem rotDigit_all_ones (d : Nat) (hd : 1 ≤ d) :
    rotDigit d (2 ^ d - 1) = 2 ^ d - 1 := by
  have hpos : 1 ≤ 2 ^ d := Nat.pow_pos (by omega)
  have hlt : 2 ^ d - 1 < 2 ^ d := by omega
  rw [rotDigit_eq_branch d hd _ hlt]
  have hpow := two_pow_eq_two_mul_pred d hd
  have hnot : ¬ (2 ^ d - 1 < 2 ^ (d - 1)) := by
    have : 1 ≤ 2 ^ (d - 1) := Nat.pow_pos (by omega); omega
  simp only [hnot, ↓reduceIte]; omega

/-- **Symbolic Carry-Cycle Certificate for ALL dimensions `d ≥ 1`:**
    `rotDigitPerm d` has exact carry-cycle length `L* = d + 1`. -/
theorem rotDigitPerm_carry_cert (d : Nat) (hd : 1 ≤ d) :
    CarryCycleCert (2 ^ d) (rotDigitPerm d hd) (d + 1) where
  hL := by omega
  h_no_carry := by
    intro r hr
    have hr_lt : r < d := by omega
    rw [rotDigit_tau_iter d hd r (by omega)]
    simp only [rotDigitPerm]
    rw [rotDigit_pow_two_sub_one d hd r hr_lt]
    have hle : 2 ^ (r + 1) ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 2 ≤ 2 ^ (r + 1) := by
      have : 1 ≤ 2 ^ r := Nat.pow_pos (by omega); rw [Nat.pow_succ]; omega
    omega
  h_carry := by
    have hsub : d + 1 - 1 = d := by omega
    rw [hsub, rotDigit_tau_iter d hd d (Nat.le_refl d)]
    exact rotDigit_all_ones d hd

/-- Exact closed form of `iter (rotDigit d) k a` for `0 ≤ k ≤ d` and `a < 2^d`:
    `iter (rotDigit d) k a = (a % 2^(d - k)) * 2^k + a / 2^(d - k)`. -/
theorem rotDigit_iter_formula (d : Nat) (hd : 1 ≤ d) (a : Nat) (ha : a < 2 ^ d) :
    ∀ k, k ≤ d →
      iter (rotDigit d) k a = (a % 2 ^ (d - k)) * 2 ^ k + a / 2 ^ (d - k) := by
  intro k hk
  induction k with
  | zero =>
    simp only [iter_zero, Nat.sub_zero, Nat.pow_zero, Nat.mul_one]
    rw [Nat.mod_eq_of_lt ha, Nat.div_eq_of_lt ha, Nat.add_zero]
  | succ k ih =>
    have hk_lt : k < d := by omega
    have hiter_lt : iter (rotDigit d) k a < 2 ^ d := by
      have := ((rotDigitPerm d hd).pow k).h_lt a ha
      rw [DigitPerm.pow_toFun_eq_iter] at this
      exact this
    rw [iter_succ, rotDigit_eq_branch d hd _ hiter_lt, ih (by omega)]
    let m := d - (k + 1)
    have hdk : d - k = m + 1 := by omega
    have hdm : m + k = d - 1 := by omega
    have hpow_dk : 2 ^ (d - k) = 2 ^ m * 2 := by rw [hdk, Nat.pow_succ]
    have hpow_d1 : 2 ^ (d - 1) = 2 ^ m * 2 ^ k := by rw [← hdm, Nat.pow_add]
    have hpow_d := two_pow_eq_two_mul_pred d hd
    have hpos_m : 0 < 2 ^ m := Nat.pow_pos (by omega)
    have hdiv_lt : a / 2 ^ (d - k) < 2 ^ k := by
      have hmul_eq : 2 ^ (d - k) * 2 ^ k = 2 ^ d := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      exact Nat.div_lt_of_lt_mul (by rw [hmul_eq]; exact ha)
    have hq_div : a / 2 ^ m = 2 * (a / 2 ^ (d - k)) + (a % 2 ^ (d - k)) / 2 ^ m := by
      have h1 := Nat.div_add_mod a (2 ^ (d - k))
      have h2 := Nat.div_add_mod (a % 2 ^ (d - k)) (2 ^ m)
      have hmul_assoc : 2 ^ m * (2 * (a / 2 ^ (d - k))) = 2 ^ (d - k) * (a / 2 ^ (d - k)) := by
        rw [hpow_dk]; ac_rfl
      have hrew : a = (a % 2 ^ (d - k)) % 2 ^ m +
          2 ^ m * (2 * (a / 2 ^ (d - k)) + (a % 2 ^ (d - k)) / 2 ^ m) := by
        rw [Nat.mul_add, hmul_assoc]; omega
      calc a / 2 ^ m
          = ((a % 2 ^ (d - k)) % 2 ^ m +
              2 ^ m * (2 * (a / 2 ^ (d - k)) + (a % 2 ^ (d - k)) / 2 ^ m)) / 2 ^ m := by rw [← hrew]
        _ = 2 * (a / 2 ^ (d - k)) + (a % 2 ^ (d - k)) / 2 ^ m := by
              rw [Nat.add_mul_div_left _ _ hpos_m, Nat.div_eq_of_lt (Nat.mod_lt _ hpos_m), Nat.zero_add]
    have hrem_mod : a % 2 ^ m = (a % 2 ^ (d - k)) % 2 ^ m := by
      have hdvd : 2 ^ m ∣ 2 ^ (d - k) := Nat.pow_dvd_pow 2 (by omega)
      exact (Nat.mod_mod_of_dvd a hdvd).symm
    have hmod_dk_lt : a % 2 ^ (d - k) < 2 * 2 ^ m := by
      calc a % 2 ^ (d - k) < 2 ^ (d - k) := Nat.mod_lt a (Nat.pow_pos (by omega))
        _ = 2 ^ m * 2 := hpow_dk
        _ = 2 * 2 ^ m := Nat.mul_comm _ _
    change (if a % 2 ^ (d - k) * 2 ^ k + a / 2 ^ (d - k) < 2 ^ (d - 1) then
        2 * (a % 2 ^ (d - k) * 2 ^ k + a / 2 ^ (d - k))
      else 2 * (a % 2 ^ (d - k) * 2 ^ k + a / 2 ^ (d - k)) - 2 ^ d + 1) =
      a % 2 ^ m * 2 ^ (k + 1) + a / 2 ^ m
    by_cases hbit : a % 2 ^ (d - k) < 2 ^ m
    · have htop0 : (a % 2 ^ (d - k)) / 2 ^ m = 0 := Nat.div_eq_of_lt hbit
      have hcond : (a % 2 ^ (d - k)) * 2 ^ k + a / 2 ^ (d - k) < 2 ^ (d - 1) := by
        rw [hpow_d1]
        have hle : (a % 2 ^ (d - k) + 1) * 2 ^ k ≤ 2 ^ m * 2 ^ k :=
          Nat.mul_le_mul_right (2 ^ k) hbit
        rw [Nat.add_mul, Nat.one_mul] at hle
        omega
      simp only [hcond, ↓reduceIte]
      rw [hq_div, htop0, Nat.add_zero, hrem_mod, Nat.mod_eq_of_lt hbit, Nat.pow_succ]
      rw [Nat.mul_add]; congr 1; ac_rfl
    · have htop1 : (a % 2 ^ (d - k)) / 2 ^ m = 1 := nat_div_eq_one (by omega) hmod_dk_lt
      have hsub_mod : a % 2 ^ m = a % 2 ^ (d - k) - 2 ^ m := by
        rw [hrem_mod]
        exact nat_mod_eq_sub (by omega) hmod_dk_lt
      have hcond : ¬ ((a % 2 ^ (d - k)) * 2 ^ k + a / 2 ^ (d - k) < 2 ^ (d - 1)) := by
        rw [hpow_d1]
        have hge : 2 ^ m * 2 ^ k ≤ (a % 2 ^ (d - k)) * 2 ^ k :=
          Nat.mul_le_mul_right (2 ^ k) (by omega)
        omega
      simp only [hcond, ↓reduceIte]
      rw [hq_div, htop1, hsub_mod, Nat.pow_succ]
      have hmul_sub : (a % 2 ^ (d - k) - 2 ^ m) * (2 ^ k * 2) =
          2 * ((a % 2 ^ (d - k)) * 2 ^ k) - 2 ^ d := by
        have hd_eq : 2 ^ d = 2 ^ m * (2 ^ k * 2) := by
          rw [hpow_d, hpow_d1]; ac_rfl
        rw [Nat.sub_mul, ← hd_eq]
        congr 1; ac_rfl
      have hge_d : 2 ^ d ≤ 2 * ((a % 2 ^ (d - k)) * 2 ^ k) := by
        rw [hpow_d, hpow_d1]
        have hle : 2 ^ m * 2 ^ k ≤ (a % 2 ^ (d - k)) * 2 ^ k :=
          Nat.mul_le_mul_right (2 ^ k) (by omega)
        omega
      rw [hmul_sub, Nat.mul_add]
      omega

/-- Exact order law: `d` cyclic rotations restore any `d`-bit digit. -/
theorem rotDigit_iter_d (d : Nat) (hd : 1 ≤ d) (a : Nat) (ha : a < 2 ^ d) :
    iter (rotDigit d) d a = a := by
  rw [rotDigit_iter_formula d hd a ha d (Nat.le_refl d)]
  simp only [Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.div_one, Nat.zero_add]

/-- **Renormalization Fixed-Point Law (`∀ d ≥ 1`):**
    `rotDigitPerm d` raised to `L* = d + 1` equals `rotDigitPerm d` itself! -/
theorem rotDigitPerm_renorm_fixed (d : Nat) (hd : 1 ≤ d) (a : Nat) (ha : a < 2 ^ d) :
    ((rotDigitPerm d hd).pow (d + 1)).toFun a = (rotDigitPerm d hd).toFun a := by
  rw [DigitPerm.pow_toFun_eq_iter, iter_succ]
  simp only [rotDigitPerm]
  rw [rotDigit_iter_d d hd a ha]

/-- **Symbolic 1-State Renormalization Automaton for ALL dimensions `d ≥ 1`:** -/
def mortonRotAutomaton (d : Nat) (hd : 1 ≤ d) : RenormAutomaton (2 ^ d) 1 where
  perm := fun _ => rotDigitPerm d hd
  len := fun _ => d + 1
  next := fun s => s
  cert := fun _ => rotDigitPerm_carry_cert d hd
  closure := fun _ a ha => rotDigitPerm_renorm_fixed d hd a ha

theorem mortonRotAutomaton_orbitProd (d : Nat) (hd : 1 ≤ d) (n : Nat) :
    (mortonRotAutomaton d hd).orbitProd ⟨0, by omega⟩ n = (d + 1) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [RenormAutomaton.orbitProd, mortonRotAutomaton] at ih ⊢
    rw [ih, Nat.pow_succ, Nat.mul_comm]

/-- **INFINITE THEOREM A1 (Exact Period `(d + 1)^n` for ALL `d ≥ 1`, `n ≥ 0`):**
    For EVERY dimension `d ≥ 1` and EVERY precision `n ≥ 0`, `step (2^d) (rotDigitPerm d) n`
    has exact minimal period `(d + 1)^n` at `0`. -/
theorem mortonRot_exact_period_all_d_n (d : Nat) (hd : 1 ≤ d) (n : Nat) :
    HasExactPeriod (step (2 ^ d) (rotDigitPerm d hd) n) 0 ((d + 1) ^ n) := by
  have hB : 2 ≤ 2 ^ d := by
    have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
    simpa using this
  have h := cmr_automaton_lift hB (mortonRotAutomaton d hd) n ⟨0, by omega⟩
  rw [mortonRotAutomaton_orbitProd] at h
  exact h

/-- **INFINITE THEOREM A1 (Native `BitVec (d * n)` Formulation):**
    Lifted directly to native Lean `BitVec (d * n)` arithmetic `mortonRotBV d n z + 1`. -/
theorem mortonRotIncBV_exact_period_all_d_n (d : Nat) (hd : 1 ≤ d) (n : Nat) :
    HasExactPeriod (mortonRotIncBV d hd n) (BitVec.ofNat (d * n) 0) ((d + 1) ^ n) := by
  have hnat := mortonRot_exact_period_all_d_n d hd n
  refine ⟨hnat.1, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [mortonRotIncBV_iter_toNat, BitVec.toNat_ofNat]
    simpa using hnat.2.1
  · intro t ht1 ht2 heq
    have htn := congrArg BitVec.toNat heq
    rw [mortonRotIncBV_iter_toNat, BitVec.toNat_ofNat] at htn
    simp only [Nat.zero_mod] at htn
    exact hnat.2.2 t ht1 ht2 htn

/-- Base-`(d+1)` Flag-Helix encoder with initial rotation phase `phi`:
    encodes `t < (d + 1)^n` into the exact `n`-digit Morton word visited at time `t`. -/
def flagHelixEncodePhase (d : Nat) (hd : 1 ≤ d) (phi : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, t =>
    let r := t % (d + 1)
    iter (rotDigit d) phi (2 ^ r - 1) +
      2 ^ d * flagHelixEncodePhase d hd (phi + r) n (t / (d + 1))

/-- Canonical Flag-Helix encoder starting at phase `0`. -/
def flagHelixEncode (d : Nat) (hd : 1 ≤ d) (n t : Nat) : Nat :=
  flagHelixEncodePhase d hd 0 n t

theorem wordPerm_rotDigit_flagHelix (d : Nat) (hd : 1 ≤ d) (n : Nat) :
    ∀ k phi t,
      wordPerm (2 ^ d) ((rotDigitPerm d hd).pow k) n (flagHelixEncodePhase d hd phi n t) =
        flagHelixEncodePhase d hd (k + phi) n t := by
  have hBpos : 0 < 2 ^ d := Nat.pow_pos (by omega)
  induction n with
  | zero =>
    intro _ _ _; rfl
  | succ n ih =>
    intro k phi t
    simp only [flagHelixEncodePhase]
    have hrm_lt : 2 ^ (t % (d + 1)) - 1 < 2 ^ d := by
      have hle : t % (d + 1) ≤ d := by
        have := Nat.mod_lt t (by omega : 0 < d + 1); omega
      have hpow : 2 ^ (t % (d + 1)) ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hle
      have hpos : 1 ≤ 2 ^ (t % (d + 1)) := Nat.pow_pos (by omega)
      omega
    have hdig_lt : iter (rotDigit d) phi (2 ^ (t % (d + 1)) - 1) < 2 ^ d := by
      have := ((rotDigitPerm d hd).pow phi).h_lt _ hrm_lt
      rw [DigitPerm.pow_toFun_eq_iter] at this
      exact this
    rw [wordPerm_add_mul (2 ^ d) hBpos _ n _ _ hdig_lt]
    rw [DigitPerm.pow_toFun_eq_iter]
    rw [ih k (phi + t % (d + 1)) (t / (d + 1)), Nat.add_assoc]
    congr 1
    exact (iter_add (rotDigit d) k phi (2 ^ (t % (d + 1)) - 1)).symm

/-- **INFINITE THEOREM A2 (Exact Closed-Form Flag-Helix Orbit Law — `∀ d ≥ 1, ∀ n ≥ 0, ∀ t`):**
    For EVERY dimension `d ≥ 1`, EVERY precision `n ≥ 0`, and EVERY time `t : Nat`,
    the `t`-th iterate from `0` is given in closed form by `flagHelixEncode d n t`! -/
theorem mortonRot_exact_flagHelix (d : Nat) (hd : 1 ≤ d) (n : Nat) :
    ∀ t, iter (step (2 ^ d) (rotDigitPerm d hd) n) t 0 = flagHelixEncode d hd n t := by
  have hB : 2 ≤ 2 ^ d := by
    have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
    simpa using this
  have hBpos : 0 < 2 ^ d := by omega
  induction n with
  | zero =>
    intro t
    induction t with
    | zero => rfl
    | succ t _ => simp [iter_succ, step, wordPerm, flagHelixEncode, flagHelixEncodePhase]
  | succ n ih =>
    intro t
    have hgen := cmr_fiber_general hB (rotDigitPerm_carry_cert d hd) n 0 (Nat.pow_pos hBpos) t
    rw [Nat.mul_zero] at hgen
    rw [hgen]
    have hstep_congr :
        iter (step (2 ^ d) ((rotDigitPerm d hd).pow (d + 1)) n) (t / (d + 1)) 0 =
        iter (step (2 ^ d) (rotDigitPerm d hd) n) (t / (d + 1)) 0 := by
      exact (iter_congr (P := fun _ => True) (fun _ _ => trivial)
        (fun y _ => step_congr (2 ^ d) hBpos (rotDigitPerm_renorm_fixed d hd) n y)
        (t / (d + 1)) 0 trivial).1
    rw [hstep_congr, ih (t / (d + 1))]
    simp only [flagHelixEncode, flagHelixEncodePhase]
    have hrm_le : t % (d + 1) ≤ d := by
      have := Nat.mod_lt t (by omega : 0 < d + 1); omega
    rw [rotDigit_tau_iter d hd (t % (d + 1)) hrm_le, iter_zero]
    rw [wordPerm_rotDigit_flagHelix d hd n (t % (d + 1)) 0 (t / (d + 1))]
    simp only [Nat.add_zero, Nat.zero_add]

/-- Exact inverse decoder from a Flag-Helix word `z` back to its unique base-`(d+1)` time index `t`. -/
def flagHelixDecodePhase (d : Nat) (hd : 1 ≤ d) (phi : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, z =>
    let dig := z % (2 ^ d)
    let unrot := iter (rotDigitInv d) phi dig
    let r := Nat.log2 (unrot + 1)
    r + (d + 1) * flagHelixDecodePhase d hd (phi + r) n (z / (2 ^ d))

def flagHelixDecode (d : Nat) (hd : 1 ≤ d) (n z : Nat) : Nat :=
  flagHelixDecodePhase d hd 0 n z

theorem rotDigitInv_iter_rotDigit (d : Nat) (hd : 1 ≤ d) (phi a : Nat) (ha : a < 2 ^ d) :
    iter (rotDigitInv d) phi (iter (rotDigit d) phi a) = a := by
  induction phi with
  | zero => rfl
  | succ phi ih =>
    rw [iter_succ_inner (rotDigitInv d), iter_succ (rotDigit d)]
    have hlt : iter (rotDigit d) phi a < 2 ^ d := by
      have := ((rotDigitPerm d hd).pow phi).h_lt a ha
      rw [DigitPerm.pow_toFun_eq_iter] at this
      exact this
    rw [rotDigit_left_inv d hd _ hlt, ih]

theorem rotDigit_iter_rotDigitInv (d : Nat) (hd : 1 ≤ d) (phi a : Nat) (ha : a < 2 ^ d) :
    iter (rotDigit d) phi (iter (rotDigitInv d) phi a) = a := by
  induction phi with
  | zero => rfl
  | succ phi ih =>
    rw [iter_succ_inner (rotDigit d), iter_succ (rotDigitInv d)]
    have hlt : iter (rotDigitInv d) phi a < 2 ^ d := by
      clear ih
      induction phi with
      | zero => exact ha
      | succ k ihk => rw [iter_succ]; exact rotDigitInv_lt d hd _ ihk
    rw [rotDigit_right_inv d hd _ hlt, ih]

theorem pow_two_land_pred (r : Nat) : (2 ^ r &&& (2 ^ r - 1)) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hi : i < r
  · rw [Nat.testBit_two_pow_of_ne (by omega), Bool.false_and]
  · have hlt : 2 ^ r - 1 < 2 ^ i := by
      have hle : 2 ^ r ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      have hpos : 1 ≤ 2 ^ r := Nat.pow_pos (by omega)
      omega
    rw [Nat.testBit_lt_two_pow hlt, Bool.and_false]

theorem log2_two_pow (r : Nat) : Nat.log2 (2 ^ r) = r := by
  have h1 : 2 ^ r ≤ 2 ^ r := Nat.le_refl _
  have h2 : 2 ^ r < 2 ^ (r + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpos : 2 ^ r ≠ 0 := by have := Nat.pow_pos (a := 2) (n := r) (by omega); omega
  have hle : r ≤ Nat.log2 (2 ^ r) := (Nat.le_log2 hpos).2 h1
  have hlt : Nat.log2 (2 ^ r) < r + 1 := (Nat.log2_lt hpos).2 h2
  omega

theorem eq_pow_two_sub_one_of_land_zero (u : Nat) (h : ((u + 1) &&& u) = 0) :
    u = 2 ^ (Nat.log2 (u + 1)) - 1 := by
  let r := Nat.log2 (u + 1)
  have hpos : u + 1 ≠ 0 := by omega
  have hge : 2 ^ r ≤ u + 1 := Nat.log2_self_le hpos
  have hlt : u + 1 < 2 ^ (r + 1) := (Nat.log2_lt hpos).1 (Nat.lt_succ_self r)
  by_cases heq : u = 2 ^ r - 1
  · exact heq
  · exfalso
    have hgt : 2 ^ r < u + 1 := by omega
    have hpow2 : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ, Nat.mul_comm]
    have hdiv1 : (u + 1) / 2 ^ r = 1 := nat_div_eq_one hge (by omega)
    have hdiv2 : u / 2 ^ r = 1 := nat_div_eq_one (by omega) (by omega)
    have hb1 : Nat.testBit (u + 1) r = true := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv1]; rfl
    have hb2 : Nat.testBit u r = true := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv2]; rfl
    have hboth := congrArg (fun x => Nat.testBit x r) h
    rw [Nat.testBit_and, hb1, hb2, Nat.zero_testBit] at hboth
    simp at hboth

/-- **INFINITE THEOREM A3 (Flag-Helix Exact Set Characterization — Soundness & Completeness):** -/
theorem flagHelix_sound (d : Nat) (hd : 1 ≤ d) (n : Nat) :
    ∀ phi t, isFlagHelixPhase d hd phi n (flagHelixEncodePhase d hd phi n t) = true := by
  have hBpos : 0 < 2 ^ d := Nat.pow_pos (by omega)
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro phi t
    let r := t % (d + 1)
    have hr_le : r ≤ d := by have := Nat.mod_lt t (by omega : 0 < d + 1); omega
    have hrm_lt : 2 ^ r - 1 < 2 ^ d := by
      have hle : 2 ^ r ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hr_le
      have hpos : 1 ≤ 2 ^ r := Nat.pow_pos (by omega); omega
    have hdig_lt : iter (rotDigit d) phi (2 ^ r - 1) < 2 ^ d := by
      have := ((rotDigitPerm d hd).pow phi).h_lt _ hrm_lt
      rw [DigitPerm.pow_toFun_eq_iter] at this; exact this
    have hmod : flagHelixEncodePhase d hd phi (n + 1) t % 2 ^ d =
        iter (rotDigit d) phi (2 ^ r - 1) := by
      simp only [flagHelixEncodePhase]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdig_lt]
    have hdiv : flagHelixEncodePhase d hd phi (n + 1) t / 2 ^ d =
        flagHelixEncodePhase d hd (phi + r) n (t / (d + 1)) := by
      simp only [flagHelixEncodePhase]
      rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hdig_lt, Nat.zero_add]
    have hunrot : iter (rotDigitInv d) phi (flagHelixEncodePhase d hd phi (n + 1) t % 2 ^ d) =
        2 ^ r - 1 := by
      rw [hmod, rotDigitInv_iter_rotDigit d hd phi _ hrm_lt]
    have hadd1 : 2 ^ r - 1 + 1 = 2 ^ r := by
      have : 1 ≤ 2 ^ r := Nat.pow_pos (by omega); omega
    simp only [isFlagHelixPhase, hunrot, hdiv, hadd1, pow_two_land_pred r,
               beq_self_eq_true, ↓reduceIte, log2_two_pow]
    exact ih (phi + r) (t / (d + 1))

theorem flagHelix_complete (d : Nat) (hd : 1 ≤ d) (n : Nat) :
    ∀ phi z, z < (2 ^ d) ^ n → isFlagHelixPhase d hd phi n z = true →
      flagHelixDecodePhase d hd phi n z < (d + 1) ^ n ∧
      flagHelixEncodePhase d hd phi n (flagHelixDecodePhase d hd phi n z) = z := by
  have hBpos : 0 < 2 ^ d := Nat.pow_pos (by omega)
  induction n with
  | zero =>
    intro phi z hz _
    simp only [Nat.pow_zero] at hz
    simp only [flagHelixDecodePhase, flagHelixEncodePhase, Nat.pow_zero]
    omega
  | succ n ih =>
    intro phi z hz hflag
    simp only [isFlagHelixPhase] at hflag
    let dig := z % 2 ^ d
    let unrot := iter (rotDigitInv d) phi dig
    by_cases hland : ((unrot + 1) &&& unrot) = 0
    · have hbeq : (((unrot + 1) &&& unrot) == 0) = true := beq_iff_eq.mpr hland
      change (if (((unrot + 1) &&& unrot) == 0) = true then
          isFlagHelixPhase d hd (phi + Nat.log2 (unrot + 1)) n (z / 2 ^ d)
        else false) = true at hflag
      simp only [hbeq, ↓reduceIte] at hflag
      let r := Nat.log2 (unrot + 1)
      have hunrot_eq : unrot = 2 ^ r - 1 := eq_pow_two_sub_one_of_land_zero unrot hland
      have hdig_lt : dig < 2 ^ d := Nat.mod_lt z hBpos
      have hunrot_lt : iter (rotDigitInv d) phi dig < 2 ^ d := by
        clear hflag hland hbeq hunrot_eq
        induction phi with
        | zero => exact hdig_lt
        | succ k ihk => rw [iter_succ]; exact rotDigitInv_lt d hd _ ihk
      have hr_lt : r < d + 1 := by
        have hpow_le : 2 ^ r ≤ 2 ^ d := by
          have : 1 ≤ 2 ^ r := Nat.pow_pos (by omega)
          have : unrot < 2 ^ d := hunrot_lt
          omega
        by_cases hle : r ≤ d
        · omega
        · exfalso
          have hgt' : d + 1 ≤ r := by omega
          have h1 : 2 ^ (d + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hgt'
          have h2 : 2 ^ d < 2 ^ (d + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
          omega
      have hzdiv_lt : z / 2 ^ d < (2 ^ d) ^ n := by
        rw [Nat.pow_succ, Nat.mul_comm] at hz
        exact Nat.div_lt_of_lt_mul hz
      obtain ⟨hdec_lt, henc_eq⟩ := ih (phi + r) (z / 2 ^ d) hzdiv_lt hflag
      simp only [flagHelixDecodePhase]
      let t_hi := flagHelixDecodePhase d hd (phi + r) n (z / 2 ^ d)
      refine ⟨?_, ?_⟩
      · rw [Nat.pow_succ, Nat.mul_comm ((d + 1) ^ n) (d + 1)]
        have hle : (d + 1) * (t_hi + 1) ≤ (d + 1) * (d + 1) ^ n :=
          Nat.mul_le_mul_left (d + 1) hdec_lt
        rw [Nat.mul_add, Nat.mul_one] at hle
        change r + (d + 1) * t_hi < (d + 1) * (d + 1) ^ n
        omega
      · simp only [flagHelixEncodePhase]
        have hmod_t : (r + (d + 1) * t_hi) % (d + 1) = r := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr_lt]
        have hdiv_t : (r + (d + 1) * t_hi) / (d + 1) = t_hi := by
          rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hr_lt, Nat.zero_add]
        rw [hmod_t, hdiv_t, ← hunrot_eq, rotDigit_iter_rotDigitInv d hd phi dig hdig_lt, henc_eq]
        have := Nat.div_add_mod z (2 ^ d)
        omega
    · have hbeq : (((unrot + 1) &&& unrot) == 0) = false := beq_false_of_ne hland
      change (if (((unrot + 1) &&& unrot) == 0) = true then
          isFlagHelixPhase d hd (phi + Nat.log2 (unrot + 1)) n (z / 2 ^ d)
        else false) = true at hflag
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hflag

/-- Exact characterization theorem: `z < (2^d)^n` lies on the giant orbit of `0` under
    `step (2^d) (rotDigitPerm d) n` **if and only if** `isFlagHelix d hd n z = true`! -/
theorem mortonRot_orbit_iff_flagHelix (d : Nat) (hd : 1 ≤ d) (n z : Nat) (hz : z < (2 ^ d) ^ n) :
    (∃ t, t < (d + 1) ^ n ∧ iter (step (2 ^ d) (rotDigitPerm d hd) n) t 0 = z) ↔
      isFlagHelix d hd n z = true := by
  constructor
  · rintro ⟨t, _, rfl⟩
    rw [mortonRot_exact_flagHelix d hd n t]
    exact flagHelix_sound d hd n 0 t
  · intro hflag
    obtain ⟨hlt, heq⟩ := flagHelix_complete d hd n 0 z hz hflag
    refine ⟨flagHelixDecode d hd n z, hlt, ?_⟩
    rw [mortonRot_exact_flagHelix d hd n]
    exact heq

/-! ## Section 5: Infinite Theorem B — Complete Exact Orbit Classification & Cycle Spectrum of 2D Morton Swap + 1 -/

/-- General injectivity transport for `HasExactPeriod`: stepping forward by an injective invariant
    map preserves exact minimal periods. -/
theorem hasExactPeriod_step_iff {α : Type} {f : α → α} {P_inv : α → Prop}
    (hf : ∀ x, P_inv x → P_inv (f x))
    (hinj : ∀ x y, P_inv x → P_inv y → f x = f y → x = y)
    {x : α} (hx : P_inv x) (P : Nat) :
    HasExactPeriod f x P ↔ HasExactPeriod f (f x) P := by
  have hinv_iter : ∀ k, P_inv (iter f k x) := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih => exact hf _ ih
  constructor
  · rintro ⟨hP, hfix, hmin⟩
    refine ⟨hP, ?_, ?_⟩
    · rw [← iter_succ_inner, iter_succ, hfix]
    · intro t ht1 ht2 heq
      rw [← iter_succ_inner, iter_succ] at heq
      exact hmin t ht1 ht2 (hinj _ _ (hinv_iter t) hx heq)
  · rintro ⟨hP, hfix, hmin⟩
    refine ⟨hP, ?_, ?_⟩
    · rw [← iter_succ_inner, iter_succ] at hfix
      exact hinj _ _ (hinv_iter P) hx hfix
    · intro t ht1 ht2 heq
      apply hmin t ht1 ht2
      rw [← iter_succ_inner, iter_succ, heq]

/-- `step B π n` is injective on `{0, ..., B^n - 1}`. -/
theorem step_inj (B : Nat) (hB : 0 < B) (π : DigitPerm B) (n : Nat)
    {x y : Nat} (hx : x < B ^ n) (hy : y < B ^ n)
    (heq : step B π n x = step B π n y) : x = y := by
  simp only [step] at heq
  have hwx := wordPerm_lt B hB π n x
  have hwy := wordPerm_lt B hB π n y
  have hweq : wordPerm B π n x = wordPerm B π n y := by
    by_cases hxm : wordPerm B π n x + 1 = B ^ n
    · rw [hxm, Nat.mod_self] at heq
      by_cases hym : wordPerm B π n y + 1 = B ^ n
      · omega
      · have hlt : wordPerm B π n y + 1 < B ^ n := by omega
        rw [Nat.mod_eq_of_lt hlt] at heq; omega
    · have hltx : wordPerm B π n x + 1 < B ^ n := by omega
      rw [Nat.mod_eq_of_lt hltx] at heq
      by_cases hym : wordPerm B π n y + 1 = B ^ n
      · rw [hym, Nat.mod_self] at heq; omega
      · have hlty : wordPerm B π n y + 1 < B ^ n := by omega
        rw [Nat.mod_eq_of_lt hlty] at heq; omega
  exact wordPerm_inj B hB π n hx hy hweq

/-- **CMR General-Basepoint Period Lift:**
    For ANY `h < B^n` (not just `h = 0`), if `step B (π.pow L) n` has exact period `P` at `h`,
    then `step B π (n + 1)` has exact period `L * P` at `B * h`. -/
theorem cmr_exact_period_lift_any {B : Nat} (hB : 2 ≤ B) {π : DigitPerm B} {L n h P : Nat}
    (cert : CarryCycleCert B π L) (hh : h < B ^ n)
    (hP : HasExactPeriod (step B (π.pow L) n) h P) :
    HasExactPeriod (step B π (n + 1)) (B * h) (L * P) := by
  have hBpos : 0 < B := by omega
  refine ⟨Nat.mul_pos cert.hL hP.1, ?_, ?_⟩
  · rw [Nat.mul_comm L P, cmr_fiber_iter hB cert n h hh P, hP.2.1]
  · intro t ht1 ht2 heq
    rw [cmr_fiber_general hB cert n h hh t] at heq
    have hmod_lt : iter (tau B π) (t % L) 0 < B := tau_iter_lt B hBpos π (t % L) 0 hBpos
    have hrem0 : iter (tau B π) (t % L) 0 = 0 := by
      have h1 := congrArg (· % B) heq
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmod_lt, Nat.mul_mod_right] at h1
      exact h1
    have htmod : t % L = 0 := by
      by_cases h0 : t % L = 0
      · exact h0
      · exfalso
        exact cert.tau_pos_ne_zero hB (Nat.pos_of_ne_zero h0) (Nat.mod_lt t cert.hL) hrem0
    have hdiv_pos : 0 < t / L := by
      have hdm := Nat.div_add_mod t L
      rw [htmod, Nat.add_zero] at hdm
      by_cases hq : t / L = 0
      · rw [hq, Nat.mul_zero] at hdm; omega
      · exact Nat.pos_of_ne_zero hq
    have hdiv_lt : t / L < P := by
      have hdm := Nat.div_add_mod t L
      rw [htmod, Nat.add_zero] at hdm
      have hmul : L * (t / L) < L * P := by omega
      exact Nat.lt_of_mul_lt_mul_left hmul
    have hdiv_eq : wordPerm B (π.pow 0) n (iter (step B (π.pow L) n) (t / L) h) = h := by
      rw [htmod, iter_zero, Nat.zero_add] at heq
      have h1 := congrArg (· / B) heq
      rw [Nat.mul_div_cancel_left _ hBpos, Nat.mul_div_cancel_left _ hBpos] at h1
      exact h1
    rw [DigitPerm.pow] at hdiv_eq
    have hlt_iter : iter (step B (π.pow L) n) (t / L) h < B ^ n := by
      cases hq : t / L with
      | zero => omega
      | succ k' => exact step_lt B hBpos (π.pow L) n _
    rw [wordPerm_id B hBpos n _ hlt_iter] at hdiv_eq
    exact hP.2.2 (t / L) hdiv_pos hdiv_lt hdiv_eq

theorem swap2D_pow2 (a : Nat) (ha : a < 4) : (swap2D.pow 2).toFun a = a := by
  rw [DigitPerm.pow_toFun_eq_iter]
  exact rotDigit_iter_d 2 (by omega) a ha

theorem swap2D_pow3 (a : Nat) (ha : a < 4) : (swap2D.pow 3).toFun a = swap2D.toFun a :=
  rotDigitPerm_renorm_fixed 2 (by omega) a ha

theorem swap2D_word_involution (n h : Nat) (hh : h < 4 ^ n) :
    wordPerm 4 swap2D n (wordPerm 4 swap2D n h) = h := by
  rw [wordPerm_comp 4 (by omega)]
  calc wordPerm 4 (DigitPerm.comp swap2D swap2D) n h
      = wordPerm 4 (DigitPerm.id 4) n h := by
          apply wordPerm_congr 4 (by omega)
          intro a ha
          have h2 := swap2D_pow2 a ha
          simpa [DigitPerm.pow, DigitPerm.comp, DigitPerm.id] using h2
    _ = h := wordPerm_id 4 (by omega) n h hh

theorem allDiag2D_iff_wordPerm_eq (n : Nat) :
    ∀ h, h < 4 ^ n → (allDiag2D n h = true ↔ wordPerm 4 swap2D n h = h) := by
  induction n with
  | zero =>
    intro h hh
    simp only [Nat.pow_zero] at hh
    simp only [allDiag2D, wordPerm]
    exact ⟨fun _ => by omega, fun _ => trivial⟩
  | succ n ih =>
    intro h hh
    have hdiv_lt : h / 4 < 4 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm] at hh
      exact Nat.div_lt_of_lt_mul hh
    have hmod_lt : h % 4 < 4 := Nat.mod_lt h (by omega)
    have hdig_iff : (h % 4 == 0 || h % 4 == 3) = true ↔ swap2D.toFun (h % 4) = h % 4 := by
      have : h % 4 = 0 ∨ h % 4 = 1 ∨ h % 4 = 2 ∨ h % 4 = 3 := by omega
      rcases this with hm | hm | hm | hm <;> simp [hm, swap2D, rotDigitPerm, rotDigit]
    simp only [allDiag2D, Bool.and_eq_true, wordPerm]
    rw [hdig_iff, ih (h / 4) hdiv_lt]
    constructor
    · rintro ⟨hd, hhi⟩
      rw [hd, hhi]
      have := Nat.div_add_mod h 4
      omega
    · intro heq
      have hsw_lt : swap2D.toFun (h % 4) < 4 := swap2D.h_lt _ hmod_lt
      have hm : swap2D.toFun (h % 4) = h % 4 := by
        have h1 := congrArg (· % 4) heq
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsw_lt] at h1
        exact h1
      have hq : wordPerm 4 swap2D n (h / 4) = h / 4 := by
        have h1 := congrArg (· / 4) heq
        rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hsw_lt, Nat.zero_add] at h1
        exact h1
      exact ⟨hm, hq⟩

theorem wordPerm_swap2D_exact_period (n h : Nat) (hh : h < 4 ^ n) :
    HasExactPeriod (wordPerm 4 swap2D n) h (if allDiag2D n h then 1 else 2) := by
  by_cases hd : allDiag2D n h = true
  · simp only [hd, ↓reduceIte]
    have hfix := (allDiag2D_iff_wordPerm_eq n h hh).mp hd
    refine ⟨by omega, ?_, ?_⟩
    · simp [iter_succ, hfix]
    · intro t ht1 ht2; omega
  · have hdf : allDiag2D n h = false := by
      cases hx : allDiag2D n h with
      | false => rfl
      | true => exact absurd hx hd
    simp only [hdf, Bool.false_eq_true, ↓reduceIte]
    have hne : wordPerm 4 swap2D n h ≠ h := by
      intro heq
      exact hd ((allDiag2D_iff_wordPerm_eq n h hh).mpr heq)
    refine ⟨by omega, ?_, ?_⟩
    · simp only [iter_succ, iter_zero]
      exact swap2D_word_involution n h hh
    · intro t ht1 ht2
      have : t = 1 := by omega
      rw [this, iter_succ, iter_zero]
      exact hne

theorem tau_swap2D_two_fixed : tau 4 swap2D 2 = 2 := by decide

theorem tau_swap2D_two_iter (r : Nat) : iter (tau 4 swap2D) r 2 = 2 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [iter_succ, ih, tau_swap2D_two_fixed]

theorem shiftToFiber2D_lt (n a h : Nat) (hh : h < 4 ^ n) :
    shiftToFiber2D n a h < 4 ^ n := by
  simp only [shiftToFiber2D]
  split
  · exact hh
  · split
    · exact step_lt 4 (by omega) swap2D n h
    · exact Nat.mod_lt _ (Nat.pow_pos (by omega))

/-- **INFINITE THEOREM B1 (Complete Exact Orbit Classification for ALL `n` and ALL `z < 4^n`):**
    For EVERY precision `n : Nat` and EVERY state `z < 4^n`, `period2D n z` is the **EXACT**
    minimal period of `z` under 2D Morton swap `+ 1`. -/
theorem morton2D_exact_period_all_z (n : Nat) :
    ∀ z, z < 4 ^ n → HasExactPeriod (step 4 swap2D n) z (period2D n z) := by
  induction n with
  | zero =>
    intro z hz
    simp only [Nat.pow_zero] at hz
    have hz0 : z = 0 := by omega
    rw [hz0]
    exact step_zero_exact_period 4 swap2D
  | succ n ih =>
    intro z hz
    have hdiv_lt : z / 4 < 4 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm] at hz
      exact Nat.div_lt_of_lt_mul hz
    have hmod_lt : z % 4 < 4 := Nat.mod_lt z (by omega)
    have hz_split : z = z % 4 + 4 * (z / 4) := by
      have := Nat.div_add_mod z 4; omega
    have hcases : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
    have hstep_inj : ∀ x y, x < 4 ^ (n + 1) → y < 4 ^ (n + 1) →
        step 4 swap2D (n + 1) x = step 4 swap2D (n + 1) y → x = y :=
      fun _ _ hx hy => step_inj 4 (by omega) swap2D (n + 1) hx hy
    have hstep_pres : ∀ x, x < 4 ^ (n + 1) → step 4 swap2D (n + 1) x < 4 ^ (n + 1) :=
      fun _ _ => step_lt 4 (by omega) swap2D (n + 1) _
    generalize hq_eq : z / 4 = q at hdiv_lt hz_split
    rcases hcases with h0 | h1 | h2 | h3
    · -- Case `a = 0`: directly on the basepoint fiber `4 * q`!
      simp only [period2D, h0, hq_eq, shiftToFiber2D]
      simp only [show (0 == 2) = false by decide, Bool.false_eq_true, ↓reduceIte,
                 beq_self_eq_true]
      have hzeq : z = 4 * q := by omega
      rw [hzeq]
      have hih := ih q hdiv_lt
      have hcongr : HasExactPeriod (step 4 (swap2D.pow 3) n) q (period2D n q) := by
        refine hasExactPeriod_of_congr (P_inv := fun _ => True) (fun _ _ => trivial) ?_ trivial hih
        intro y _; exact (step_congr 4 (by omega) swap2D_pow3 n y).symm
      exact cmr_exact_period_lift_any (by omega) (rotDigitPerm_carry_cert 2 (by omega)) hdiv_lt hcongr
    · -- Case `a = 1`: 2 steps forward land at `4 * ((q + 1) % 4^n)`!
      simp only [period2D, h1, hq_eq, shiftToFiber2D]
      simp only [show (1 == 2) = false by decide, show (1 == 0) = false by decide,
                 show (1 == 3) = false by decide, Bool.false_eq_true, ↓reduceIte]
      have h1step : step 4 swap2D (n + 1) z = 3 + 4 * wordPerm 4 swap2D n q := by
        rw [hz_split, h1]
        rw [step_add_mul_no_carry 4 (by omega) swap2D n 1 q (by omega) (by decide)]
        rfl
      have h2step : step 4 swap2D (n + 1) (step 4 swap2D (n + 1) z) = 4 * ((q + 1) % 4 ^ n) := by
        rw [h1step]
        rw [step_add_mul_carry 4 (by omega) swap2D n 3 _ (by omega) (by decide)]
        congr 1
        simp only [step, swap2D_word_involution n q hdiv_lt]
      rw [hasExactPeriod_step_iff hstep_pres hstep_inj hz]
      rw [hasExactPeriod_step_iff hstep_pres hstep_inj (hstep_pres z hz)]
      rw [h2step]
      have hlt' : (q + 1) % 4 ^ n < 4 ^ n := Nat.mod_lt _ (Nat.pow_pos (by omega))
      have hih := ih _ hlt'
      have hcongr : HasExactPeriod (step 4 (swap2D.pow 3) n) ((q + 1) % 4 ^ n)
          (period2D n ((q + 1) % 4 ^ n)) := by
        refine hasExactPeriod_of_congr (P_inv := fun _ => True) (fun _ _ => trivial) ?_ trivial hih
        intro y _; exact (step_congr 4 (by omega) swap2D_pow3 n y).symm
      exact cmr_exact_period_lift_any (by omega) (rotDigitPerm_carry_cert 2 (by omega)) hlt' hcongr
    · -- Case `a = 2`: carry-free strip via CMR Theorem 8!
      simp only [period2D, h2, hq_eq, beq_self_eq_true, ↓reduceIte]
      rw [hz_split, h2]
      have hcf : ∀ r, swap2D.toFun (iter (tau 4 swap2D) r 2) < 4 - 1 := by
        intro r; rw [tau_swap2D_two_iter r]; decide
      have hL : HasExactPeriod (tau 4 swap2D) 2 1 := by
        refine ⟨by omega, ?_, ?_⟩
        · simp [iter_succ, tau_swap2D_two_fixed]
        · intro t ht1 ht2; omega
      have hM := wordPerm_swap2D_exact_period n q hdiv_lt
      have hlcm := cmr_carry_free_period (by omega) swap2D n 2 q 1
        (if allDiag2D n q then 1 else 2) (by omega) hdiv_lt hcf hL hM
      have h1lcm : Nat.lcm 1 (if allDiag2D n q then 1 else 2) =
          (if allDiag2D n q then 1 else 2) := Nat.lcm_one_left _
      rw [h1lcm] at hlcm
      exact hlcm
    · -- Case `a = 3`: 1 step forward lands at `4 * step 4 swap2D n q`!
      simp only [period2D, h3, hq_eq, shiftToFiber2D]
      simp only [show (3 == 2) = false by decide, show (3 == 0) = false by decide,
                 beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      have h1step : step 4 swap2D (n + 1) z = 4 * step 4 swap2D n q := by
        rw [hz_split, h3]
        exact step_add_mul_carry 4 (by omega) swap2D n 3 q (by omega) (by decide)
      rw [hasExactPeriod_step_iff hstep_pres hstep_inj hz, h1step]
      have hlt' : step 4 swap2D n q < 4 ^ n := step_lt 4 (by omega) swap2D n _
      have hih := ih _ hlt'
      have hcongr : HasExactPeriod (step 4 (swap2D.pow 3) n) (step 4 swap2D n q)
          (period2D n (step 4 swap2D n q)) := by
        refine hasExactPeriod_of_congr (P_inv := fun _ => True) (fun _ _ => trivial) ?_ trivial hih
        intro y _; exact (step_congr 4 (by omega) swap2D_pow3 n y).symm
      exact cmr_exact_period_lift_any (by omega) (rotDigitPerm_carry_cert 2 (by omega)) hlt' hcongr

/-- **INFINITE THEOREM B2 (Exact Period Spectrum Dichotomy for 2D Morton Swap `+ 1`):**
    For EVERY `n : Nat` and EVERY `z < 4^n`, the orbit length of `z` is strictly of the form
    `3^k` (with `k ≤ n`) or `2 * 3^k` (with `k + 2 ≤ n`). -/
theorem morton2D_period_dichotomy (n : Nat) :
    ∀ z, z < 4 ^ n →
      (∃ k, k ≤ n ∧ period2D n z = 3 ^ k) ∨
      (∃ k, k + 2 ≤ n ∧ period2D n z = 2 * 3 ^ k) := by
  induction n with
  | zero =>
    intro z _
    left; exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ n ih =>
    intro z hz
    have hdiv_lt : z / 4 < 4 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm] at hz
      exact Nat.div_lt_of_lt_mul hz
    simp only [period2D]
    by_cases h2 : (z % 4 == 2) = true
    · simp only [h2, ↓reduceIte]
      by_cases hd : allDiag2D n (z / 4) = true
      · simp only [hd, ↓reduceIte]
        left; exact ⟨0, by omega, rfl⟩
      · have hdf : allDiag2D n (z / 4) = false := by
          cases hx : allDiag2D n (z / 4) with
          | false => rfl
          | true => exact absurd hx hd
        simp only [hdf, Bool.false_eq_true, ↓reduceIte]
        cases n with
        | zero => simp [allDiag2D] at hdf
        | succ m =>
          right; exact ⟨0, by omega, rfl⟩
    · have h2f : (z % 4 == 2) = false := by
        cases hx : (z % 4 == 2) with
        | false => rfl
        | true => exact absurd hx h2
      simp only [h2f, Bool.false_eq_true, ↓reduceIte]
      have hlt' := shiftToFiber2D_lt n (z % 4) (z / 4) hdiv_lt
      rcases ih _ hlt' with ⟨k, hk, heq⟩ | ⟨k, hk, heq⟩
      · left; refine ⟨k + 1, by omega, ?_⟩
        rw [heq, Nat.pow_succ, Nat.mul_comm]
      · right; refine ⟨k + 1, by omega, ?_⟩
        rw [heq, Nat.pow_succ]; ac_rfl

/-- Exact boolean counter on `{0, ..., m - 1}`. -/
def countMod : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | m + 1, p => countMod m p + if p m then 1 else 0

theorem countMod_congr (m : Nat) {p q : Nat → Bool} (h : ∀ x, x < m → p x = q x) :
    countMod m p = countMod m q := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [countMod]
    rw [ih (fun x hx => h x (by omega)), h m (by omega)]

theorem countMod_false (m : Nat) : countMod m (fun _ => false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [countMod, ih]

theorem countMod_true (m : Nat) : countMod m (fun _ => true) = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [countMod, ih]

theorem countMod_add_compl (m : Nat) (p : Nat → Bool) :
    countMod m p + countMod m (fun x => !p x) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [countMod]
    by_cases h : p m = true
    · simp [h]; omega
    · have hf : p m = false := by cases hx : p m <;> simp_all
      simp [hf]; omega

theorem countMod_shift_succ (N : Nat) (hN : 0 < N) (p : Nat → Bool) :
    countMod N (fun x => p ((x + 1) % N)) = countMod N p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have haux : ∀ k, countMod k (fun x => p (x + 1)) + (if p 0 then 1 else 0) = countMod (k + 1) p := by
    intro k
    induction k with
    | zero => simp [countMod]
    | succ k ih =>
      simp only [countMod] at ih ⊢
      omega
  have hcongr : countMod m (fun x => p ((x + 1) % (m + 1))) = countMod m (fun x => p (x + 1)) := by
    apply countMod_congr
    intro x hx
    rw [Nat.mod_eq_of_lt (by omega)]
  change countMod m (fun x => p ((x + 1) % (m + 1))) + (if p ((m + 1) % (m + 1)) then 1 else 0) =
    countMod (m + 1) p
  simp only [Nat.mod_self, hcongr]
  exact haux m

/-- Radix-4 splitting lemma: `countMod (4 * M) p = ∑_{a=0}^3 countMod M (fun h => p (a + 4 * h))`. -/
theorem countMod_mul_four (M : Nat) (p : Nat → Bool) :
    countMod (4 * M) p =
      countMod M (fun h => p (0 + 4 * h)) +
      countMod M (fun h => p (1 + 4 * h)) +
      countMod M (fun h => p (2 + 4 * h)) +
      countMod M (fun h => p (3 + 4 * h)) := by
  induction M with
  | zero => rfl
  | succ M ih =>
    have h4 : 4 * (M + 1) = 4 * M + 4 := by omega
    rw [h4]
    simp only [countMod] at ih ⊢
    have h0 : 0 + 4 * M = 4 * M := by omega
    have h1 : 1 + 4 * M = 4 * M + 1 := by omega
    have h2 : 2 + 4 * M = 4 * M + 2 := by omega
    have h3 : 3 + 4 * M = 4 * M + 3 := by omega
    simp only [h0, h1, h2, h3, ih]
    omega

theorem countMod_wordPerm_swap2D (n : Nat) :
    ∀ (p : Nat → Bool), countMod (4 ^ n) (fun h => p (wordPerm 4 swap2D n h)) = countMod (4 ^ n) p := by
  induction n with
  | zero =>
    intro p; simp [countMod, wordPerm]
  | succ n ih =>
    intro p
    rw [Nat.pow_succ, Nat.mul_comm (4 ^ n) 4]
    rw [countMod_mul_four (4 ^ n), countMod_mul_four (4 ^ n)]
    have h0 : ∀ h, wordPerm 4 swap2D (n + 1) (0 + 4 * h) = 0 + 4 * wordPerm 4 swap2D n h := fun h =>
      wordPerm_add_mul 4 (by omega) swap2D n 0 h (by omega)
    have h1 : ∀ h, wordPerm 4 swap2D (n + 1) (1 + 4 * h) = 2 + 4 * wordPerm 4 swap2D n h := fun h =>
      wordPerm_add_mul 4 (by omega) swap2D n 1 h (by omega)
    have h2 : ∀ h, wordPerm 4 swap2D (n + 1) (2 + 4 * h) = 1 + 4 * wordPerm 4 swap2D n h := fun h =>
      wordPerm_add_mul 4 (by omega) swap2D n 2 h (by omega)
    have h3 : ∀ h, wordPerm 4 swap2D (n + 1) (3 + 4 * h) = 3 + 4 * wordPerm 4 swap2D n h := fun h =>
      wordPerm_add_mul 4 (by omega) swap2D n 3 h (by omega)
    have c0 : countMod (4 ^ n) (fun h => p (wordPerm 4 swap2D (n + 1) (0 + 4 * h))) =
        countMod (4 ^ n) (fun h => p (0 + 4 * h)) := by
      rw [countMod_congr (4 ^ n) (fun h _ => by rw [h0 h])]
      exact ih (fun y => p (0 + 4 * y))
    have c1 : countMod (4 ^ n) (fun h => p (wordPerm 4 swap2D (n + 1) (1 + 4 * h))) =
        countMod (4 ^ n) (fun h => p (2 + 4 * h)) := by
      rw [countMod_congr (4 ^ n) (fun h _ => by rw [h1 h])]
      exact ih (fun y => p (2 + 4 * y))
    have c2 : countMod (4 ^ n) (fun h => p (wordPerm 4 swap2D (n + 1) (2 + 4 * h))) =
        countMod (4 ^ n) (fun h => p (1 + 4 * h)) := by
      rw [countMod_congr (4 ^ n) (fun h _ => by rw [h2 h])]
      exact ih (fun y => p (1 + 4 * y))
    have c3 : countMod (4 ^ n) (fun h => p (wordPerm 4 swap2D (n + 1) (3 + 4 * h))) =
        countMod (4 ^ n) (fun h => p (3 + 4 * h)) := by
      rw [countMod_congr (4 ^ n) (fun h _ => by rw [h3 h])]
      exact ih (fun y => p (3 + 4 * y))
    rw [c0, c1, c2, c3]
    omega

theorem countMod_step_swap2D (n : Nat) (p : Nat → Bool) :
    countMod (4 ^ n) (fun h => p (step 4 swap2D n h)) = countMod (4 ^ n) p := by
  have h1 := countMod_wordPerm_swap2D n (fun y => p ((y + 1) % 4 ^ n))
  have h2 := countMod_shift_succ (4 ^ n) (Nat.pow_pos (by omega)) p
  exact h1.trans h2

/-- Exact diagonal count: `countMod (4^n) (allDiag2D n) = 2^n`. -/
theorem countMod_allDiag2D (n : Nat) :
    countMod (4 ^ n) (allDiag2D n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ 4 n, Nat.mul_comm (4 ^ n) 4, countMod_mul_four]
    have h0 : ∀ h, allDiag2D (n + 1) (0 + 4 * h) = allDiag2D n h := fun h => by
      simp only [allDiag2D]
      have hm : (0 + 4 * h) % 4 = 0 := by omega
      have hd : (0 + 4 * h) / 4 = h := by omega
      rw [hm, hd]; rfl
    have h1 : ∀ h, allDiag2D (n + 1) (1 + 4 * h) = false := fun h => by
      simp only [allDiag2D]
      have hm : (1 + 4 * h) % 4 = 1 := by omega
      rw [hm]; rfl
    have h2 : ∀ h, allDiag2D (n + 1) (2 + 4 * h) = false := fun h => by
      simp only [allDiag2D]
      have hm : (2 + 4 * h) % 4 = 2 := by omega
      rw [hm]; rfl
    have h3 : ∀ h, allDiag2D (n + 1) (3 + 4 * h) = allDiag2D n h := fun h => by
      simp only [allDiag2D]
      have hm : (3 + 4 * h) % 4 = 3 := by omega
      have hd : (3 + 4 * h) / 4 = h := by omega
      rw [hm, hd]; rfl
    rw [countMod_congr (4 ^ n) (fun h _ => h0 h),
        countMod_congr (4 ^ n) (fun h _ => h1 h),
        countMod_congr (4 ^ n) (fun h _ => h2 h),
        countMod_congr (4 ^ n) (fun h _ => h3 h),
        countMod_false, ih, Nat.pow_succ]
    omega

/-- **Exact Recurrence for Period-Class Populations under 2D Morton Swap `+ 1`:**
    For any `P` with `3 ∣ P` (`P = 3 * Q`), the number of elements in `Fin (4^(n+1))` of period `3 * Q`
    is **EXACTLY** `3` times the number of elements in `Fin (4^n)` of period `Q`! -/
theorem countMod_period2D_mul3 (n Q : Nat) :
    countMod (4 ^ (n + 1)) (fun z => period2D (n + 1) z == 3 * Q) =
      3 * countMod (4 ^ n) (fun h => period2D n h == Q) := by
  rw [Nat.pow_succ 4 n, Nat.mul_comm (4 ^ n) 4, countMod_mul_four]
  have h2false : ∀ h, (period2D (n + 1) (2 + 4 * h) == 3 * Q) = false := by
    intro h
    simp only [period2D]
    have hm : (2 + 4 * h) % 4 = 2 := by omega
    rw [hm]; simp only [beq_self_eq_true, ↓reduceIte]
    cases allDiag2D n ((2 + 4 * h) / 4) <;> (simp only [↓reduceIte, Bool.false_eq_true]; exact beq_false_of_ne (by omega))
  have h0eq : ∀ h, (period2D (n + 1) (0 + 4 * h) == 3 * Q) = (period2D n h == Q) := by
    intro h
    simp only [period2D, shiftToFiber2D]
    have hm : (0 + 4 * h) % 4 = 0 := by omega
    have hd : (0 + 4 * h) / 4 = h := by omega
    rw [hm, hd]
    simp only [show (0 == 2) = false by decide, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    by_cases heq : period2D n h = Q
    · rw [heq]; simp
    · simp [beq_false_of_ne heq, beq_false_of_ne (show 3 * period2D n h ≠ 3 * Q by omega)]
  have h1eq : ∀ h, (period2D (n + 1) (1 + 4 * h) == 3 * Q) = (period2D n ((h + 1) % 4 ^ n) == Q) := by
    intro h
    simp only [period2D, shiftToFiber2D]
    have hm : (1 + 4 * h) % 4 = 1 := by omega
    have hd : (1 + 4 * h) / 4 = h := by omega
    rw [hm, hd]
    simp only [show (1 == 2) = false by decide, show (1 == 0) = false by decide,
               show (1 == 3) = false by decide, Bool.false_eq_true, ↓reduceIte]
    by_cases heq : period2D n ((h + 1) % 4 ^ n) = Q
    · rw [heq]; simp
    · simp [beq_false_of_ne heq, beq_false_of_ne (show 3 * period2D n ((h + 1) % 4 ^ n) ≠ 3 * Q by omega)]
  have h3eq : ∀ h, (period2D (n + 1) (3 + 4 * h) == 3 * Q) = (period2D n (step 4 swap2D n h) == Q) := by
    intro h
    simp only [period2D, shiftToFiber2D]
    have hm : (3 + 4 * h) % 4 = 3 := by omega
    have hd : (3 + 4 * h) / 4 = h := by omega
    rw [hm, hd]
    simp only [show (3 == 2) = false by decide, show (3 == 0) = false by decide,
               beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
    by_cases heq : period2D n (step 4 swap2D n h) = Q
    · rw [heq]; simp
    · simp [beq_false_of_ne heq, beq_false_of_ne (show 3 * period2D n (step 4 swap2D n h) ≠ 3 * Q by omega)]
  rw [countMod_congr (4 ^ n) (fun h _ => h0eq h),
      countMod_congr (4 ^ n) (fun h _ => h1eq h),
      countMod_congr (4 ^ n) (fun h _ => h2false h),
      countMod_congr (4 ^ n) (fun h _ => h3eq h),
      countMod_false,
      countMod_shift_succ (4 ^ n) (Nat.pow_pos (by omega)) (fun x => period2D n x == Q),
      countMod_step_swap2D n (fun h => period2D n h == Q)]
  omega

theorem countMod_period2D_one (n : Nat) :
    countMod (4 ^ (n + 1)) (fun z => period2D (n + 1) z == 1) = 2 ^ n := by
  rw [Nat.pow_succ 4 n, Nat.mul_comm (4 ^ n) 4, countMod_mul_four]
  have hnot2 : ∀ a, a < 4 → a ≠ 2 → ∀ h, (period2D (n + 1) (a + 4 * h) == 1) = false := by
    intro a ha hne h
    simp only [period2D]
    have hm : (a + 4 * h) % 4 = a := by omega
    rw [hm, beq_false_of_ne hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact beq_false_of_ne (by omega)
  have h2eq : ∀ h, (period2D (n + 1) (2 + 4 * h) == 1) = allDiag2D n h := by
    intro h
    simp only [period2D]
    have hm : (2 + 4 * h) % 4 = 2 := by omega
    have hd : (2 + 4 * h) / 4 = h := by omega
    rw [hm, hd]; simp only [beq_self_eq_true, ↓reduceIte]
    cases allDiag2D n h <;> decide
  rw [countMod_congr (4 ^ n) (fun h _ => hnot2 0 (by omega) (by omega) h),
      countMod_congr (4 ^ n) (fun h _ => hnot2 1 (by omega) (by omega) h),
      countMod_congr (4 ^ n) (fun h _ => h2eq h),
      countMod_congr (4 ^ n) (fun h _ => hnot2 3 (by omega) (by omega) h),
      countMod_false, countMod_allDiag2D n]
  omega

theorem countMod_period2D_two (n : Nat) :
    countMod (4 ^ (n + 1)) (fun z => period2D (n + 1) z == 2) = 4 ^ n - 2 ^ n := by
  rw [Nat.pow_succ 4 n, Nat.mul_comm (4 ^ n) 4, countMod_mul_four]
  have hnot2 : ∀ a, a < 4 → a ≠ 2 → ∀ h, (period2D (n + 1) (a + 4 * h) == 2) = false := by
    intro a ha hne h
    simp only [period2D]
    have hm : (a + 4 * h) % 4 = a := by omega
    rw [hm, beq_false_of_ne hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact beq_false_of_ne (by omega)
  have h2eq : ∀ h, (period2D (n + 1) (2 + 4 * h) == 2) = !allDiag2D n h := by
    intro h
    simp only [period2D]
    have hm : (2 + 4 * h) % 4 = 2 := by omega
    have hd : (2 + 4 * h) / 4 = h := by omega
    rw [hm, hd]; simp only [beq_self_eq_true, ↓reduceIte]
    cases allDiag2D n h <;> decide
  rw [countMod_congr (4 ^ n) (fun h _ => hnot2 0 (by omega) (by omega) h),
      countMod_congr (4 ^ n) (fun h _ => hnot2 1 (by omega) (by omega) h),
      countMod_congr (4 ^ n) (fun h _ => h2eq h),
      countMod_congr (4 ^ n) (fun h _ => hnot2 3 (by omega) (by omega) h),
      countMod_false]
  have hsum := countMod_add_compl (4 ^ n) (allDiag2D n)
  rw [countMod_allDiag2D n] at hsum
  omega

/-- **INFINITE THEOREM B3 (Exact Complete Cycle-Spectrum Multiplicities for ALL `n ≥ 1`):**
    1. Unique giant cycle of length `3^n`: exactly `3^n` elements (`1` cycle).
    2. For every `k < n`: exactly `3^k * 2^(n - 1 - k)` elements of period `3^k` (`2^(n - 1 - k)` cycles).
    3. For every `k + 2 ≤ n`: exactly `3^k * (4^(n - 1 - k) - 2^(n - 1 - k))` elements of period `2 * 3^k`
       (`2^(n - 2 - k) * (2^(n - 1 - k) - 1)` cycles). -/
theorem morton2D_count_giant (n : Nat) :
    countMod (4 ^ n) (fun z => period2D n z == 3 ^ n) = 3 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h3 : 3 ^ (n + 1) = 3 * 3 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h3, countMod_period2D_mul3, ih]

theorem morton2D_count_pow3 (k : Nat) :
    ∀ n, k < n → countMod (4 ^ n) (fun z => period2D n z == 3 ^ k) = 3 ^ k * 2 ^ (n - 1 - k) := by
  induction k with
  | zero =>
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa [Nat.pow_zero, Nat.one_mul] using countMod_period2D_one m
  | succ k ih =>
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have h3 : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h3, countMod_period2D_mul3, ih m (by omega)]
    have hsub : m + 1 - 1 - (k + 1) = m - 1 - k := by omega
    rw [hsub, Nat.mul_assoc]

theorem morton2D_count_two_pow3 (k : Nat) :
    ∀ n, k + 2 ≤ n →
      countMod (4 ^ n) (fun z => period2D n z == 2 * 3 ^ k) =
        3 ^ k * (4 ^ (n - 1 - k) - 2 ^ (n - 1 - k)) := by
  induction k with
  | zero =>
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa [Nat.pow_zero, Nat.mul_one, Nat.one_mul] using countMod_period2D_two m
  | succ k ih =>
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have h3 : 2 * 3 ^ (k + 1) = 3 * (2 * 3 ^ k) := by rw [Nat.pow_succ]; ac_rfl
    rw [h3, countMod_period2D_mul3, ih m (by omega)]
    have hsub : m + 1 - 1 - (k + 1) = m - 1 - k := by omega
    rw [hsub, Nat.pow_succ, Nat.mul_comm (3 ^ k) 3, Nat.mul_assoc]

/-! ## Section 6: Infinite Theorem C — Non-Nilpotent 4D Morton Coordinate 3-Cycle Full-Period Theorem -/

/-- Pure 4D Morton coordinate 3-cycle `(0 → 2, 1 → 1, 2 → 3, 3 → 0)` acting on 4-bit digits. -/
def perm4_3cycleFun (a : Nat) : Nat :=
  let b0 := a % 2
  let b1 := (a / 2) % 2
  let b2 := (a / 4) % 2
  let b3 := (a / 8) % 2
  b3 + 2 * b1 + 4 * b0 + 8 * b2

/-- Inverse coordinate 3-cycle `(0 → 3, 1 → 1, 2 → 0, 3 → 2)`. -/
def perm4_3cycleInv (a : Nat) : Nat :=
  let b0 := a % 2
  let b1 := (a / 2) % 2
  let b2 := (a / 4) % 2
  let b3 := (a / 8) % 2
  b2 + 2 * b1 + 4 * b3 + 8 * b0

def perm4_3cycle : DigitPerm 16 where
  toFun := perm4_3cycleFun
  invFun := perm4_3cycleInv
  h_lt := by intro a ha; revert a; decide
  h_inv_lt := by intro a ha; revert a; decide
  h_left := by intro a ha; revert a; decide
  h_right := by intro a ha; revert a; decide

theorem perm4_3cycle_carry_cert : CarryCycleCert 16 perm4_3cycle 16 where
  hL := by omega
  h_no_carry := by intro r hr; revert r; decide
  h_carry := by decide

theorem perm4_3cycle_closure (a : Nat) (ha : a < 16) :
    (perm4_3cycle.pow 16).toFun a = perm4_3cycle.toFun a := by
  revert a; decide

/-- Non-nilpotence witness: `perm4_3cycle` has exact order `3` (does NOT divide `B = 16`!). -/
theorem perm4_3cycle_order_three :
    (∀ a, a < 16 → (perm4_3cycle.pow 3).toFun a = a) ∧ perm4_3cycle.toFun 1 ≠ 1 := by
  refine ⟨?_, by decide⟩
  intro a ha; revert a; decide

def perm4_3cycleAutomaton : RenormAutomaton 16 1 where
  perm := fun _ => perm4_3cycle
  len := fun _ => 16
  next := fun s => s
  cert := fun _ => perm4_3cycle_carry_cert
  closure := fun _ a ha => perm4_3cycle_closure a ha

/-- **INFINITE THEOREM C (Non-Nilpotent 4D Morton Coordinate 3-Cycle Universal Full-Period):**
    Even though `perm4_3cycle` has order `3 ∤ 16` and NEVER collapses to the identity under
    renormalization (`π^16 = π`), for EVERY precision `n ≥ 0`, `step 16 perm4_3cycle n` is a
    **single Hamiltonian full-period cycle of length `16^n = 2^(4n)`**! -/
theorem morton4D_3cycle_full_period (n : Nat) :
    HasExactPeriod (step 16 perm4_3cycle n) 0 (16 ^ n) :=
  cmr_full_period_compiler (by omega) perm4_3cycleAutomaton (fun _ => rfl) ⟨0, by omega⟩ n

/-! ## Section 7: Infinite Theorem D — 3D Trichotomy, Delayed-Fracture Trap & Sharpness Counterexamples -/

/-- D1: 3D Morton coordinate transposition `swapYZ = (0, 2, 1)` (swaps bits 1 and 2, fixes bit 0). -/
def swapYZ3DFun (a : Nat) : Nat :=
  let b0 := a % 2
  let b1 := (a / 2) % 2
  let b2 := (a / 4) % 2
  b0 + 2 * b2 + 4 * b1

def swapYZ3D : DigitPerm 8 where
  toFun := swapYZ3DFun
  invFun := swapYZ3DFun
  h_lt := by intro a ha; revert a; decide
  h_inv_lt := by intro a ha; revert a; decide
  h_left := by intro a ha; revert a; decide
  h_right := by intro a ha; revert a; decide

theorem id8_carry_cert : CarryCycleCert 8 (DigitPerm.id 8) 8 where
  hL := by omega
  h_no_carry := by intro r hr; revert r; decide
  h_carry := by decide

theorem swapYZ3D_carry_cert : CarryCycleCert 8 swapYZ3D 8 where
  hL := by omega
  h_no_carry := by intro r hr; revert r; decide
  h_carry := by decide

def swapYZ3DAutomaton : RenormAutomaton 8 2 where
  perm := fun s => if s.val == 0 then swapYZ3D else DigitPerm.id 8
  len := fun _ => 8
  next := fun _ => ⟨1, by omega⟩
  cert := fun s => by
    cases s with | mk v hv =>
    have : v = 0 ∨ v = 1 := by omega
    rcases this with rfl | rfl
    · exact swapYZ3D_carry_cert
    · exact id8_carry_cert
  closure := fun s a ha => by
    cases s with | mk v hv =>
    have : v = 0 ∨ v = 1 := by omega
    rcases this with rfl | rfl
    · have h : ∀ x, x < 8 → (swapYZ3D.pow 8).toFun x = (DigitPerm.id 8).toFun x := by decide
      exact h a ha
    · have h : ∀ x, x < 8 → ((DigitPerm.id 8).pow 8).toFun x = (DigitPerm.id 8).toFun x := by decide
      exact h a ha

/-- **3D Trichotomy — Regime II (Full-Period):** `swapYZ = (0, 2, 1)` has full period `8^n` for all `n`. -/
theorem morton3D_swapYZ_full_period (n : Nat) :
    HasExactPeriod (step 8 swapYZ3D n) 0 (8 ^ n) :=
  cmr_full_period_compiler (by omega) swapYZ3DAutomaton (fun _ => rfl) ⟨0, by omega⟩ n

/-- D2: 3D Morton coordinate transposition `swapXY = (1, 0, 2)` (swaps bits 0 and 1, fixes bit 2). -/
def swapXY3DFun (a : Nat) : Nat :=
  let b0 := a % 2
  let b1 := (a / 2) % 2
  let b2 := (a / 4) % 2
  b1 + 2 * b0 + 4 * b2

def swapXY3D : DigitPerm 8 where
  toFun := swapXY3DFun
  invFun := swapXY3DFun
  h_lt := by intro a ha; revert a; decide
  h_inv_lt := by intro a ha; revert a; decide
  h_left := by intro a ha; revert a; decide
  h_right := by intro a ha; revert a; decide

theorem swapXY3D_carry_cert : CarryCycleCert 8 swapXY3D 6 where
  hL := by omega
  h_no_carry := by intro r hr; revert r; decide
  h_carry := by decide

def swapXY3DAutomaton : RenormAutomaton 8 2 where
  perm := fun s => if s.val == 0 then swapXY3D else DigitPerm.id 8
  len := fun s => if s.val == 0 then 6 else 8
  next := fun _ => ⟨1, by omega⟩
  cert := fun s => by
    cases s with | mk v hv =>
    have : v = 0 ∨ v = 1 := by omega
    rcases this with rfl | rfl
    · exact swapXY3D_carry_cert
    · exact id8_carry_cert
  closure := fun s a ha => by
    cases s with | mk v hv =>
    have : v = 0 ∨ v = 1 := by omega
    rcases this with rfl | rfl
    · have h : ∀ x, x < 8 → (swapXY3D.pow 6).toFun x = (DigitPerm.id 8).toFun x := by decide
      simpa using h a ha
    · have h : ∀ x, x < 8 → ((DigitPerm.id 8).pow 8).toFun x = (DigitPerm.id 8).toFun x := by decide
      simpa using h a ha

theorem swapXY3DAutomaton_orbitProd (n : Nat) :
    swapXY3DAutomaton.orbitProd ⟨0, by omega⟩ (n + 1) = 6 * 8 ^ n := by
  have hid : ∀ m, swapXY3DAutomaton.orbitProd ⟨1, by omega⟩ m = 8 ^ m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [RenormAutomaton.orbitProd, swapXY3DAutomaton] at ih ⊢
      rw [ih, Nat.pow_succ, Nat.mul_comm]
      rfl
  simp only [RenormAutomaton.orbitProd, swapXY3DAutomaton]
  exact congrArg (6 * ·) (hid n)

/-- **3D Trichotomy — Regime III (Mixed 3/4):** `swapXY = (1, 0, 2)` has exact period `6 * 8^n`
    at width `n + 1` for ALL `n : Nat`. -/
theorem morton3D_swapXY_mixed_period (n : Nat) :
    HasExactPeriod (step 8 swapXY3D (n + 1)) 0 (6 * 8 ^ n) := by
  have h := cmr_automaton_lift (by omega) swapXY3DAutomaton (n + 1) ⟨0, by omega⟩
  rw [swapXY3DAutomaton_orbitProd n] at h
  exact h

/-- **INFINITE THEOREM D (Delayed-Fracture Trap — Exact Period for ALL `n`):** -/
theorem delayed_fracture_exact_period (n : Nat) :
    HasExactPeriod (step 8 piDelay n) 0 (piDelayAutomaton.orbitProd ⟨0, by omega⟩ n) :=
  cmr_automaton_lift (by omega) piDelayAutomaton n ⟨0, by omega⟩

/-- Closed-form period formula: `orbitProd(0, n) * 2^(n / 3) = 8^n` for ALL `n : Nat`. -/
theorem delayed_fracture_closed_form (n : Nat) :
    piDelayAutomaton.orbitProd ⟨0, by omega⟩ n * 2 ^ (n / 3) = 8 ^ n := by
  have hstep3 : ∀ m, piDelayAutomaton.orbitProd ⟨0, by omega⟩ (m + 3) =
      256 * piDelayAutomaton.orbitProd ⟨0, by omega⟩ m := by
    intro m
    change 8 * (8 * (4 * piDelayAutomaton.orbitProd ⟨0, by omega⟩ m)) =
      256 * piDelayAutomaton.orbitProd ⟨0, by omega⟩ m
    omega
  have hmain : ∀ q r, r < 3 →
      piDelayAutomaton.orbitProd ⟨0, by omega⟩ (3 * q + r) * 2 ^ q = 8 ^ (3 * q + r) := by
    intro q r hr
    induction q with
    | zero =>
      have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      rcases this with rfl | rfl | rfl <;> decide
    | succ q ih =>
      have heq : 3 * (q + 1) + r = (3 * q + r) + 3 := by omega
      rw [heq, hstep3 (3 * q + r)]
      have h8 : 8 ^ (3 * q + r + 3) = 512 * 8 ^ (3 * q + r) := by
        rw [Nat.pow_add]; have : 8 ^ 3 = 512 := rfl; rw [this, Nat.mul_comm]
      rw [h8, Nat.pow_succ 2 q]
      have hmul : 256 * piDelayAutomaton.orbitProd ⟨0, by omega⟩ (3 * q + r) * (2 ^ q * 2) =
          512 * (piDelayAutomaton.orbitProd ⟨0, by omega⟩ (3 * q + r) * 2 ^ q) := by
        have h256 : 256 * 2 = 512 := rfl
        calc 256 * piDelayAutomaton.orbitProd ⟨0, by omega⟩ (3 * q + r) * (2 ^ q * 2)
            = (256 * 2) * (piDelayAutomaton.orbitProd ⟨0, by omega⟩ (3 * q + r) * 2 ^ q) := by ac_rfl
          _ = 512 * (piDelayAutomaton.orbitProd ⟨0, by omega⟩ (3 * q + r) * 2 ^ q) := by rw [h256]
      rw [hmul, ih]
  have hdm : 3 * (n / 3) + n % 3 = n := Nat.div_add_mod n 3
  have hres := hmain (n / 3) (n % 3) (Nat.mod_lt n (by omega))
  rw [hdm] at hres
  exact hres

/-- Explicit delayed-fracture milestones: FULL PERIOD at `n = 1` and `n = 2`, FRACTURE at `n = 3`! -/
theorem delayed_fracture_milestones :
    HasExactPeriod (step 8 piDelay 1) 0 (8 ^ 1) ∧
    HasExactPeriod (step 8 piDelay 2) 0 (8 ^ 2) ∧
    HasExactPeriod (step 8 piDelay 3) 0 256 ∧
    256 < 8 ^ 3 := by
  have h1 : piDelayAutomaton.orbitProd ⟨0, by omega⟩ 1 = 8 ^ 1 := by decide
  have h2 : piDelayAutomaton.orbitProd ⟨0, by omega⟩ 2 = 8 ^ 2 := by decide
  have h3 : piDelayAutomaton.orbitProd ⟨0, by omega⟩ 3 = 256 := by decide
  refine ⟨?_, ?_, ?_, by decide⟩
  · rw [← h1]; exact delayed_fracture_exact_period 1
  · rw [← h2]; exact delayed_fracture_exact_period 2
  · rw [← h3]; exact delayed_fracture_exact_period 3

/-- D4: **Addend `+2` Sharpness Counterexample:**
    Relaxing the single-carry-source addend `+1` to `+2` on 2D Morton swap (`n = 2`) breaks
    the `3^2 = 9` orbit law: `0` instead has exact period `12 ≠ 9`! -/
def step2DPlus2 (z : Nat) : Nat :=
  (wordPerm 4 swap2D 2 z + 2) % 16

theorem sharpness_addend_plus2_breaks_pow3 :
    iter step2DPlus2 9 0 ≠ 0 ∧ HasExactPeriod step2DPlus2 0 12 := by
  refine ⟨by decide, by omega, by decide, ?_⟩
  have hmin : ∀ t, t < 12 → 0 < t → iter step2DPlus2 t 0 ≠ 0 := by decide
  intro t ht1 ht2
  exact hmin t ht2 ht1

/-! ## Section 8: Non-Vacuity Witnesses & Kernel Axiom Audits -/

/-- Non-vacuity witness 1: `CarryCycleCert` is inhabited across ALL dimensions `d ≥ 1`. -/
theorem nonvacuity_carryCycleCert (d : Nat) (hd : 1 ≤ d) :
    Nonempty (CarryCycleCert (2 ^ d) (rotDigitPerm d hd) (d + 1)) :=
  ⟨rotDigitPerm_carry_cert d hd⟩

/-- Non-vacuity witness 2: `RenormAutomaton` is inhabited in all 3 regimes:
    fixed-point fractal (`S = 1`), non-nilpotent full-period (`S = 1`, `ord 3 ∤ 16`),
    and delayed-fracture oscillating (`S = 3`). -/
theorem nonvacuity_renormAutomata :
    Nonempty (RenormAutomaton 4 1) ∧
    Nonempty (RenormAutomaton 16 1) ∧
    Nonempty (RenormAutomaton 8 3) :=
  ⟨⟨mortonRotAutomaton 2 (by omega)⟩, ⟨perm4_3cycleAutomaton⟩, ⟨piDelayAutomaton⟩⟩

/-- Concrete kernel-checked witness on native `BitVec 6` (3D Morton rotation, `n = 2`, period `4^2 = 16`). -/
example : HasExactPeriod (mortonRotIncBV 3 (by omega) 2) (BitVec.ofNat 6 0) 16 :=
  mortonRotIncBV_exact_period_all_d_n 3 (by omega) 2

end Dynsil4.CMR

-- Kernel axiom audits (must contain ONLY standard axioms `{propext, Classical.choice, Quot.sound}` or empty)


