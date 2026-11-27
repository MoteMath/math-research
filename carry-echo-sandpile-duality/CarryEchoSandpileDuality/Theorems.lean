/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryEchoSandpileDuality.Defs

/-!
# Theorems (`carry-echo-sandpile-duality`)

Full proofs of the headline infinite theorems of Carry-Echo and Directed-Carry Silicon Sandpile Duality Engine.
-/

namespace SiliconSandpile

theorem addCfg_comm {w : Nat} (x y : Fin w → Nat) : addCfg x y = addCfg y x := by
  funext i; exact Nat.add_comm (x i) (y i)

theorem addCfg_assoc {w : Nat} (x y z : Fin w → Nat) :
    addCfg (addCfg x y) z = addCfg x (addCfg y z) := by
  funext i; exact Nat.add_assoc (x i) (y i) (z i)

theorem addCfg_zero_left {w : Nat} (x : Fin w → Nat) : addCfg (zeroCfg w) x = x := by
  funext i; exact Nat.zero_add (x i)

theorem addCfg_zero_right {w : Nat} (x : Fin w → Nat) : addCfg x (zeroCfg w) = x := by
  funext i; exact Nat.add_zero (x i)

theorem addCfg_single_decAt {w : Nat} (f : Fin w → Nat) (i : Fin w) (h : 0 < f i) :
    addCfg (singleCfg i 1) (decAt f i) = f := by
  funext j
  simp only [addCfg, singleCfg, decAt]
  by_cases hji : j = i
  · subst hji; simp; omega
  · simp [hji]

theorem decAt_addCfg_single_self {w : Nat} (f : Fin w → Nat) (i : Fin w) :
    decAt (addCfg (singleCfg i 1) f) i = f := by
  funext j
  simp only [decAt, addCfg, singleCfg]
  by_cases hji : j = i
  · subst hji; simp
  · simp [hji]

theorem decAt_addCfg_single_ne {w : Nat} (f : Fin w → Nat) {k i : Fin w} (hne : k ≠ i) :
    addCfg (singleCfg k 1) (decAt f i) = decAt (addCfg (singleCfg k 1) f) i := by
  funext j
  simp only [addCfg, singleCfg, decAt]
  by_cases hjk : j = k
  · subst hjk
    simp [hne]
  · by_cases hji : j = i
    · subst hji
      simp [hjk]
    · simp [hjk, hji]

theorem finSum_mul_left (w : Nat) (k : Nat) (f : Fin w → Nat) :
    finSum w (fun i => k * f i) = k * finSum w f := by
  induction w with
  | zero => simp [finSum]
  | succ w ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc), Nat.mul_add]

theorem finSum_mul_right (w : Nat) (f : Fin w → Nat) (k : Nat) :
    finSum w (fun i => f i * k) = finSum w f * k := by
  induction w with
  | zero => simp [finSum]
  | succ w ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc), Nat.add_mul]

theorem finSum_add_single {w : Nat} (f : Fin w → Nat) (i : Fin w) (v : Nat) :
    finSum w (fun j => f j + if j = i then v else 0) = finSum w f + v := by
  rw [finSum_add, finSum_single]

theorem finSum_le {w : Nat} {f g : Fin w → Nat} (h : ∀ i, f i ≤ g i) :
    finSum w f ≤ finSum w g := by
  induction w with
  | zero => exact Nat.le_refl 0
  | succ w ih =>
    simp only [finSum]
    exact Nat.add_le_add (ih (fun i => h i.castSucc)) (h ⟨w, Nat.lt_succ_self w⟩)

theorem finSum_single_le {w : Nat} (f : Fin w → Nat) (i : Fin w) :
    f i ≤ finSum w f := by
  have h : finSum w (fun j => if j = i then f i else 0) ≤ finSum w f := by
    apply finSum_le
    intro j
    split
    · next hji => subst hji; exact Nat.le_refl _
    · exact Nat.zero_le _
  rw [finSum_single] at h
  exact h

theorem finSum_dvd {w : Nat} (M : Nat) (f : Fin w → Nat) (h : ∀ i, M ∣ f i) :
    M ∣ finSum w f := by
  induction w with
  | zero => exact Nat.dvd_zero M
  | succ w ih =>
    simp only [finSum]
    exact Nat.dvd_add (ih (fun i => f i.castSucc) (fun i => h i.castSucc))
                      (h ⟨w, Nat.lt_succ_self w⟩)

theorem dot_add_left (w : Nat) (x y z : Fin w → Nat) :
    dot w (addCfg x y) z = dot w x z + dot w y z := by
  unfold dot addCfg
  have h : finSum w (fun i => (x i + y i) * z i) = finSum w (fun i => x i * z i + y i * z i) :=
    finSum_congr (fun i => Nat.add_mul (x i) (y i) (z i))
  rw [h, finSum_add]

theorem dot_single_left {w : Nat} (i : Fin w) (v : Nat) (y : Fin w → Nat) :
    dot w (singleCfg i v) y = v * y i := by
  unfold dot singleCfg
  have h : finSum w (fun j => (if j = i then v else 0) * y j) =
           finSum w (fun j => if j = i then v * y i else 0) := by
    apply finSum_congr
    intro j
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  rw [h, finSum_single]

theorem dot_zero_left (w : Nat) (y : Fin w → Nat) : dot w (zeroCfg w) y = 0 := by
  unfold dot zeroCfg
  have h : finSum w (fun i => 0 * y i) = finSum w (fun _ => 0) :=
    finSum_congr (fun i => Nat.zero_mul (y i))
  rw [h, finSum_zero]

theorem dot_comm (w : Nat) (x y : Fin w → Nat) : dot w x y = dot w y x := by
  unfold dot
  apply finSum_congr
  intro i; exact Nat.mul_comm (x i) (y i)

/-! ## Part 2: Generic Reusable Abelian Sandpile & Harmonic-Lifting Engine -/

namespace AbelianToppleSys

variable {w : Nat}

theorem maxStable_isStable (S : AbelianToppleSys w) : S.IsStable S.maxStable := by
  intro i
  have hp := S.tau_pos i
  simp only [maxStable]
  omega

theorem Steps.single {S : AbelianToppleSys w} {c c' : Fin w → Nat} {i : Fin w} (h : S.Step c i c') :
    S.Steps c (singleCfg i 1) c' := by
  have hs := Steps.step h (Steps.refl c')
  rw [addCfg_zero_right] at hs
  exact hs

theorem Steps.trans {S : AbelianToppleSys w} {c₁ c₂ c₃ f₁ f₂ : Fin w → Nat}
    (h1 : S.Steps c₁ f₁ c₂) (h2 : S.Steps c₂ f₂ c₃) :
    S.Steps c₁ (addCfg f₁ f₂) c₃ := by
  induction h1 with
  | refl c =>
    rw [addCfg_zero_left]
    exact h2
  | step hs _ ih =>
    rw [addCfg_assoc]
    exact Steps.step hs (ih h2)

theorem Step.add_right {S : AbelianToppleSys w} {c c' : Fin w → Nat} {i : Fin w}
    (h : S.Step c i c') (d : Fin w → Nat) :
    S.Step (addCfg c d) i (addCfg c' d) := by
  rcases h with ⟨hlen, rfl⟩
  refine ⟨?_, ?_⟩
  · simp only [addCfg]; omega
  · funext j
    simp only [fire, addCfg]
    by_cases hji : j = i
    · subst hji; simp; omega
    · simp [hji]; omega

theorem Steps.add_right {S : AbelianToppleSys w} {c₁ c₂ f : Fin w → Nat}
    (h : S.Steps c₁ f c₂) (d : Fin w → Nat) :
    S.Steps (addCfg c₁ d) f (addCfg c₂ d) := by
  induction h with
  | refl c => exact Steps.refl (addCfg c d)
  | step hs _ ih => exact Steps.step (hs.add_right d) ih

theorem Steps.add_left {S : AbelianToppleSys w} {c₁ c₂ f : Fin w → Nat}
    (h : S.Steps c₁ f c₂) (d : Fin w → Nat) :
    S.Steps (addCfg d c₁) f (addCfg d c₂) := by
  rw [addCfg_comm d c₁, addCfg_comm d c₂]
  exact h.add_right d

/-! ### Linear Balance & Strict Potential Certificates -/

theorem LinearBalance.conservation {S : AbelianToppleSys w} (B : S.LinearBalance)
    {c c' f : Fin w → Nat} (h : S.Steps c f c') :
    dot w c B.p = dot w c' B.p + dot w f B.delta := by
  induction h with
  | refl c =>
    rw [dot_zero_left, Nat.add_zero]
  | step hs _ ih =>
    rw [B.step_eq hs, ih, dot_add_left, dot_single_left, Nat.one_mul]
    omega

theorem LinearBalance.mod_invariant {S : AbelianToppleSys w} (B : S.LinearBalance) (M : Nat)
    (hdiv : ∀ i, M ∣ B.delta i) {c c' f : Fin w → Nat} (h : S.Steps c f c') :
    dot w c B.p % M = dot w c' B.p % M := by
  have hcons := B.conservation h
  have hM : M ∣ dot w f B.delta :=
    finSum_dvd M (fun i => f i * B.delta i) (fun i => Nat.dvd_trans (hdiv i) (Nat.dvd_mul_left (B.delta i) (f i)))
  rcases hM with ⟨q, hq⟩
  rw [hcons, hq, Nat.add_mul_mod_self_left]

theorem diamond_step (S : AbelianToppleSys w) {c : Fin w → Nat} {i j : Fin w} (hne : i ≠ j)
    (hi : S.tau i ≤ c i) (hj : S.tau j ≤ c j) :
    S.Step (S.fire c i) j (S.fire (S.fire c i) j) ∧
    S.Step (S.fire c j) i (S.fire (S.fire c j) i) ∧
    S.fire (S.fire c i) j = S.fire (S.fire c j) i := by
  have hne' : j ≠ i := fun h => hne h.symm
  refine ⟨⟨?_, rfl⟩, ⟨?_, rfl⟩, ?_⟩
  · simp only [fire, ite_eq_right_iff.mpr (fun h => False.elim (hne' h))]; omega
  · simp only [fire, ite_eq_right_iff.mpr (fun h => False.elim (hne h))]; omega
  · funext k
    simp only [fire]
    by_cases hki : k = i
    · subst hki
      simp [hne]
      omega
    · by_cases hkj : k = j
      · subst hkj
        simp [hne']
        omega
      · simp [hki, hkj]
        omega

theorem abelian_exchange (S : AbelianToppleSys w) {c c₁ c₂ f : Fin w → Nat} {i : Fin w}
    (hstep : S.Step c i c₁) (hsteps : S.Steps c f c₂) (hstab : S.IsStable c₂) :
    0 < f i ∧ S.Steps c₁ (decAt f i) c₂ := by
  induction hsteps generalizing c₁ with
  | refl c =>
    exfalso
    have hlt := hstab i
    have hle := hstep.1
    omega
  | @step c c' c₂ k f' hsk hrest ih =>
    by_cases hki : k = i
    · subst hki
      have hceq : c' = c₁ := by rw [hsk.2, hstep.2]
      subst hceq
      refine ⟨?_, ?_⟩
      · simp [addCfg, singleCfg]; omega
      · rw [decAt_addCfg_single_self]
        exact hrest
    · rcases S.diamond_step hki hsk.1 hstep.1 with ⟨hstep_c'_i, hstep_c1_k, hcomm⟩
      have h1 : S.Step c' i (S.fire c' i) := by
        rw [hsk.2]; exact hstep_c'_i
      rcases ih h1 hstab with ⟨hpos', hsteps'⟩
      have h2 : S.Step c₁ k (S.fire c' i) := by
        rw [hstep.2, hsk.2, hcomm]; exact hstep_c1_k
      refine ⟨?_, ?_⟩
      · simp [addCfg, singleCfg]; omega
      · rw [← decAt_addCfg_single_ne f' hki]
        exact Steps.step h2 hsteps'

theorem confluent_and_odometer_unique (S : AbelianToppleSys w) {c c₁ c₂ f₁ f₂ : Fin w → Nat}
    (h1 : S.Steps c f₁ c₁) (hs1 : S.IsStable c₁)
    (h2 : S.Steps c f₂ c₂) (hs2 : S.IsStable c₂) :
    c₁ = c₂ ∧ f₁ = f₂ := by
  induction h1 generalizing f₂ with
  | refl c =>
    cases h2 with
    | refl => exact ⟨rfl, rfl⟩
    | @step _ _ _ k _ hsk _ =>
      exfalso
      have hlt := hs1 k
      have hle := hsk.1
      omega
  | @step c c' c₁ i f₁' hsi hrest ih =>
    rcases S.abelian_exchange hsi h2 hs2 with ⟨hpos, h2'⟩
    rcases ih hs1 h2' with ⟨hceq, hfeq⟩
    refine ⟨hceq, ?_⟩
    rw [hfeq, addCfg_single_decAt f₂ i hpos]

/-! ### Constructive Stabilization from a `StrictPotential` Certificate -/

theorem stab_isStable (S : AbelianToppleSys w) (P : S.StrictPotential) (c : Fin w → Nat) :
    S.IsStable (S.stab P c) :=
  (S.stabilizeAux P (dot w c P.p) c (Nat.le_refl _)).property.1

theorem stab_steps (S : AbelianToppleSys w) (P : S.StrictPotential) (c : Fin w → Nat) :
    S.Steps c (S.odom P c) (S.stab P c) :=
  (S.stabilizeAux P (dot w c P.p) c (Nat.le_refl _)).property.2

theorem stab_eq_of_steps (S : AbelianToppleSys w) (P : S.StrictPotential) {c c' f : Fin w → Nat}
    (h : S.Steps c f c') (hs : S.IsStable c') :
    S.stab P c = c' ∧ S.odom P c = f :=
  S.confluent_and_odometer_unique (S.stab_steps P c) (S.stab_isStable P c) h hs

theorem stab_of_isStable (S : AbelianToppleSys w) (P : S.StrictPotential) {c : Fin w → Nat}
    (hs : S.IsStable c) : S.stab P c = c :=
  (S.stab_eq_of_steps P (Steps.refl c) hs).1

theorem odom_of_isStable (S : AbelianToppleSys w) (P : S.StrictPotential) {c : Fin w → Nat}
    (hs : S.IsStable c) : S.odom P c = zeroCfg w :=
  (S.stab_eq_of_steps P (Steps.refl c) hs).2

theorem stab_idem (S : AbelianToppleSys w) (P : S.StrictPotential) (c : Fin w → Nat) :
    S.stab P (S.stab P c) = S.stab P c :=
  S.stab_of_isStable P (S.stab_isStable P c)

theorem stab_add_left (S : AbelianToppleSys w) (P : S.StrictPotential) (c₁ c₂ : Fin w → Nat) :
    S.stab P (addCfg (S.stab P c₁) c₂) = S.stab P (addCfg c₁ c₂) := by
  have h1 : S.Steps (addCfg c₁ c₂) (S.odom P c₁) (addCfg (S.stab P c₁) c₂) :=
    (S.stab_steps P c₁).add_right c₂
  have h2 : S.Steps (addCfg (S.stab P c₁) c₂) (S.odom P (addCfg (S.stab P c₁) c₂))
                    (S.stab P (addCfg (S.stab P c₁) c₂)) :=
    S.stab_steps P (addCfg (S.stab P c₁) c₂)
  exact ((S.stab_eq_of_steps P (h1.trans h2) (S.stab_isStable P _)).1).symm

theorem stab_add_right (S : AbelianToppleSys w) (P : S.StrictPotential) (c₁ c₂ : Fin w → Nat) :
    S.stab P (addCfg c₁ (S.stab P c₂)) = S.stab P (addCfg c₁ c₂) := by
  rw [addCfg_comm c₁ (S.stab P c₂), S.stab_add_left P c₂ c₁, addCfg_comm]

theorem stab_add_both (S : AbelianToppleSys w) (P : S.StrictPotential) (c₁ c₂ : Fin w → Nat) :
    S.stab P (addCfg (S.stab P c₁) (S.stab P c₂)) = S.stab P (addCfg c₁ c₂) := by
  rw [S.stab_add_left, S.stab_add_right]

theorem stab_add_comm (S : AbelianToppleSys w) (P : S.StrictPotential) (c₁ c₂ : Fin w → Nat) :
    S.stab P (addCfg c₁ c₂) = S.stab P (addCfg c₂ c₁) := by
  rw [addCfg_comm]

theorem stab_add_assoc (S : AbelianToppleSys w) (P : S.StrictPotential) (c₁ c₂ c₃ : Fin w → Nat) :
    S.stab P (addCfg (S.stab P (addCfg c₁ c₂)) c₃) =
    S.stab P (addCfg c₁ (S.stab P (addCfg c₂ c₃))) := by
  rw [S.stab_add_left, S.stab_add_right, addCfg_assoc]

theorem odom_add_left (S : AbelianToppleSys w) (P : S.StrictPotential) (c₁ c₂ : Fin w → Nat) :
    S.odom P (addCfg c₁ c₂) = addCfg (S.odom P c₁) (S.odom P (addCfg (S.stab P c₁) c₂)) := by
  have h1 : S.Steps (addCfg c₁ c₂) (S.odom P c₁) (addCfg (S.stab P c₁) c₂) :=
    (S.stab_steps P c₁).add_right c₂
  have h2 := S.stab_steps P (addCfg (S.stab P c₁) c₂)
  exact (S.stab_eq_of_steps P (h1.trans h2) (S.stab_isStable P _)).2

theorem odom_add_law (S : AbelianToppleSys w) (P : S.StrictPotential) (c₁ c₂ : Fin w → Nat) :
    S.odom P (addCfg c₁ c₂) =
    addCfg (addCfg (S.odom P c₁) (S.odom P c₂))
           (S.odom P (addCfg (S.stab P c₁) (S.stab P c₂))) := by
  have h1 : S.Steps (addCfg c₁ c₂) (S.odom P c₁) (addCfg (S.stab P c₁) c₂) :=
    (S.stab_steps P c₁).add_right c₂
  have h2 : S.Steps (addCfg (S.stab P c₁) c₂) (S.odom P c₂) (addCfg (S.stab P c₁) (S.stab P c₂)) :=
    (S.stab_steps P c₂).add_left (S.stab P c₁)
  have h3 := S.stab_steps P (addCfg (S.stab P c₁) (S.stab P c₂))
  exact (S.stab_eq_of_steps P ((h1.trans h2).trans h3) (S.stab_isStable P _)).2

/-! ### Recurrence & 3-Line Odometer-Cancellation Burning Theorem -/

theorem maxStable_isRecurrent (S : AbelianToppleSys w) (P : S.StrictPotential) :
    S.IsRecurrent P S.maxStable :=
  ⟨S.maxStable_isStable, zeroCfg w, by rw [addCfg_zero_right]; exact S.stab_of_isStable P S.maxStable_isStable⟩

theorem stab_maxStable_add_isRecurrent (S : AbelianToppleSys w) (P : S.StrictPotential) (a : Fin w → Nat) :
    S.IsRecurrent P (S.stab P (addCfg S.maxStable a)) :=
  ⟨S.stab_isStable P _, a, rfl⟩

theorem recurrent_add_closed (S : AbelianToppleSys w) (P : S.StrictPotential) {c₁ c₂ : Fin w → Nat}
    (h1 : S.IsRecurrent P c₁) (h2 : S.IsRecurrent P c₂) :
    S.IsRecurrent P (S.stab P (addCfg c₁ c₂)) := by
  rcases h1 with ⟨_, a₁, rfl⟩
  rcases h2 with ⟨_, a₂, rfl⟩
  refine ⟨S.stab_isStable P _, addCfg a₁ (addCfg S.maxStable a₂), ?_⟩
  rw [S.stab_add_both, addCfg_assoc]

/-- Odometer-Cancellation Burning Theorem:
    If `μ + β ->^1 μ`, then EVERY recurrent configuration `c` burns via `c + β ->^1 c`. -/
theorem burning_necessity (S : AbelianToppleSys w) (P : S.StrictPotential) (beta : Fin w → Nat)
    (hburn_mu : S.Steps (addCfg S.maxStable beta) (oneCfg w) S.maxStable)
    {c : Fin w → Nat} (hrec : S.IsRecurrent P c) :
    S.Steps (addCfg c beta) (oneCfg w) c := by
  rcases hrec with ⟨hc_stab, a, rfl⟩
  let μ := S.maxStable
  have hway1 : S.Steps (addCfg (addCfg μ a) beta) (addCfg (oneCfg w) (S.odom P (addCfg μ a)))
                       (S.stab P (addCfg μ a)) := by
    have hcomm : addCfg (addCfg μ a) beta = addCfg (addCfg μ beta) a := by
      funext i; simp only [addCfg]; omega
    rw [hcomm]
    exact (hburn_mu.add_right a).trans (S.stab_steps P (addCfg μ a))
  have hway2 : S.Steps (addCfg (addCfg μ a) beta)
                       (addCfg (S.odom P (addCfg μ a)) (S.odom P (addCfg (S.stab P (addCfg μ a)) beta)))
                       (S.stab P (addCfg (S.stab P (addCfg μ a)) beta)) :=
    ((S.stab_steps P (addCfg μ a)).add_right beta).trans (S.stab_steps P _)
  have ⟨hceq, hfeq⟩ := S.confluent_and_odometer_unique hway1 hc_stab hway2 (S.stab_isStable P _)
  have hodom : S.odom P (addCfg (S.stab P (addCfg μ a)) beta) = oneCfg w := by
    funext i
    have hi := congrFun hfeq i
    simp only [addCfg, oneCfg] at hi ⊢
    omega
  have hst := S.stab_steps P (addCfg (S.stab P (addCfg μ a)) beta)
  rw [hodom, ← hceq] at hst
  exact hst

/-! ### Generic Harmonic-Bijection Sandpile Group Lifter (`HarmonicGroupCert`) -/

namespace HarmonicGroupCert

variable {S : AbelianToppleSys w} {P : S.StrictPotential} (C : S.HarmonicGroupCert P)

theorem Hval_stab (c : Fin w → Nat) : C.Hval (S.stab P c) % C.M = C.Hval c % C.M :=
  (C.Hbal.mod_invariant C.M C.H_mod_dvd (S.stab_steps P c)).symm

theorem Hval_add (c₁ c₂ : Fin w → Nat) :
    C.Hval (addCfg c₁ c₂) = C.Hval c₁ + C.Hval c₂ :=
  dot_add_left w c₁ c₂ C.Hbal.p

theorem Hval_add_gen (c : Fin w → Nat) (k : Nat) :
    C.Hval (addCfg c (singleCfg C.gen k)) % C.M = (C.Hval c + k) % C.M := by
  rw [C.Hval_add]
  unfold Hval
  rw [dot_single_left]
  rw [Nat.add_mod, Nat.mul_mod, C.gen_unit]
  rw [← Nat.mul_mod, Nat.mul_one, ← Nat.add_mod]

theorem decode_isRecurrent (r : Fin C.M) : S.IsRecurrent P (C.decode r) :=
  S.stab_maxStable_add_isRecurrent P _

theorem decode_Hval (r : Fin C.M) : C.Hval (C.decode r) % C.M = r.val := by
  unfold decode
  rw [C.Hval_stab, C.Hval_add_gen]
  have hmu_lt : C.Hval S.maxStable % C.M < C.M := Nat.mod_lt _ C.M_pos
  have hr_lt : r.val < C.M := r.isLt
  have h1 : (C.Hval S.maxStable + (r.val + C.M - C.Hval S.maxStable % C.M) % C.M) % C.M =
            (C.Hval S.maxStable % C.M + (r.val + C.M - C.Hval S.maxStable % C.M)) % C.M := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [Nat.add_mod (C.Hval S.maxStable % C.M), Nat.mod_mod, ← Nat.add_mod]
  rw [h1]
  have h2 : C.Hval S.maxStable % C.M + (r.val + C.M - C.Hval S.maxStable % C.M) = r.val + C.M := by
    omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hr_lt]

theorem recurrent_implies_Pred {c : Fin w → Nat} (hrec : S.IsRecurrent P c) : C.Pred c :=
  C.burn_implies_Pred c hrec.1 (S.burning_necessity P C.beta C.burn_mu hrec)

theorem Pred_implies_recurrent {c : Fin w → Nat} (hP : C.Pred c) : S.IsRecurrent P c := by
  let c' := C.decode (C.encode c)
  have hrec' : S.IsRecurrent P c' := C.decode_isRecurrent _
  have hP' : C.Pred c' := C.recurrent_implies_Pred hrec'
  have hHeq : C.Hval c' % C.M = C.Hval c % C.M := C.decode_Hval (C.encode c)
  have hceq : c' = c := C.H_inj_on_Pred c' c hP' hP hHeq
  rw [← hceq]
  exact hrec'

/-- Main Lifted Theorem 1: Exact Recurrence Characterization. -/
theorem recurrent_iff_Pred (c : Fin w → Nat) : S.IsRecurrent P c ↔ C.Pred c :=
  ⟨C.recurrent_implies_Pred, C.Pred_implies_recurrent⟩

/-- Main Lifted Theorem 2: Constructive Bijection `Recurrent ≃ Fin M` (Exact Count = M). -/
theorem encode_decode (r : Fin C.M) : C.encode (C.decode r) = r := by
  apply Fin.ext
  exact C.decode_Hval r

theorem decode_encode {c : Fin w → Nat} (hrec : S.IsRecurrent P c) :
    C.decode (C.encode c) = c := by
  have hrec' := C.decode_isRecurrent (C.encode c)
  exact C.H_inj_on_Pred _ _ (C.recurrent_implies_Pred hrec') (C.recurrent_implies_Pred hrec)
    (C.decode_Hval (C.encode c))

/-- Main Lifted Theorem 3: Exact Sandpile Group Homomorphism `(R, ⊕) ≅ (Z/MZ, +)`. -/
theorem harmonic_group_hom (c₁ c₂ : Fin w → Nat) :
    C.Hval (S.stab P (addCfg c₁ c₂)) % C.M = (C.Hval c₁ + C.Hval c₂) % C.M := by
  rw [C.Hval_stab, C.Hval_add]

theorem identity_isRecurrent : S.IsRecurrent P C.identity :=
  C.decode_isRecurrent ⟨0, C.M_pos⟩

theorem identity_Hval_mod : C.Hval C.identity % C.M = 0 :=
  C.decode_Hval ⟨0, C.M_pos⟩

theorem identity_add_right {c : Fin w → Nat} (hrec : S.IsRecurrent P c) :
    S.stab P (addCfg c C.identity) = c := by
  have hsum_rec := S.recurrent_add_closed P hrec C.identity_isRecurrent
  apply C.H_inj_on_Pred _ _ (C.recurrent_implies_Pred hsum_rec) (C.recurrent_implies_Pred hrec)
  change C.Hval (S.stab P (addCfg c C.identity)) % C.M = C.Hval c % C.M
  rw [C.harmonic_group_hom, Nat.add_mod, C.identity_Hval_mod, Nat.add_zero, Nat.mod_mod]

theorem identity_add_left {c : Fin w → Nat} (hrec : S.IsRecurrent P c) :
    S.stab P (addCfg C.identity c) = c := by
  rw [addCfg_comm]
  exact C.identity_add_right hrec

theorem identity_unique_of_Hval {e : Fin w → Nat} (hP : C.Pred e) (hH : C.Hval e % C.M = 0) :
    e = C.identity := by
  apply C.H_inj_on_Pred e C.identity hP (C.recurrent_implies_Pred C.identity_isRecurrent)
  change C.Hval e % C.M = C.Hval C.identity % C.M
  rw [hH, C.identity_Hval_mod]

theorem identity_unique_idempotent {e : Fin w → Nat} (hrec : S.IsRecurrent P e)
    (hidem : S.stab P (addCfg e e) = e) : e = C.identity := by
  have hmod : (C.Hval e + C.Hval e) % C.M = C.Hval e % C.M := by
    rw [← C.harmonic_group_hom, hidem]
  have hlt : C.Hval e % C.M < C.M := Nat.mod_lt _ C.M_pos
  have h2 : (C.Hval e % C.M + C.Hval e % C.M) % C.M = C.Hval e % C.M := by
    rw [← Nat.add_mod]; exact hmod
  have hzero : C.Hval e % C.M = 0 := by
    by_cases hsum : C.Hval e % C.M + C.Hval e % C.M < C.M
    · rw [Nat.mod_eq_of_lt hsum] at h2; omega
    · have hsub : C.Hval e % C.M + C.Hval e % C.M - C.M < C.M := by omega
      have hmod2 : (C.Hval e % C.M + C.Hval e % C.M) % C.M =
                   C.Hval e % C.M + C.Hval e % C.M - C.M := by
        have := Nat.mod_eq_sub_mod (a := C.Hval e % C.M + C.Hval e % C.M) (b := C.M) (by omega)
        rw [this, Nat.mod_eq_of_lt hsub]
      rw [hmod2] at h2; omega
  exact C.identity_unique_of_Hval (C.recurrent_implies_Pred hrec) hzero

theorem inv_isRecurrent (c : Fin w → Nat) : S.IsRecurrent P (C.inv c) :=
  C.decode_isRecurrent _

theorem add_inv {c : Fin w → Nat} (hrec : S.IsRecurrent P c) :
    S.stab P (addCfg c (C.inv c)) = C.identity := by
  have hsum_rec := S.recurrent_add_closed P hrec (C.inv_isRecurrent c)
  apply C.identity_unique_of_Hval (C.recurrent_implies_Pred hsum_rec)
  rw [C.harmonic_group_hom]
  unfold inv
  have hdec := C.decode_Hval ⟨(C.M - C.Hval c % C.M) % C.M, Nat.mod_lt _ C.M_pos⟩
  rw [Nat.add_mod, hdec]
  dsimp only
  have hlt : C.Hval c % C.M < C.M := Nat.mod_lt _ C.M_pos
  by_cases h0 : C.Hval c % C.M = 0
  · simp [h0]
  · have hlt2 : C.M - C.Hval c % C.M < C.M := by omega
    rw [Nat.mod_eq_of_lt hlt2]
    have hsum : C.Hval c % C.M + (C.M - C.Hval c % C.M) = C.M := by omega
    rw [hsum, Nat.mod_self]

end HarmonicGroupCert

end AbelianToppleSys

section CarryEcho

theorem repunit_zero (b : Nat) : repunit b 0 = 0 := rfl

theorem repunit_one (b : Nat) : repunit b 1 = 1 := by simp [repunit]

theorem repunit_mul_pred (b k : Nat) (hb : 1 ≤ b) : (b - 1) * repunit b k + 1 = b ^ k := by
  induction k with
  | zero => simp [repunit]
  | succ k ih =>
    rw [repunit_add_one, Nat.mul_add]
    have hmul : (b - 1) * b ^ k + b ^ k = b * b ^ k := by
      have h1 : (b - 1) * b ^ k + 1 * b ^ k = (b - 1 + 1) * b ^ k := (Nat.add_mul (b - 1) 1 (b ^ k)).symm
      rw [Nat.one_mul] at h1
      have h2 : b - 1 + 1 = b := by omega
      rw [h2] at h1
      exact h1
    rw [Nat.pow_succ']
    omega

theorem carryEcho_skew_conservation (b w : Nat) (hw : 0 < w) {c c' f : Fin w → Nat}
    (h : (carryEchoSys b w).Steps c f c') :
    skewWeight b w c = skewWeight b w c' + f ⟨w - 1, by omega⟩ * repunit b (w + 1) := by
  have hcons := (carryEchoHBal b w).conservation h
  change skewWeight b w c = skewWeight b w c' + dot w f (fun i => if i.val + 1 = w then repunit b (w + 1) else 0) at hcons
  rw [hcons]
  congr 1
  unfold dot
  let top : Fin w := ⟨w - 1, by omega⟩
  have hc : finSum w (fun i => f i * (if i.val + 1 = w then repunit b (w + 1) else 0)) =
            finSum w (fun i => if i = top then f top * repunit b (w + 1) else 0) := by
    apply finSum_congr
    intro i
    by_cases hit : i = top
    · subst hit
      have hv : top.val + 1 = w := by simp [top]; omega
      simp [hv]
    · have hv : i.val + 1 ≠ w := by
        intro hv; apply hit; exact Fin.ext (by simp [top]; omega)
      simp [hit, hv]
  rw [hc, finSum_single]

theorem carryEcho_first_moment_energy (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w)
    {c c' f : Fin w → Nat} (h : (carryEchoSys b w).Steps c f c') :
    firstMoment w c =
    firstMoment w c' + (b - 1) * finSum w f + (w + 1) * f ⟨w - 1, by omega⟩ := by
  have hcons := (carryEchoM1Pot b w hb).toLinearBalance.conservation h
  change firstMoment w c = firstMoment w c' +
         dot w f (fun i => if i.val + 1 = w then (b - 1) + (w + 1) else b - 1) at hcons
  rw [hcons]
  have hdot : dot w f (fun i => if i.val + 1 = w then (b - 1) + (w + 1) else b - 1) =
              (b - 1) * finSum w f + (w + 1) * f ⟨w - 1, by omega⟩ := by
    unfold dot
    let top : Fin w := ⟨w - 1, by omega⟩
    have hsplit : finSum w (fun i => f i * (if i.val + 1 = w then (b - 1) + (w + 1) else b - 1)) =
                  finSum w (fun i => (b - 1) * f i) +
                  finSum w (fun i => if i = top then (w + 1) * f top else 0) := by
      rw [← finSum_add]
      apply finSum_congr
      intro i
      by_cases hit : i = top
      · subst hit
        have hv : top.val + 1 = w := by simp [top]; omega
        simp only [hv, ite_true]
        rw [Nat.mul_add, Nat.mul_comm (f top) (b - 1), Nat.mul_comm (f top) (w + 1)]
      · have hv : i.val + 1 ≠ w := by
          intro hv; apply hit; exact Fin.ext (by simp [top]; omega)
        simp [hit, hv, Nat.mul_comm]
    rw [hsplit, finSum_mul_left, finSum_single]
  omega

/-- Exact Constant-Drop Total Avalanche Conservation Law:
    (b^{w+1} - 1) * (sum_i f_i) + Ψ_{b,w}(c') = Ψ_{b,w}(c). -/
theorem carryEcho_total_avalanche_law (b w : Nat) (hb : 2 ≤ b)
    {c c' f : Fin w → Nat} (h : (carryEchoSys b w).Steps c f c') :
    psiPotential b w c = psiPotential b w c' + finSum w f * (b ^ (w + 1) - 1) := by
  have hcons := (carryEchoPsiPot b w hb).toLinearBalance.conservation h
  change psiPotential b w c = psiPotential b w c' +
         dot w f (fun _ => (b - 1) * repunit b (w + 1)) at hcons
  rw [hcons]
  congr 1
  unfold dot
  rw [finSum_mul_right]
  have hrep := repunit_mul_pred b (w + 1) (by omega)
  have hsub : (b - 1) * repunit b (w + 1) = b ^ (w + 1) - 1 := by omega
  rw [hsub]

theorem carryEcho_total_avalanche_dvd (b w : Nat) (hb : 2 ≤ b)
    {c c' f : Fin w → Nat} (h : (carryEchoSys b w).Steps c f c') :
    (b ^ (w + 1) - 1) ∣ (psiPotential b w c - psiPotential b w c') := by
  have hlaw := carryEcho_total_avalanche_law b w hb h
  refine ⟨finSum w f, ?_⟩
  rw [Nat.mul_comm]
  omega

theorem carryEcho_value_conservation (b w : Nat) (hw : 2 ≤ w)
    {c c' f : Fin w → Nat} (h : (carryEchoSys b w).Steps c f c') :
    baseValue b w c = baseValue b w c' + f ⟨0, by omega⟩ + b ^ w * f ⟨w - 1, by omega⟩ := by
  have hcons := (carryEchoPhiBal b w hw).conservation h
  change baseValue b w c = baseValue b w c' +
         dot w f (fun i => (if i.val = 0 then 1 else 0) + (if i.val + 1 = w then b ^ w else 0)) at hcons
  rw [hcons]
  have hdot : dot w f (fun i => (if i.val = 0 then 1 else 0) + (if i.val + 1 = w then b ^ w else 0)) =
              f ⟨0, by omega⟩ + b ^ w * f ⟨w - 1, by omega⟩ := by
    unfold dot
    let bot : Fin w := ⟨0, by omega⟩
    let top : Fin w := ⟨w - 1, by omega⟩
    have hsplit : finSum w (fun i => f i * ((if i.val = 0 then 1 else 0) + (if i.val + 1 = w then b ^ w else 0))) =
                  finSum w (fun i => if i = bot then f bot else 0) +
                  finSum w (fun i => if i = top then b ^ w * f top else 0) := by
      rw [← finSum_add]
      apply finSum_congr
      intro i
      rw [Nat.mul_add]
      congr 1
      · by_cases hib : i = bot
        · subst hib; simp [bot]
        · have hv : i.val ≠ 0 := fun hv => hib (Fin.ext hv)
          simp [hib, hv]
      · by_cases hit : i = top
        · subst hit
          have hv : top.val + 1 = w := by simp [top]; omega
          simp [hv, Nat.mul_comm]
        · have hv : i.val + 1 ≠ w := fun hv => hit (Fin.ext (by simp [top]; omega))
          simp [hit, hv]
    rw [hsplit, finSum_single, finSum_single]
  omega

theorem carryEcho_mass_conservation (b w : Nat) (hw : 2 ≤ w)
    {c c' f : Fin w → Nat} (h : (carryEchoSys b w).Steps c f c') :
    chipMass w c = chipMass w c' + b * f ⟨0, by omega⟩ + f ⟨w - 1, by omega⟩ := by
  have hcons := (carryEchoMassBal b w hw).conservation h
  have hcm : ∀ x : Fin w → Nat, dot w x (fun _ => 1) = chipMass w x := by
    intro x; unfold dot chipMass; apply finSum_congr; intro i; exact Nat.mul_one (x i)
  change dot w c (fun _ => 1) = dot w c' (fun _ => 1) +
         dot w f (fun i => (if i.val = 0 then b else 0) + (if i.val + 1 = w then 1 else 0)) at hcons
  rw [hcm c, hcm c'] at hcons
  rw [hcons]
  have hdot : dot w f (fun i => (if i.val = 0 then b else 0) + (if i.val + 1 = w then 1 else 0)) =
              b * f ⟨0, by omega⟩ + f ⟨w - 1, by omega⟩ := by
    unfold dot
    let bot : Fin w := ⟨0, by omega⟩
    let top : Fin w := ⟨w - 1, by omega⟩
    have hsplit : finSum w (fun i => f i * ((if i.val = 0 then b else 0) + (if i.val + 1 = w then 1 else 0))) =
                  finSum w (fun i => if i = bot then b * f bot else 0) +
                  finSum w (fun i => if i = top then f top else 0) := by
      rw [← finSum_add]
      apply finSum_congr
      intro i
      rw [Nat.mul_add]
      congr 1
      · by_cases hib : i = bot
        · subst hib
          change f bot * (if (0 : Nat) = 0 then b else 0) = if bot = bot then b * f bot else 0
          simp [Nat.mul_comm]
        · have hv : i.val ≠ 0 := fun hv => hib (Fin.ext hv)
          simp [hib, hv]
      · by_cases hit : i = top
        · subst hit
          have hv : top.val + 1 = w := by simp [top]; omega
          simp [hv]
        · have hv : i.val + 1 ≠ w := fun hv => hit (Fin.ext (by simp [top]; omega))
          simp [hit, hv]
    rw [hsplit, finSum_single, finSum_single]
  omega

/-! ### Unit Burning Wave & Skew-Base-b Duality for E_{b, w} -/

/-- Theorem 1A (Exact Recurrence ↔ Dual Canonical Skew-Base-b, ∀ b ≥ 2, ∀ w ≥ 1). -/
theorem carryEcho_recurrent_iff_dualSkew (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) (c : Fin w → Nat) :
    (carryEchoSys b w).IsRecurrent (carryEchoM1Pot b w hb) c ↔ IsDualSkew b w c :=
  (carryEchoGroupCert b w hb hw).recurrent_iff_Pred c

/-- Theorem 1B (Exact Recurrent Count = R_{b, w+1} via Constructive Bijection, ∀ b ≥ 2, ∀ w ≥ 1). -/
theorem carryEcho_recurrent_count_left (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w)
    (r : Fin (repunit b (w + 1))) :
    (carryEchoGroupCert b w hb hw).encode ((carryEchoGroupCert b w hb hw).decode r) = r :=
  (carryEchoGroupCert b w hb hw).encode_decode r

theorem carryEcho_recurrent_count_right (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w)
    {c : Fin w → Nat} (hrec : (carryEchoSys b w).IsRecurrent (carryEchoM1Pot b w hb) c) :
    (carryEchoGroupCert b w hb hw).decode ((carryEchoGroupCert b w hb hw).encode c) = c :=
  (carryEchoGroupCert b w hb hw).decode_encode hrec

/-- Theorem 1C (Exact Cyclic Group Isomorphism (R_{b,w}, ⊕) ≅ Z/R_{b,w+1}Z, ∀ b ≥ 2, ∀ w ≥ 1). -/
theorem carryEcho_group_hom (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) (c₁ c₂ : Fin w → Nat) :
    skewWeight b w ((carryEchoSys b w).stab (carryEchoM1Pot b w hb) (addCfg c₁ c₂)) % repunit b (w + 1) =
    (skewWeight b w c₁ + skewWeight b w c₂) % repunit b (w + 1) :=
  (carryEchoGroupCert b w hb hw).harmonic_group_hom c₁ c₂

/-! ### Constructive Greedy Skew-Base-b Encoder & Explicit Closed-Form Identity Element -/

theorem skewEncode_zero (b w : Nat) : skewEncode b w 0 = zeroCfg w := by
  induction w with
  | zero => funext i; exact Fin.elim0 i
  | succ w ih =>
    funext i
    unfold skewEncode zeroCfg
    dsimp only
    by_cases h : i.val < w
    · simp only [h, dite_true, Nat.zero_mod]
      rw [ih]; rfl
    · simp [h]

theorem skewEncode_spec {b : Nat} (_hb : 2 ≤ b) (w n : Nat) (hn : n < repunit b (w + 1)) :
    IsSkewCanon b w (skewEncode b w n) ∧ skewWeight b w (skewEncode b w n) = n := by
  induction w generalizing n with
  | zero =>
    refine ⟨⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, ?_⟩
    simp [repunit] at hn
    unfold skewWeight dot finSum
    omega
  | succ w ih =>
    let r := repunit b (w + 1)
    have hr_pos : 0 < r := repunit_pos b (w + 1) (Nat.succ_pos w)
    have hrep : repunit b (w + 1 + 1) = b * r + 1 := rfl
    have hq_le : n / r ≤ b := by
      have : n ≤ b * r := by omega
      have hdiv := Nat.div_le_div_right (c := r) this
      rw [Nat.mul_div_cancel b hr_pos] at hdiv
      exact hdiv
    have hrem_lt : n % r < r := Nat.mod_lt n hr_pos
    rcases ih (n % r) hrem_lt with ⟨hcan_low, hwt_low⟩
    have hcan : IsSkewCanon b (w + 1) (skewEncode b (w + 1) n) := by
      refine ⟨?_, ?_⟩
      · intro i
        unfold skewEncode
        dsimp only
        by_cases h : i.val < w
        · simp only [h, dite_true]; exact hcan_low.1 ⟨i.val, h⟩
        · simp only [h, dite_false]; exact hq_le
      · intro i j hij hjb
        unfold skewEncode at hjb ⊢
        dsimp only at hjb ⊢
        by_cases hj : j.val < w
        · have hi : i.val < w := by omega
          simp only [hj, dite_true] at hjb
          simp only [hi, dite_true]
          exact hcan_low.2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij hjb
        · have hi : i.val < w := by omega
          simp only [hj, dite_false] at hjb
          simp only [hi, dite_true]
          have hdiv_eq := Nat.div_add_mod n r
          have hrem0 : n % r = 0 := by
            have hmul : r * (n / r) = b * r := by rw [hjb, Nat.mul_comm]
            omega
          rw [hrem0, skewEncode_zero]; rfl
    have hwt : skewWeight b (w + 1) (skewEncode b (w + 1) n) = n := by
      unfold skewWeight dot finSum
      dsimp only
      have hlow_eq : finSum w (fun i : Fin w => skewEncode b (w + 1) n i.castSucc * repunit b (i.castSucc.val + 1)) =
                     skewWeight b w (skewEncode b w (n % r)) := by
        unfold skewWeight dot
        apply finSum_congr
        intro i
        have hstep : skewEncode b (w + 1) n i.castSucc = skewEncode b w (n % r) i := by
          rw [skewEncode]
          dsimp only
          have hilt : i.castSucc.val < w := i.isLt
          rw [dite_eq_left_of_eq_true (eq_true hilt)]
          rfl
        rw [hstep, Fin.val_castSucc]
      rw [hlow_eq, hwt_low]
      have htop_eq : skewEncode b (w + 1) n ⟨w, Nat.lt_succ_self w⟩ = n / r := by
        rw [skewEncode]
        dsimp only
        have hnot : ¬ (w < w) := Nat.lt_irrefl w
        rw [dite_eq_right_of_eq_false (eq_false hnot)]
      rw [htop_eq]
      have hdm := Nat.div_add_mod n r
      rw [Nat.mul_comm] at hdm
      change n % r + (n / r) * r = n
      omega
    exact ⟨hcan, hwt⟩

/-- Theorem 1D (Exact Closed-Form Identity Element Theorem, ∀ b ≥ 2, ∀ w ≥ 1). -/
theorem carryEcho_explicitIdentity_eq (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) :
    explicitIdentity b w = (carryEchoGroupCert b w hb hw).identity := by
  let M := repunit b (w + 1)
  have hMpos : 0 < M := repunit_pos b (w + 1) (Nat.succ_pos w)
  let hmu := skewWeight b w (carryEchoSys b w).maxStable
  have hrem_lt : hmu % M < M := Nat.mod_lt hmu hMpos
  rcases skewEncode_spec hb w (hmu % M) hrem_lt with ⟨hcan, hwt⟩
  have hdual : IsDualSkew b w (explicitIdentity b w) := by
    refine ⟨fun i => Nat.sub_le b _, ?_⟩
    intro i j hij hje0
    change b - skewEncode b w (hmu % M) j = 0 at hje0
    change b - skewEncode b w (hmu % M) i = b
    have hle_j := hcan.1 j
    have hdj : skewEncode b w (hmu % M) j = b := by omega
    have hdi : skewEncode b w (hmu % M) i = 0 := hcan.2 i j hij hdj
    omega
  have hdual_back : dualCfg b w (explicitIdentity b w) = skewEncode b w (hmu % M) := by
    funext i
    change b - (b - skewEncode b w (hmu % M) i) = skewEncode b w (hmu % M) i
    have hle_i := hcan.1 i
    omega
  have hadd := dualCfg_skewWeight_add hdual.1
  rw [hdual_back, hwt] at hadd
  have hHmod : skewWeight b w (explicitIdentity b w) % M = 0 := by
    have hdiv := Nat.div_add_mod hmu M
    change skewWeight b w (explicitIdentity b w) + hmu % M = hmu at hadd
    have hEq : skewWeight b w (explicitIdentity b w) = M * (hmu / M) := by omega
    rw [hEq, Nat.mul_mod_right]
  exact (carryEchoGroupCert b w hb hw).identity_unique_of_Hval hdual hHmod

/-! ### Exact Closed-Form Identity Value & Self-Addition Avalanche Laws (∀ b ≥ 2, ∀ w ≥ 2) -/

theorem skewWeight_one_formula (b w : Nat) (hb : 2 ≤ b) :
    (b - 1) * skewWeight b w (oneCfg w) + (w + 1) = repunit b (w + 1) := by
  induction w with
  | zero =>
    unfold skewWeight dot finSum
    simp [repunit]
  | succ w ih =>
    have hstep : skewWeight b (w + 1) (oneCfg (w + 1)) =
                 skewWeight b w (oneCfg w) + repunit b (w + 1) := by
      unfold skewWeight dot oneCfg
      rw [finSum]
      simp only [Nat.one_mul, Fin.val_castSucc]
    rw [hstep, Nat.mul_add]
    have hrep := repunit_mul_pred b (w + 1) (by omega)
    have hadd1 := repunit_add_one b (w + 1)
    omega

theorem skewWeight_maxStable_formula (b w : Nat) (hb : 2 ≤ b) :
    (b - 1) * skewWeight b w (carryEchoSys b w).maxStable + b * (w + 1) =
    b * repunit b (w + 1) := by
  have hmu_eq : skewWeight b w (carryEchoSys b w).maxStable = b * skewWeight b w (oneCfg w) := by
    unfold skewWeight dot AbelianToppleSys.maxStable carryEchoSys oneCfg
    rw [← finSum_mul_left]
    apply finSum_congr
    intro i
    simp
  rw [hmu_eq]
  have h1 := skewWeight_one_formula b w hb
  have h2 := congrArg (b * ·) h1
  rw [Nat.mul_add] at h2
  have hassoc : (b - 1) * (b * skewWeight b w (oneCfg w)) =
                b * ((b - 1) * skewWeight b w (oneCfg w)) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (b - 1) b, Nat.mul_assoc]
  omega

theorem mul_succ_le_repunit {b : Nat} (hb : 2 ≤ b) (w : Nat) (hw : 2 ≤ w) :
    b * (w + 1) ≤ repunit b (w + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, w = 2 + d := ⟨w - 2, by omega⟩
  induction d with
  | zero =>
    simp only [Nat.add_zero, repunit]
    have h1 : b * 3 = b + b + b := by rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_one]
    have h2 : b * (b * (b * 0 + 1) + 1) + 1 = b * b + b + 1 := by
      simp [Nat.mul_add]
    have hsq : 2 * b ≤ b * b := Nat.mul_le_mul_right b hb
    omega
  | succ d ih =>
    have hstep : 2 + (d + 1) + 1 = (2 + d + 1) + 1 := by omega
    rw [hstep, repunit_add_one, Nat.mul_add, Nat.mul_one]
    have hpow : b ≤ b ^ (2 + d + 1) := by
      have : b ^ 1 ≤ b ^ (2 + d + 1) := pow_mono (by omega) (by omega)
      simpa using this
    omega

/-- Theorem 1E (Exact Identity Weight & Self-Addition Avalanche Laws, ∀ b ≥ 2, ∀ w ≥ 2):
    For ALL b ≥ 2 and w ≥ 2, letting e = e_{b,w} and f = odom(e + e):
      1. H_b(e) = R_{b, w+1}  (exact, not just mod R_{b, w+1}!)
      2. f(w - 1) = 1         (the MSB fires EXACTLY ONCE during 2e →* e!)
      3. (b - 1) * ∑ f_i + (w + 1) = M_1(e)
      4. W(e) = b * f(0) + 1  (mass of e is ALWAYS ≡ 1 mod b; ODD for binary b = 2!)
      5. Φ_b(e) = b^w + f(0)  (exact base-b numeric value of e!) -/
theorem carryEcho_identity_laws_ge2 (b w : Nat) (hb : 2 ≤ b) (hw : 2 ≤ w) :
    let S := carryEchoSys b w
    let P := carryEchoM1Pot b w hb
    let e := explicitIdentity b w
    let f := S.odom P (addCfg e e)
    skewWeight b w e = repunit b (w + 1) ∧
    f ⟨w - 1, by omega⟩ = 1 ∧
    (b - 1) * finSum w f + (w + 1) = firstMoment w e ∧
    chipMass w e = b * f ⟨0, by omega⟩ + 1 ∧
    baseValue b w e = b ^ w + f ⟨0, by omega⟩ := by
  intro S P e f
  let M := repunit b (w + 1)
  have hMpos : 0 < M := repunit_pos b (w + 1) (Nat.succ_pos w)
  let hmu := skewWeight b w S.maxStable
  have hform : (b - 1) * hmu + b * (w + 1) = b * M := skewWeight_maxStable_formula b w hb
  have hle_rep : b * (w + 1) ≤ M := mul_succ_le_repunit hb w hw
  have hM_le_hmu : M ≤ hmu := by
    have hmul : (b - 1) * M ≤ (b - 1) * hmu := by
      have h1 : (b - 1) * M + M = b * M := by
        have := (Nat.add_mul (b - 1) 1 M).symm
        rw [Nat.one_mul] at this
        have hb1 : b - 1 + 1 = b := by omega
        rw [hb1] at this; exact this
      omega
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  have hhmu_lt_2M : hmu < 2 * M := by
    have hmul : (b - 1) * hmu < (b - 1) * (2 * M) := by
      have h1 : b * M ≤ (b - 1) * (2 * M) := by
        have h2 : (b - 1) * (2 * M) = (2 * b - 2) * M := by
          rw [← Nat.mul_assoc]; congr 1; omega
        rw [h2]
        exact Nat.mul_le_mul_right M (by omega)
      have hpos : 0 < b * (w + 1) := Nat.mul_pos (by omega) (Nat.succ_pos w)
      omega
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hdiv1 : hmu / M = 1 := by
    have hdm : M * (hmu / M) + hmu % M = hmu := Nat.div_add_mod hmu M
    have hmod_lt : hmu % M < M := Nat.mod_lt hmu hMpos
    by_cases h0 : hmu / M = 0
    · rw [h0, Nat.mul_zero, Nat.zero_add] at hdm; omega
    · by_cases h2 : 2 ≤ hmu / M
      · have hle2 : M * 2 ≤ M * (hmu / M) := Nat.mul_le_mul_left M h2
        have hcomm : M * 2 = 2 * M := Nat.mul_comm M 2
        omega
      · have hge1 : 1 ≤ hmu / M := Nat.pos_of_ne_zero h0
        have hlt2 : hmu / M < 2 := Nat.lt_of_not_le h2
        exact Nat.le_antisymm (Nat.le_of_lt_succ hlt2) hge1
  -- Compute H_b(e) = M * (hmu / M) = M
  rcases skewEncode_spec hb w (hmu % M) (Nat.mod_lt hmu hMpos) with ⟨hcan, hwt⟩
  have hle_e : ∀ i, e i ≤ b := fun i => by change b - skewEncode b w (hmu % M) i ≤ b; omega
  have hdual_back : dualCfg b w e = skewEncode b w (hmu % M) := by
    funext i; unfold dualCfg; change b - (b - skewEncode b w (hmu % M) i) = skewEncode b w (hmu % M) i
    have := hcan.1 i; omega
  have hadd_e := dualCfg_skewWeight_add hle_e
  rw [hdual_back, hwt] at hadd_e
  change skewWeight b w e + hmu % M = hmu at hadd_e
  have hHe : skewWeight b w e = M := by
    have hdm := Nat.div_add_mod hmu M
    rw [hdiv1, Nat.mul_one] at hdm
    omega
  -- Idempotence: stab (e + e) = e
  have hid_eq : e = (carryEchoGroupCert b w hb (by omega)).identity :=
    carryEcho_explicitIdentity_eq b w hb (by omega)
  have hstab_ee : S.stab P (addCfg e e) = e := by
    rw [hid_eq]; exact (carryEchoGroupCert b w hb (by omega)).identity_add_right
      (carryEchoGroupCert b w hb (by omega)).identity_isRecurrent
  have hsteps_ee : S.Steps (addCfg e e) f e := by
    have hs := S.stab_steps P (addCfg e e)
    rw [hstab_ee] at hs
    exact hs
  -- 1. MSB firing count f(w - 1) = 1
  have hskew := carryEcho_skew_conservation b w (by omega) hsteps_ee
  have hskew_2e : skewWeight b w (addCfg e e) = skewWeight b w e + skewWeight b w e :=
    dot_add_left w e e _
  rw [hskew_2e, hHe] at hskew
  change M + M = M + f ⟨w - 1, by omega⟩ * M at hskew
  have hfw : f ⟨w - 1, by omega⟩ = 1 := by
    have h1 : M = f ⟨w - 1, by omega⟩ * M := by omega
    have h2 : 1 * M = f ⟨w - 1, by omega⟩ * M := by rw [Nat.one_mul]; exact h1
    exact (Nat.eq_of_mul_eq_mul_right hMpos h2).symm
  -- 2. First-moment avalanche work
  have hm1 := carryEcho_first_moment_energy b w hb (by omega) hsteps_ee
  have hm1_2e : firstMoment w (addCfg e e) = firstMoment w e + firstMoment w e :=
    dot_add_left w e e _
  rw [hm1_2e, hfw, Nat.mul_one] at hm1
  -- 3. Chip mass
  have hmass := carryEcho_mass_conservation b w hw hsteps_ee
  have hmass_2e : chipMass w (addCfg e e) = chipMass w e + chipMass w e :=
    finSum_add w e e
  rw [hmass_2e, hfw] at hmass
  -- 4. Base-b value
  have hval := carryEcho_value_conservation b w hw hsteps_ee
  have hval_2e : baseValue b w (addCfg e e) = baseValue b w e + baseValue b w e :=
    dot_add_left w e e _
  rw [hval_2e, hfw, Nat.mul_one] at hval
  exact ⟨hHe, hfw, by omega, by omega, by omega⟩

end CarryEcho

section DirectedCarry

/-- Theorem 2A (Directed Carry Recurrence & Zero Identity, ∀ b ≥ 2, ∀ w ≥ 1). -/
theorem directedCarry_all_stable_recurrent (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) (c : Fin w → Nat) :
    (directedCarrySys b w hb).IsRecurrent (directedCarryMassPot b w hb) c ↔
    (directedCarrySys b w hb).IsStable c :=
  (directedCarryGroupCert b w hb hw).recurrent_iff_Pred c

theorem directedCarry_identity_is_zero (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) :
    zeroCfg w = (directedCarryGroupCert b w hb hw).identity := by
  apply (directedCarryGroupCert b w hb hw).identity_unique_of_Hval
  · intro i; simp [zeroCfg, directedCarrySys]; omega
  · change baseValue b w (zeroCfg w) % b ^ w = 0
    rw [baseValue, dot_zero_left, Nat.zero_mod]

/-- Theorem 2B (Exact Legendre/Kummer Carry-Avalanche Energy Conservation, ∀ b ≥ 2, ∀ w ≥ 1). -/
theorem directedCarry_kummer_conservation (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w)
    {c c' f : Fin w → Nat} (h : (directedCarrySys b w hb).Steps c f c') :
    chipMass w c = chipMass w c' + (b - 1) * finSum w f + f ⟨w - 1, by omega⟩ := by
  have hcons := (directedCarryMassPot b w hb).toLinearBalance.conservation h
  have hcm : ∀ x : Fin w → Nat, dot w x (fun _ => 1) = chipMass w x := by
    intro x; unfold dot chipMass; apply finSum_congr; intro i; exact Nat.mul_one (x i)
  change dot w c (fun _ => 1) = dot w c' (fun _ => 1) +
         dot w f (fun i => if i.val + 1 = w then b else b - 1) at hcons
  rw [hcm c, hcm c'] at hcons
  rw [hcons]
  have hdot : dot w f (fun i => if i.val + 1 = w then b else b - 1) =
              (b - 1) * finSum w f + f ⟨w - 1, by omega⟩ := by
    unfold dot
    let top : Fin w := ⟨w - 1, by omega⟩
    have hsplit : finSum w (fun i => f i * (if i.val + 1 = w then b else b - 1)) =
                  finSum w (fun i => (b - 1) * f i) +
                  finSum w (fun i => if i = top then f top else 0) := by
      rw [← finSum_add]
      apply finSum_congr
      intro i
      by_cases hit : i = top
      · subst hit
        have hv : top.val + 1 = w := by simp [top]; omega
        simp only [hv, ite_true]
        have hmul : (b - 1) * f top + f top = b * f top := by
          have := (Nat.add_mul (b - 1) 1 (f top)).symm
          rw [Nat.one_mul] at this
          have hb1 : b - 1 + 1 = b := by omega
          rw [hb1] at this; exact this
        rw [Nat.mul_comm (f top) b, hmul]
      · have hv : i.val + 1 ≠ w := fun hv => hit (Fin.ext (by simp [top]; omega))
        simp [hit, hv, Nat.mul_comm]
    rw [hsplit, finSum_mul_left, finSum_single]
  omega

end DirectedCarry

section WitnessesAndSharpness

theorem nonvacuity_certs_inhabited (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) :
    Nonempty ((carryEchoSys b w).StrictPotential) ∧
    Nonempty ((carryEchoSys b w).HarmonicGroupCert (carryEchoM1Pot b w hb)) ∧
    Nonempty ((directedCarrySys b w hb).HarmonicGroupCert (directedCarryMassPot b w hb)) :=
  ⟨⟨carryEchoM1Pot b w hb⟩, ⟨carryEchoGroupCert b w hb hw⟩, ⟨directedCarryGroupCert b w hb hw⟩⟩

/-- Concrete kernel-checked witness: b=2, w=2 => e_{2,2} = [1, 2], H_2 = 7, f(2e->e) = [1, 1]. -/
theorem witness_carryEcho_b2_w2 :
    (∀ i : Fin 2, explicitIdentity 2 2 i = vec2 1 2 i) ∧
    skewWeight 2 2 (explicitIdentity 2 2) = 7 ∧
    (∀ i : Fin 2, (carryEchoSys 2 2).odom (carryEchoM1Pot 2 2 (by omega))
                    (addCfg (explicitIdentity 2 2) (explicitIdentity 2 2)) i = vec2 1 1 i) := by
  refine ⟨by decide, by decide, by decide⟩

/-- Concrete kernel-checked witness: b=2, w=3 => e_{2,3} = [2, 2, 1], H_2 = 15, f(2e->e) = [2, 2, 1]. -/
theorem witness_carryEcho_b2_w3 :
    (∀ i : Fin 3, explicitIdentity 2 3 i = vec3 2 2 1 i) ∧
    skewWeight 2 3 (explicitIdentity 2 3) = 15 ∧
    (∀ i : Fin 3, (carryEchoSys 2 3).odom (carryEchoM1Pot 2 3 (by omega))
                    (addCfg (explicitIdentity 2 3) (explicitIdentity 2 3)) i = vec3 2 2 1 i) := by
  refine ⟨by decide, by decide, by decide⟩

/-- Concrete kernel-checked witness: b=2, w=4 => e_{2,4} = [2, 0, 2, 1], H_2 = 31, f(2e->e) = [2, 2, 2, 1]. -/
theorem witness_carryEcho_b2_w4 :
    (∀ i : Fin 4, explicitIdentity 2 4 i = vec4 2 0 2 1 i) ∧
    skewWeight 2 4 (explicitIdentity 2 4) = 31 ∧
    (∀ i : Fin 4, (carryEchoSys 2 4).odom (carryEchoM1Pot 2 4 (by omega))
                    (addCfg (explicitIdentity 2 4) (explicitIdentity 2 4)) i = vec4 2 2 2 1 i) := by
  refine ⟨by decide, by decide, by decide⟩

/-- Concrete kernel-checked witness: b=2, w=5 => e_{2,5} = [0, 1, 2, 1, 1], H_2 = 63, f(2e->e) = [2, 3, 3, 2, 1]. -/
theorem witness_carryEcho_b2_w5 :
    (∀ i : Fin 5, explicitIdentity 2 5 i = vec5 0 1 2 1 1 i) ∧
    skewWeight 2 5 (explicitIdentity 2 5) = 63 ∧
    (∀ i : Fin 5, (carryEchoSys 2 5).odom (carryEchoM1Pot 2 5 (by omega))
                    (addCfg (explicitIdentity 2 5) (explicitIdentity 2 5)) i = vec5 2 3 3 2 1 i) := by
  refine ⟨by decide, by decide, by decide⟩

/-- Concrete kernel-checked witness: b=3, w=3 => e_{3,3} = [2, 3, 2], H_3 = 40, f(2e->e) = [2, 2, 1]. -/
theorem witness_carryEcho_b3_w3 :
    (∀ i : Fin 3, explicitIdentity 3 3 i = vec3 2 3 2 i) ∧
    skewWeight 3 3 (explicitIdentity 3 3) = 40 ∧
    (∀ i : Fin 3, (carryEchoSys 3 3).odom (carryEchoM1Pot 3 3 (by omega))
                    (addCfg (explicitIdentity 3 3) (explicitIdentity 3 3)) i = vec3 2 2 1 i) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### 5.2 Kernel-Checked Sharpness Counterexamples -/

/-- Counterexample C1 (Sharpness of `w ≥ 2` in Theorem 1E):
    At w = 1, b = 2, e_{2,1} = [0] has H_2(e_{2,1}) = 0 ≠ R_{2,2} = 3 and f_{2e->e}(0) = 0 ≠ 1. -/
theorem sharpness_w1_boundary :
    explicitIdentity 2 1 ⟨0, by omega⟩ = 0 ∧
    skewWeight 2 1 (explicitIdentity 2 1) ≠ repunit 2 2 ∧
    (carryEchoSys 2 1).odom (carryEchoM1Pot 2 1 (by omega))
      (addCfg (explicitIdentity 2 1) (explicitIdentity 2 1)) ⟨0, by omega⟩ = 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Counterexample C2 (Recurrence is essential for identity uniqueness):
    At b = 2, w = 2, the zero configuration 0 = [0, 0] is stable and idempotent (0 ⊕ 0 = 0),
    yet NOT recurrent in E_{2, 2}. -/
theorem sharpness_zero_nonrecurrent_idempotent :
    (carryEchoSys 2 2).IsStable (zeroCfg 2) ∧
    (carryEchoSys 2 2).stab (carryEchoM1Pot 2 2 (by omega)) (addCfg (zeroCfg 2) (zeroCfg 2)) = zeroCfg 2 ∧
    ¬ (carryEchoSys 2 2).IsRecurrent (carryEchoM1Pot 2 2 (by omega)) (zeroCfg 2) := by
  refine ⟨fun i => by simp [zeroCfg, carryEchoSys], ?_, ?_⟩
  · rw [addCfg_zero_left]
    exact (carryEchoSys 2 2).stab_of_isStable (carryEchoM1Pot 2 2 (by omega))
      (fun i => by simp [zeroCfg, carryEchoSys])
  · intro hrec
    have hdual : IsDualSkew 2 2 (zeroCfg 2) :=
      (carryEcho_recurrent_iff_dualSkew 2 2 (by omega) (by omega) (zeroCfg 2)).mp hrec
    have hlt : (⟨0, by omega⟩ : Fin 2).val < (⟨1, by omega⟩ : Fin 2).val := by decide
    have h0 := hdual.2 ⟨0, by omega⟩ ⟨1, by omega⟩ hlt rfl
    simp [zeroCfg] at h0

/-- Counterexample C3 (Single-bit skew-base-b violation fails recurrence):
    At b = 2, w = 2, c = [1, 0] is stable (every digit ≤ 2) yet violates `c 0 = 2` below `c 1 = 0`,
    hence is NOT recurrent. -/
theorem sharpness_single_skew_violation :
    (carryEchoSys 2 2).IsStable (vec2 1 0) ∧
    ¬ (carryEchoSys 2 2).IsRecurrent (carryEchoM1Pot 2 2 (by omega)) (vec2 1 0) := by
  refine ⟨fun i => by unfold vec2 carryEchoSys; dsimp only; split <;> omega, ?_⟩
  intro hrec
  have hdual : IsDualSkew 2 2 (vec2 1 0) :=
    (carryEcho_recurrent_iff_dualSkew 2 2 (by omega) (by omega) (vec2 1 0)).mp hrec
  have hlt : (⟨0, by omega⟩ : Fin 2).val < (⟨1, by omega⟩ : Fin 2).val := by decide
  have h0 := hdual.2 ⟨0, by omega⟩ ⟨1, by omega⟩ hlt rfl
  simp [vec2] at h0

theorem sharpness_cyclic_no_strict_potential :
    cyclicCarryEcho2.StrictPotential → False := by
  intro P
  have h0 := P.balance ⟨0, by omega⟩
  have h1 := P.balance ⟨1, by omega⟩
  have hp0 := P.delta_pos ⟨0, by omega⟩
  have hp1 := P.delta_pos ⟨1, by omega⟩
  have hd0 : dot 2 (fun j => cyclicCarryEcho2.A ⟨0, by omega⟩ j) P.p = 3 * P.p ⟨1, by omega⟩ := by
    change ((0 + (if (⟨0, by omega⟩ : Fin 2) = ⟨0, by omega⟩ then 0 else 3) * P.p ⟨0, by omega⟩) +
            (if (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ then 0 else 3) * P.p ⟨1, by omega⟩) =
           3 * P.p ⟨1, by omega⟩
    simp
  have hd1 : dot 2 (fun j => cyclicCarryEcho2.A ⟨1, by omega⟩ j) P.p = 3 * P.p ⟨0, by omega⟩ := by
    change ((0 + (if (⟨1, by omega⟩ : Fin 2) = ⟨0, by omega⟩ then 0 else 3) * P.p ⟨0, by omega⟩) +
            (if (⟨1, by omega⟩ : Fin 2) = ⟨1, by omega⟩ then 0 else 3) * P.p ⟨1, by omega⟩) =
           3 * P.p ⟨0, by omega⟩
    simp
  rw [hd0] at h0
  rw [hd1] at h1
  change 3 * P.p ⟨0, by omega⟩ = P.delta ⟨0, by omega⟩ + 3 * P.p ⟨1, by omega⟩ at h0
  change 3 * P.p ⟨1, by omega⟩ = P.delta ⟨1, by omega⟩ + 3 * P.p ⟨0, by omega⟩ at h1
  omega

theorem sharpness_cyclic_infinite_cycle (n : Nat) :
    cyclicCarryEcho2.Steps (vec2 3 0) (vec2 n n) (vec2 3 0) := by
  induction n with
  | zero =>
    have h0 : vec2 0 0 = zeroCfg 2 := by funext i; unfold vec2 zeroCfg; split <;> rfl
    rw [h0]; exact AbelianToppleSys.Steps.refl _
  | succ n ih =>
    have hs0 : cyclicCarryEcho2.Step (vec2 3 0) ⟨0, by omega⟩ (vec2 0 3) := by
      refine ⟨by decide, ?_⟩
      funext j
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    have hs1 : cyclicCarryEcho2.Step (vec2 0 3) ⟨1, by omega⟩ (vec2 3 0) := by
      refine ⟨by decide, ?_⟩
      funext j
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    have hcycle : cyclicCarryEcho2.Steps (vec2 3 0) (vec2 1 1) (vec2 3 0) := by
      have h2 := AbelianToppleSys.Steps.step hs0 (AbelianToppleSys.Steps.single hs1)
      have hadd : addCfg (singleCfg (⟨0, by omega⟩ : Fin 2) 1) (singleCfg (⟨1, by omega⟩ : Fin 2) 1) = vec2 1 1 := by
        funext j
        match j with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
      rw [hadd] at h2; exact h2
    have htr := hcycle.trans ih
    have hsum : addCfg (vec2 1 1) (vec2 n n) = vec2 (n + 1) (n + 1) := by
      funext j; unfold addCfg vec2; split <;> omega
    rw [hsum] at htr; exact htr

/-- Counterexample C5 (Sharpness of `b ≥ 2` for first-moment strict dissipation):
    At b = 1, w = 2 (classical symmetric 1D sandpile CB(2; 1, 1)), M_1(i) = i + 1 has
    EXACT ZERO drop at site 0: tau(0)*p(0) = 2*1 = 1*2 = dot(A(0), p). -/
theorem sharpness_b1_M1_zero_drop :
    (carryEchoSys 1 2).tau ⟨0, by omega⟩ * (0 + 1) =
    dot 2 (fun j => (carryEchoSys 1 2).A ⟨0, by omega⟩ j) (fun i => i.val + 1) := by
  decide

end WitnessesAndSharpness

end SiliconSandpile
