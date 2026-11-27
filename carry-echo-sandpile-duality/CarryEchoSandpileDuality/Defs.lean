/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`carry-echo-sandpile-duality`)

Carry-Echo and Directed-Carry Silicon Sandpile Duality Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace SiliconSandpile


/-! ## Part 1: Finite-Sum & Configuration Vector Primitives -/

def zeroCfg (w : Nat) : Fin w → Nat := fun _ => 0

def oneCfg (w : Nat) : Fin w → Nat := fun _ => 1

def addCfg {w : Nat} (x y : Fin w → Nat) : Fin w → Nat := fun i => x i + y i

def singleCfg {w : Nat} (i : Fin w) (v : Nat) : Fin w → Nat := fun j => if j = i then v else 0

def decAt {w : Nat} (f : Fin w → Nat) (i : Fin w) : Fin w → Nat :=
  fun j => if j = i then f i - 1 else f j

def finSum : (w : Nat) → (Fin w → Nat) → Nat
  | 0, _ => 0
  | w + 1, f => finSum w (fun i => f i.castSucc) + f ⟨w, Nat.lt_succ_self w⟩

theorem finSum_zero (w : Nat) : finSum w (fun _ => 0) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [finSum, ih]

theorem finSum_congr {w : Nat} {f g : Fin w → Nat} (h : ∀ i, f i = g i) :
    finSum w f = finSum w g := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [finSum]
    rw [ih (fun i => h i.castSucc), h ⟨w, Nat.lt_succ_self w⟩]

theorem finSum_add (w : Nat) (f g : Fin w → Nat) :
    finSum w (fun i => f i + g i) = finSum w f + finSum w g := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem finSum_single {w : Nat} (i : Fin w) (v : Nat) :
    finSum w (fun j => if j = i then v else 0) = v := by
  induction w with
  | zero => exact Fin.elim0 i
  | succ w ih =>
    simp only [finSum]
    by_cases hi : i.val = w
    · have hi_eq : i = ⟨w, Nat.lt_succ_self w⟩ := Fin.ext hi
      subst hi_eq
      have h0 : finSum w (fun j : Fin w => if j.castSucc = ⟨w, Nat.lt_succ_self w⟩ then v else 0) = 0 := by
        have hc : finSum w (fun j : Fin w => if j.castSucc = ⟨w, Nat.lt_succ_self w⟩ then v else 0) =
                  finSum w (fun _ => 0) := by
          apply finSum_congr
          intro j
          have hne : j.castSucc ≠ ⟨w, Nat.lt_succ_self w⟩ := by
            intro h
            have hv : j.val = w := congrArg Fin.val h
            omega
          simp [hne]
        rw [hc, finSum_zero]
      rw [h0]
      simp
    · have hlt : i.val < w := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hi
      let i' : Fin w := ⟨i.val, hlt⟩
      have hi_eq : i = i'.castSucc := Fin.ext rfl
      have hne_top : ¬ (⟨w, Nat.lt_succ_self w⟩ = i) := by
        intro h
        have hv : w = i.val := congrArg Fin.val h
        omega
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hne_top h)), Nat.add_zero]
      have hcongr : finSum w (fun j : Fin w => if j.castSucc = i then v else 0) =
                    finSum w (fun j : Fin w => if j = i' then v else 0) := by
        apply finSum_congr
        intro j
        by_cases hji : j = i'
        · subst hji; simp [hi_eq]
        · have hne' : j.castSucc ≠ i := by
            intro h
            apply hji
            exact Fin.ext (by simpa [i'] using congrArg Fin.val h)
          simp [hji, hne']
      rw [hcongr, ih i']

theorem finSum_sub_single {w : Nat} (f : Fin w → Nat) (i : Fin w) (k : Nat) (hk : k ≤ f i) :
    finSum w (fun j => if j = i then f i - k else f j) + k = finSum w f := by
  have h1 : finSum w (fun j => (if j = i then f i - k else f j) + (if j = i then k else 0)) =
            finSum w (fun j => if j = i then f i - k else f j) + k := by
    rw [finSum_add, finSum_single]
  rw [← h1]
  apply finSum_congr
  intro j
  by_cases hji : j = i
  · subst hji; simp; omega
  · simp [hji]

def dot (w : Nat) (x y : Fin w → Nat) : Nat := finSum w (fun i => x i * y i)

structure AbelianToppleSys (w : Nat) where
  tau : Fin w → Nat
  tau_pos : ∀ i, 0 < tau i
  A : Fin w → Fin w → Nat
  A_diag : ∀ i, A i i = 0

namespace AbelianToppleSys

variable {w : Nat}

def IsStable (S : AbelianToppleSys w) (c : Fin w → Nat) : Prop := ∀ i, c i < S.tau i

def maxStable (S : AbelianToppleSys w) : Fin w → Nat := fun i => S.tau i - 1

def fire (S : AbelianToppleSys w) (c : Fin w → Nat) (i : Fin w) : Fin w → Nat :=
  fun j => if j = i then c i - S.tau i else c j + S.A i j

def Step (S : AbelianToppleSys w) (c : Fin w → Nat) (i : Fin w) (c' : Fin w → Nat) : Prop :=
  S.tau i ≤ c i ∧ c' = S.fire c i

inductive Steps (S : AbelianToppleSys w) : (Fin w → Nat) → (Fin w → Nat) → (Fin w → Nat) → Prop
  | refl (c : Fin w → Nat) : Steps S c (zeroCfg w) c
  | step {c c₁ c₂ : Fin w → Nat} {i : Fin w} {f : Fin w → Nat} :
      S.Step c i c₁ → Steps S c₁ f c₂ → Steps S c (addCfg (singleCfg i 1) f) c₂

structure LinearBalance (S : AbelianToppleSys w) where
  p : Fin w → Nat
  delta : Fin w → Nat
  balance : ∀ i, S.tau i * p i = delta i + dot w (fun j => S.A i j) p

theorem LinearBalance.step_eq {S : AbelianToppleSys w} (B : S.LinearBalance)
    {c c' : Fin w → Nat} {i : Fin w} (h : S.Step c i c') :
    dot w c B.p = dot w c' B.p + B.delta i := by
  rcases h with ⟨hlen, rfl⟩
  unfold dot fire
  have hdecomp :
      finSum w (fun j => (if j = i then c i - S.tau i else c j + S.A i j) * B.p j) =
      finSum w (fun j => (if j = i then (c i - S.tau i) * B.p i else c j * B.p j) +
                         (if j = i then 0 else S.A i j * B.p j)) := by
    apply finSum_congr
    intro j
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji, Nat.add_mul]
  rw [hdecomp, finSum_add]
  have hA : finSum w (fun j => if j = i then 0 else S.A i j * B.p j) =
            dot w (fun j => S.A i j) B.p := by
    unfold dot
    apply finSum_congr
    intro j
    by_cases hji : j = i
    · subst hji; simp [S.A_diag j]
    · simp [hji]
  rw [hA]
  have hsub : finSum w (fun j => if j = i then c i * B.p i - S.tau i * B.p i else c j * B.p j) +
              S.tau i * B.p i = finSum w (fun j => c j * B.p j) :=
    finSum_sub_single (fun j => c j * B.p j) i (S.tau i * B.p i) (Nat.mul_le_mul_right (B.p i) hlen)
  have hmul : (c i - S.tau i) * B.p i = c i * B.p i - S.tau i * B.p i :=
    Nat.sub_mul (c i) (S.tau i) (B.p i)
  have hcongr : finSum w (fun j => if j = i then (c i - S.tau i) * B.p i else c j * B.p j) =
                finSum w (fun j => if j = i then c i * B.p i - S.tau i * B.p i else c j * B.p j) := by
    apply finSum_congr
    intro j
    split
    · exact hmul
    · rfl
  rw [hcongr]
  have hbal := B.balance i
  omega

structure StrictPotential (S : AbelianToppleSys w) extends S.LinearBalance where
  delta_pos : ∀ i, 0 < delta i

/-! ### Strong Confluence & Odometer Uniqueness (No Termination Required!) -/

def findUnstableAux (S : AbelianToppleSys w) :
    (k : Nat) → (hk : k ≤ w) → (Fin w → Nat) → Option (Fin w)
  | 0, _, _ => none
  | k + 1, hk, c =>
    let idx : Fin w := ⟨k, hk⟩
    if S.tau idx ≤ c idx then some idx
    else findUnstableAux S k (Nat.le_of_lt hk) c

theorem findUnstableAux_some (S : AbelianToppleSys w) (k : Nat) (hk : k ≤ w) (c : Fin w → Nat)
    (i : Fin w) (h : S.findUnstableAux k hk c = some i) : S.tau i ≤ c i := by
  induction k with
  | zero => simp [findUnstableAux] at h
  | succ k ih =>
    simp only [findUnstableAux] at h
    split at h
    · next hle =>
      injection h with hi
      subst hi; exact hle
    · exact ih (Nat.le_of_lt hk) h

theorem findUnstableAux_none (S : AbelianToppleSys w) (k : Nat) (hk : k ≤ w) (c : Fin w → Nat)
    (h : S.findUnstableAux k hk c = none) :
    ∀ (i : Fin w), i.val < k → c i < S.tau i := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    simp only [findUnstableAux] at h
    split at h
    · contradiction
    · next hnot =>
      intro i hi
      by_cases hik : i.val = k
      · have hieq : i = ⟨k, hk⟩ := Fin.ext hik
        rw [hieq]; omega
      · exact ih (Nat.le_of_lt hk) h i (by omega)

def findUnstable (S : AbelianToppleSys w) (c : Fin w → Nat) : Option (Fin w) :=
  S.findUnstableAux w (Nat.le_refl w) c

def stabilizeAux (S : AbelianToppleSys w) (P : S.StrictPotential) :
    (fuel : Nat) → (c : Fin w → Nat) → dot w c P.p ≤ fuel →
    { r : (Fin w → Nat) × (Fin w → Nat) // S.IsStable r.1 ∧ S.Steps c r.2 r.1 }
  | fuel, c, hfuel =>
    match hfind : S.findUnstable c with
    | none =>
      ⟨(c, zeroCfg w),
       fun i => S.findUnstableAux_none w (Nat.le_refl w) c hfind i i.isLt,
       Steps.refl c⟩
    | some i =>
      have hle : S.tau i ≤ c i := S.findUnstableAux_some w (Nat.le_refl w) c i hfind
      have hstep : S.Step c i (S.fire c i) := ⟨hle, rfl⟩
      have hdrop : dot w c P.p = dot w (S.fire c i) P.p + P.delta i := P.toLinearBalance.step_eq hstep
      have hpos : 0 < P.delta i := P.delta_pos i
      match fuel, hfuel with
      | 0, h0 => False.elim (by omega)
      | fuel' + 1, hsucc =>
        have hlt : dot w (S.fire c i) P.p ≤ fuel' := by omega
        let res := S.stabilizeAux P fuel' (S.fire c i) hlt
        ⟨(res.val.1, addCfg (singleCfg i 1) res.val.2),
         res.property.1,
         Steps.step hstep res.property.2⟩

def stab (S : AbelianToppleSys w) (P : S.StrictPotential) (c : Fin w → Nat) : Fin w → Nat :=
  (S.stabilizeAux P (dot w c P.p) c (Nat.le_refl _)).val.1

def odom (S : AbelianToppleSys w) (P : S.StrictPotential) (c : Fin w → Nat) : Fin w → Nat :=
  (S.stabilizeAux P (dot w c P.p) c (Nat.le_refl _)).val.2

def IsRecurrent (S : AbelianToppleSys w) (P : S.StrictPotential) (c : Fin w → Nat) : Prop :=
  S.IsStable c ∧ ∃ a : Fin w → Nat, S.stab P (addCfg S.maxStable a) = c

structure HarmonicGroupCert (S : AbelianToppleSys w) (P : S.StrictPotential) where
  beta : Fin w → Nat
  burn_mu : S.Steps (addCfg S.maxStable beta) (oneCfg w) S.maxStable
  M : Nat
  M_pos : 0 < M
  Hbal : S.LinearBalance
  H_mod_dvd : ∀ i, M ∣ Hbal.delta i
  gen : Fin w
  gen_unit : Hbal.p gen % M = 1 % M
  Pred : (Fin w → Nat) → Prop
  burn_implies_Pred : ∀ c, S.IsStable c → S.Steps (addCfg c beta) (oneCfg w) c → Pred c
  H_inj_on_Pred : ∀ c₁ c₂, Pred c₁ → Pred c₂ →
    dot w c₁ Hbal.p % M = dot w c₂ Hbal.p % M → c₁ = c₂

namespace HarmonicGroupCert

variable {S : AbelianToppleSys w} {P : S.StrictPotential} (C : S.HarmonicGroupCert P)

def Hval (c : Fin w → Nat) : Nat := dot w c C.Hbal.p

def decode (r : Fin C.M) : Fin w → Nat :=
  let hmu := C.Hval S.maxStable % C.M
  let k := (r.val + C.M - hmu) % C.M
  S.stab P (addCfg S.maxStable (singleCfg C.gen k))

def encode (c : Fin w → Nat) : Fin C.M :=
  ⟨C.Hval c % C.M, Nat.mod_lt _ C.M_pos⟩

/-- Main Lifted Theorem 4: Existence & Uniqueness of the Recurrent Identity Element. -/
def identity : Fin w → Nat := C.decode ⟨0, C.M_pos⟩

/-- Main Lifted Theorem 5: Constructive Unique Inverse in the Sandpile Group. -/
def inv (c : Fin w → Nat) : Fin w → Nat :=
  let r := C.Hval c % C.M
  C.decode ⟨(C.M - r) % C.M, Nat.mod_lt _ C.M_pos⟩

end HarmonicGroupCert

end AbelianToppleSys

section CarryEcho


/-- Exact base-b repunit R_{b, k} = sum_{j=0}^{k-1} b^j = (b^k - 1) / (b - 1). -/
def repunit (b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => b * repunit b k + 1

theorem repunit_pos (b k : Nat) (hk : 0 < k) : 0 < repunit b k := by
  cases k with
  | zero => omega
  | succ k' => simp [repunit]

theorem repunit_add_one (b k : Nat) : repunit b (k + 1) = repunit b k + b ^ k := by
  induction k with
  | zero => simp [repunit]
  | succ k ih =>
    simp only [repunit] at ih ⊢
    rw [ih, Nat.mul_add, Nat.pow_succ']
    omega

theorem repunit_recurrence (b k : Nat) :
    (b + 1) * repunit b (k + 1) = repunit b (k + 2) + b * repunit b k := by
  simp only [repunit]
  have h1 : (b + 1) * (b * repunit b k + 1) = b * (b * repunit b k + 1) + 1 * (b * repunit b k + 1) :=
    Nat.add_mul b 1 _
  rw [Nat.one_mul] at h1
  omega

theorem pow_ge_one (b k : Nat) (hb : 1 ≤ b) : 1 ≤ b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ (by omega))

theorem pow_mono {b k m : Nat} (hb : 1 ≤ b) (hkm : k ≤ m) : b ^ k ≤ b ^ m := by
  induction hkm with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rw [Nat.pow_succ]
    exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ (by omega))

theorem repunit_lt_mul_pow {b : Nat} (hb : 2 ≤ b) (k : Nat) :
    repunit b (k + 1) < (k + 1) * b ^ (k + 1) := by
  induction k with
  | zero => simp [repunit]; omega
  | succ k ih =>
    rw [repunit_add_one]
    have hpow : b ^ (k + 1) ≤ b ^ (k + 2) := pow_mono (by omega) (Nat.le_succ _)
    have h1 : (k + 1) * b ^ (k + 1) + b ^ (k + 1) = (k + 2) * b ^ (k + 1) := by
      have := (Nat.add_mul (k + 1) 1 (b ^ (k + 1))).symm
      rw [Nat.one_mul] at this
      exact this
    have h2 : (k + 2) * b ^ (k + 1) ≤ (k + 2) * b ^ (k + 2) := Nat.mul_le_mul_left (k + 2) hpow
    change repunit b (k + 1) + b ^ (k + 1) < (k + 2) * b ^ (k + 2)
    omega

theorem psiWeight_ineq {b : Nat} (hb : 2 ≤ b) {k m : Nat} (hkm : k < m) :
    (m + 1) * repunit b (k + 1) < (k + 1) * repunit b (m + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = k + 1 + d := ⟨m - k - 1, by omega⟩
  induction d with
  | zero =>
    rw [Nat.add_zero, repunit_add_one b (k + 1), Nat.mul_add]
    have h1 : (k + 2) * repunit b (k + 1) = (k + 1) * repunit b (k + 1) + repunit b (k + 1) := by
      have := Nat.add_mul (k + 1) 1 (repunit b (k + 1))
      rw [Nat.one_mul] at this; exact this
    have hlt := repunit_lt_mul_pow hb k
    omega
  | succ d ih =>
    have hstep : k + 1 + (d + 1) + 1 = (k + 1 + d + 1) + 1 := by omega
    rw [hstep, repunit_add_one b (k + 1 + d + 1), Nat.mul_add]
    have h1 : (k + 1 + d + 1 + 1) * repunit b (k + 1) =
              (k + 1 + d + 1) * repunit b (k + 1) + repunit b (k + 1) := by
      have := Nat.add_mul (k + 1 + d + 1) 1 (repunit b (k + 1))
      rw [Nat.one_mul] at this; exact this
    have hlt1 := repunit_lt_mul_pow hb k
    have hpow : b ^ (k + 1) ≤ b ^ (k + 1 + d + 1) := pow_mono (by omega) (by omega)
    have hlt2 : repunit b (k + 1) < (k + 1) * b ^ (k + 1 + d + 1) :=
      Nat.lt_of_lt_of_le hlt1 (Nat.mul_le_mul_left (k + 1) hpow)
    omega

/-- The Bit-Sliced Radix-b Carry-Echo Abelian Sandpile E_{b, w}:
    threshold b + 1 at every bit position; firing bit i sends 1 chip to i+1 and b chips to i-1. -/
def carryEchoSys (b w : Nat) : AbelianToppleSys w where
  tau := fun _ => b + 1
  tau_pos := fun _ => Nat.succ_pos b
  A := fun i j => (if j.val = i.val + 1 then 1 else 0) + (if i.val = j.val + 1 then b else 0)
  A_diag := fun i => by simp

theorem dot_carryEcho_row (b w : Nat) (p : Fin w → Nat) (i : Fin w) :
    dot w (fun j => (carryEchoSys b w).A i j) p =
    (if h : i.val + 1 < w then p ⟨i.val + 1, h⟩ else 0) +
    (if h : 0 < i.val then b * p ⟨i.val - 1, by omega⟩ else 0) := by
  unfold dot carryEchoSys
  dsimp only
  have hsplit : finSum w (fun j => ((if j.val = i.val + 1 then 1 else 0) +
                                    (if i.val = j.val + 1 then b else 0)) * p j) =
                finSum w (fun j => (if j.val = i.val + 1 then 1 else 0) * p j) +
                finSum w (fun j => (if i.val = j.val + 1 then b else 0) * p j) := by
    rw [← finSum_add]
    apply finSum_congr
    intro j
    exact Nat.add_mul _ _ _
  rw [hsplit]
  have hup : finSum w (fun j => (if j.val = i.val + 1 then 1 else 0) * p j) =
             (if h : i.val + 1 < w then p ⟨i.val + 1, h⟩ else 0) := by
    by_cases h : i.val + 1 < w
    · simp only [h, dite_true]
      let idx : Fin w := ⟨i.val + 1, h⟩
      have hc : finSum w (fun j => (if j.val = i.val + 1 then 1 else 0) * p j) =
                finSum w (fun j => if j = idx then p idx else 0) := by
        apply finSum_congr
        intro j
        by_cases hje : j = idx
        · subst hje; simp [idx]
        · have hv : j.val ≠ i.val + 1 := fun hv => hje (Fin.ext hv)
          simp [hje, hv]
      rw [hc, finSum_single]
    · simp only [h, dite_false]
      have hc : finSum w (fun j => (if j.val = i.val + 1 then 1 else 0) * p j) =
                finSum w (fun _ => 0) := by
        apply finSum_congr
        intro j
        have hv : j.val ≠ i.val + 1 := by omega
        simp [hv]
      rw [hc, finSum_zero]
  have hdn : finSum w (fun j => (if i.val = j.val + 1 then b else 0) * p j) =
             (if h : 0 < i.val then b * p ⟨i.val - 1, by omega⟩ else 0) := by
    by_cases h : 0 < i.val
    · simp only [h, dite_true]
      let idx : Fin w := ⟨i.val - 1, by omega⟩
      have hc : finSum w (fun j => (if i.val = j.val + 1 then b else 0) * p j) =
                finSum w (fun j => if j = idx then b * p idx else 0) := by
        apply finSum_congr
        intro j
        by_cases hje : j = idx
        · subst hje
          have hv : i.val = idx.val + 1 := by simp [idx]; omega
          simp [hv]
        · have hv : i.val ≠ j.val + 1 := by
            intro hv
            apply hje
            exact Fin.ext (by simp [idx]; omega)
          simp [hje, hv]
      rw [hc, finSum_single]
    · simp only [h, dite_false]
      have hc : finSum w (fun j => (if i.val = j.val + 1 then b else 0) * p j) =
                finSum w (fun _ => 0) := by
        apply finSum_congr
        intro j
        have hv : i.val ≠ j.val + 1 := by omega
        simp [hv]
      rw [hc, finSum_zero]
  rw [hup, hdn]

/-! ### Five Exact Linear-Balance & Potential Certificates for E_{b, w} -/

/-- 1. First-Moment Strict Potential M_1(c) = sum (i+1) c_i (strictly dissipative ∀ b ≥ 2). -/
def carryEchoM1Pot (b w : Nat) (hb : 2 ≤ b) : (carryEchoSys b w).StrictPotential where
  p := fun i => i.val + 1
  delta := fun i => if i.val + 1 = w then (b - 1) + (w + 1) else b - 1
  balance := fun i => by
    rw [dot_carryEcho_row]
    change (b + 1) * (i.val + 1) =
           (if i.val + 1 = w then (b - 1) + (w + 1) else b - 1) +
           ((if h : i.val + 1 < w then i.val + 1 + 1 else 0) +
            (if h : 0 < i.val then b * (i.val - 1 + 1) else 0))
    by_cases htop : i.val + 1 < w
    · have hne : i.val + 1 ≠ w := by omega
      simp only [hne, ite_false, htop, dite_true]
      by_cases hbot : 0 < i.val
      · simp only [hbot, dite_true]
        have hsub : i.val - 1 + 1 = i.val := by omega
        rw [hsub]
        have hmul1 : (b + 1) * (i.val + 1) = b * i.val + b + i.val + 1 := by
          rw [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]; omega
        omega
      · simp only [hbot, dite_false]
        have hi0 : i.val = 0 := by omega
        rw [hi0]; simp; omega
    · have heq : i.val + 1 = w := by omega
      simp only [htop, dite_false]
      simp only [heq, ite_true]
      by_cases hbot : 0 < i.val
      · simp only [hbot, dite_true]
        have hsub : i.val - 1 + 1 = i.val := by omega
        rw [hsub]
        have hmul1 : (b + 1) * w = b * i.val + b + i.val + 1 := by
          have h1 : (b + 1) * (i.val + 1) = b * i.val + b + i.val + 1 := by
            rw [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]; omega
          have h2 : (b + 1) * w = (b + 1) * (i.val + 1) := congrArg ((b + 1) * ·) heq.symm
          omega
        omega
      · simp only [hbot, dite_false]
        have hw1 : w = 1 := by omega
        rw [hw1]; simp; omega
  delta_pos := fun i => by split <;> omega

/-- 2. Skew-Base-b Harmonic Balance H_b(c) = sum c_i * R_{b, i+1} (drops only at MSB by R_{b, w+1}). -/
def carryEchoHBal (b w : Nat) : (carryEchoSys b w).LinearBalance where
  p := fun i => repunit b (i.val + 1)
  delta := fun i => if i.val + 1 = w then repunit b (w + 1) else 0
  balance := fun i => by
    rw [dot_carryEcho_row]
    change (b + 1) * repunit b (i.val + 1) =
           (if i.val + 1 = w then repunit b (w + 1) else 0) +
           ((if h : i.val + 1 < w then repunit b (i.val + 1 + 1) else 0) +
            (if h : 0 < i.val then b * repunit b (i.val - 1 + 1) else 0))
    have hrec := repunit_recurrence b i.val
    by_cases htop : i.val + 1 < w
    · have hne : i.val + 1 ≠ w := by omega
      simp only [hne, ite_false, htop, dite_true]
      by_cases hbot : 0 < i.val
      · simp only [hbot, dite_true]
        have hsub : i.val - 1 + 1 = i.val := by omega
        have h2 : i.val + 1 + 1 = i.val + 2 := by omega
        rw [hsub, h2]; omega
      · simp only [hbot, dite_false]
        have hi0 : i.val = 0 := by omega
        rw [hi0] at hrec ⊢
        simp [repunit] at hrec ⊢
    · have heq : i.val + 1 = w := by omega
      simp only [htop, dite_false]
      simp only [heq, ite_true]
      have hw2 : i.val + 2 = w + 1 := by omega
      rw [heq, hw2] at hrec
      by_cases hbot : 0 < i.val
      · simp only [hbot, dite_true]
        have hsub : i.val - 1 + 1 = i.val := by omega
        rw [hsub]; omega
      · simp only [hbot, dite_false]
        have hi0 : i.val = 0 := by omega
        have hw1 : w = 1 := by omega
        rw [hw1]
        simp [repunit]

/-- 3. Constant-Drop Total-Avalanche Potential Ψ_{b, w}(i) = (i+1)R_{b,w+1} - (w+1)R_{b,i+1}. -/
def psiWeight (b w : Nat) (i : Fin w) : Nat :=
  (i.val + 1) * repunit b (w + 1) - (w + 1) * repunit b (i.val + 1)

theorem psiWeight_add (b w : Nat) (hb : 2 ≤ b) (i : Fin w) :
    psiWeight b w i + (w + 1) * repunit b (i.val + 1) = (i.val + 1) * repunit b (w + 1) := by
  unfold psiWeight
  have hlt := psiWeight_ineq hb i.isLt
  omega

theorem carryEcho_psi_step_balance (b w : Nat) (hb : 2 ≤ b) (i : Fin w) :
    (b + 1) * psiWeight b w i =
    (b - 1) * repunit b (w + 1) + dot w (fun j => (carryEchoSys b w).A i j) (psiWeight b w) := by
  rw [dot_carryEcho_row]
  change (b + 1) * psiWeight b w i =
         (b - 1) * repunit b (w + 1) +
         ((if h : i.val + 1 < w then psiWeight b w ⟨i.val + 1, h⟩ else 0) +
          (if h : 0 < i.val then b * psiWeight b w ⟨i.val - 1, by omega⟩ else 0))
  have hpi := psiWeight_add b w hb i
  by_cases htop : i.val + 1 < w
  · simp only [htop, dite_true]
    have hpu := psiWeight_add b w hb ⟨i.val + 1, htop⟩
    dsimp only at hpu
    have h2 : i.val + 1 + 1 = i.val + 2 := by omega
    rw [h2] at hpu
    by_cases hbot : 0 < i.val
    · simp only [hbot, dite_true]
      have hpd := psiWeight_add b w hb ⟨i.val - 1, by omega⟩
      dsimp only at hpd
      have hsub : i.val - 1 + 1 = i.val := by omega
      rw [hsub] at hpd
      have hrec := repunit_recurrence b i.val
      have hmul_pi : (b + 1) * psiWeight b w i + (b + 1) * ((w + 1) * repunit b (i.val + 1)) =
                     (b + 1) * ((i.val + 1) * repunit b (w + 1)) := by
        rw [← Nat.mul_add, hpi]
      have hmul_pd : b * psiWeight b w ⟨i.val - 1, by omega⟩ + b * ((w + 1) * repunit b i.val) =
                     b * (i.val * repunit b (w + 1)) := by
        rw [← Nat.mul_add, hpd]
      have hR : (b + 1) * ((w + 1) * repunit b (i.val + 1)) =
                (w + 1) * repunit b (i.val + 2) + b * ((w + 1) * repunit b i.val) := by
        have h1 : (b + 1) * ((w + 1) * repunit b (i.val + 1)) =
                  (w + 1) * ((b + 1) * repunit b (i.val + 1)) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (b + 1) (w + 1), Nat.mul_assoc]
        have h2' : b * ((w + 1) * repunit b i.val) = (w + 1) * (b * repunit b i.val) := by
          rw [← Nat.mul_assoc, Nat.mul_comm b (w + 1), Nat.mul_assoc]
        rw [h1, h2', hrec, Nat.mul_add]
      have hM : (b + 1) * ((i.val + 1) * repunit b (w + 1)) =
                (b - 1) * repunit b (w + 1) + (i.val + 2) * repunit b (w + 1) +
                b * (i.val * repunit b (w + 1)) := by
        have hc : (b + 1) * (i.val + 1) = (b - 1) + (i.val + 2) + b * i.val := by
          rw [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]; omega
        rw [← Nat.mul_assoc, hc, Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
      omega
    · simp only [hbot, dite_false]
      have hi0 : i.val = 0 := by omega
      have hpi0 : psiWeight b w i + (w + 1) * repunit b 1 = 1 * repunit b (w + 1) := by
        simpa [hi0] using hpi
      have hpu0 : psiWeight b w ⟨i.val + 1, htop⟩ + (w + 1) * repunit b 2 = 2 * repunit b (w + 1) := by
        simpa [hi0] using hpu
      have hmul_pi : (b + 1) * psiWeight b w i + (b + 1) * ((w + 1) * repunit b 1) =
                     (b + 1) * (1 * repunit b (w + 1)) := by
        rw [← Nat.mul_add, hpi0]
      have hR : (b + 1) * ((w + 1) * repunit b 1) = (w + 1) * repunit b 2 := by
        simp [repunit]; rw [Nat.mul_comm]
      have hM : (b + 1) * (1 * repunit b (w + 1)) =
                (b - 1) * repunit b (w + 1) + 2 * repunit b (w + 1) := by
        rw [Nat.one_mul, ← Nat.add_mul]; congr 1; omega
      omega
  · have heq : i.val + 1 = w := by omega
    simp only [htop, dite_false]
    by_cases hbot : 0 < i.val
    · simp only [hbot, dite_true]
      have hpd := psiWeight_add b w hb ⟨i.val - 1, by omega⟩
      dsimp only at hpd
      have hsub : i.val - 1 + 1 = i.val := by omega
      rw [hsub] at hpd
      have hrec := repunit_recurrence b i.val
      have hw2 : i.val + 2 = w + 1 := by omega
      rw [hw2] at hrec
      have hpi_w : psiWeight b w i + (w + 1) * repunit b (i.val + 1) = w * repunit b (w + 1) := by
        simpa [heq] using hpi
      have hmul_pi : (b + 1) * psiWeight b w i + (b + 1) * ((w + 1) * repunit b (i.val + 1)) =
                     (b + 1) * (w * repunit b (w + 1)) := by
        rw [← Nat.mul_add, hpi_w]
      have hmul_pd : b * psiWeight b w ⟨i.val - 1, by omega⟩ + b * ((w + 1) * repunit b i.val) =
                     b * (i.val * repunit b (w + 1)) := by
        rw [← Nat.mul_add, hpd]
      have hR : (b + 1) * ((w + 1) * repunit b (i.val + 1)) =
                (w + 1) * repunit b (w + 1) + b * ((w + 1) * repunit b i.val) := by
        have h1 : (b + 1) * ((w + 1) * repunit b (i.val + 1)) =
                  (w + 1) * ((b + 1) * repunit b (i.val + 1)) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (b + 1) (w + 1), Nat.mul_assoc]
        have h2' : b * ((w + 1) * repunit b i.val) = (w + 1) * (b * repunit b i.val) := by
          rw [← Nat.mul_assoc, Nat.mul_comm b (w + 1), Nat.mul_assoc]
        rw [h1, h2', hrec, Nat.mul_add]
      have hM : (b + 1) * (w * repunit b (w + 1)) =
                (b - 1) * repunit b (w + 1) + (w + 1) * repunit b (w + 1) +
                b * (i.val * repunit b (w + 1)) := by
        have hc : (b + 1) * w = (b - 1) + (w + 1) + b * i.val := by
          have h1 : (b + 1) * (i.val + 1) = (b - 1) + (i.val + 2) + b * i.val := by
            rw [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]; omega
          have hw_mul : (b + 1) * w = (b + 1) * (i.val + 1) := congrArg ((b + 1) * ·) heq.symm
          omega
        rw [← Nat.mul_assoc, hc, Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
      omega
    · simp only [hbot, dite_false]
      have hi0 : i.val = 0 := by omega
      have hw1 : w = 1 := by omega
      have hpi1 : psiWeight b w i + 2 * repunit b 1 = 1 * repunit b 2 := by
        have h1 : w + 1 = 2 := by omega
        have h2 : i.val + 1 = 1 := by omega
        simpa [h1, h2] using hpi
      have hr2 : repunit b 2 = b + 1 := by simp [repunit]
      have hr1 : repunit b 1 = 1 := by simp [repunit]
      have hrepw : repunit b (w + 1) = b + 1 := by
        have h1 : w + 1 = 2 := by omega
        rw [h1, hr2]
      rw [hr2, hr1] at hpi1
      rw [hrepw]
      have hpsi : psiWeight b w i = b - 1 := by omega
      rw [hpsi, Nat.mul_comm]
      omega

def carryEchoPsiPot (b w : Nat) (hb : 2 ≤ b) : (carryEchoSys b w).StrictPotential where
  p := psiWeight b w
  delta := fun _ => (b - 1) * repunit b (w + 1)
  balance := carryEcho_psi_step_balance b w hb
  delta_pos := fun _ => Nat.mul_pos (by omega) (repunit_pos b (w + 1) (Nat.succ_pos w))

/-- 4. Base-b Numeric Value Balance Φ_b(c) = sum c_i * b^i (w ≥ 2). -/
def carryEchoPhiBal (b w : Nat) (hw : 2 ≤ w) : (carryEchoSys b w).LinearBalance where
  p := fun i => b ^ i.val
  delta := fun i => (if i.val = 0 then 1 else 0) + (if i.val + 1 = w then b ^ w else 0)
  balance := fun i => by
    rw [dot_carryEcho_row]
    change (b + 1) * b ^ i.val =
           ((if i.val = 0 then 1 else 0) + (if i.val + 1 = w then b ^ w else 0)) +
           ((if h : i.val + 1 < w then b ^ (i.val + 1) else 0) +
            (if h : 0 < i.val then b * b ^ (i.val - 1) else 0))
    by_cases hbot : 0 < i.val
    · have hne0 : i.val ≠ 0 := by omega
      simp only [hne0, ite_false, hbot, dite_true]
      have hpow_dn : b * b ^ (i.val - 1) = b ^ i.val := by
        have hsub : (i.val - 1) + 1 = i.val := by omega
        have h1 : b ^ ((i.val - 1) + 1) = b * b ^ (i.val - 1) := Nat.pow_succ'
        rw [← h1, hsub]
      rw [hpow_dn]
      by_cases htop : i.val + 1 < w
      · have hnew : i.val + 1 ≠ w := by omega
        simp only [hnew, ite_false, htop, dite_true, Nat.pow_succ', Nat.add_mul, Nat.one_mul]; omega
      · have heqw : i.val + 1 = w := by omega
        simp only [htop, dite_false]
        simp only [heqw, ite_true]
        have hpow_w : b ^ w = b * b ^ i.val := by
          have h1 : b ^ w = b ^ (i.val + 1) := congrArg (b ^ ·) heqw.symm
          rw [h1, Nat.pow_succ']
        rw [hpow_w, Nat.add_mul, Nat.one_mul]; omega
    · have hi0 : i.val = 0 := by omega
      have htop : i.val + 1 < w := by omega
      have hnew : i.val + 1 ≠ w := by omega
      simp only [hbot, dite_false, htop, dite_true, hnew, ite_false]
      simp only [hi0, ite_true]
      simp; omega

/-- 5. Chip Mass Balance W(c) = sum c_i (w ≥ 2). -/
def carryEchoMassBal (b w : Nat) (hw : 2 ≤ w) : (carryEchoSys b w).LinearBalance where
  p := fun _ => 1
  delta := fun i => (if i.val = 0 then b else 0) + (if i.val + 1 = w then 1 else 0)
  balance := fun i => by
    rw [dot_carryEcho_row]
    change (b + 1) * 1 =
           ((if i.val = 0 then b else 0) + (if i.val + 1 = w then 1 else 0)) +
           ((if h : i.val + 1 < w then 1 else 0) +
            (if h : 0 < i.val then b * 1 else 0))
    by_cases hbot : 0 < i.val
    · have hne0 : i.val ≠ 0 := by omega
      simp only [hne0, ite_false, hbot, dite_true]
      by_cases htop : i.val + 1 < w
      · have hnew : i.val + 1 ≠ w := by omega
        simp only [hnew, ite_false, htop, dite_true]; omega
      · have heqw : i.val + 1 = w := by omega
        simp only [htop, dite_false]
        simp only [heqw, ite_true]; omega
    · have hi0 : i.val = 0 := by omega
      have htop : i.val + 1 < w := by omega
      have hnew : i.val + 1 ≠ w := by omega
      simp only [hbot, dite_false, htop, dite_true, hnew, ite_false]
      simp only [hi0, ite_true]; omega

/-! ### Exact Avalanche Energy & Boundary-Odometer Conservation Theorems for E_{b, w} -/

def skewWeight (b w : Nat) (c : Fin w → Nat) : Nat :=
  dot w c (fun i => repunit b (i.val + 1))

def firstMoment (w : Nat) (c : Fin w → Nat) : Nat :=
  dot w c (fun i => i.val + 1)

def psiPotential (b w : Nat) (c : Fin w → Nat) : Nat :=
  dot w c (psiWeight b w)

def baseValue (b w : Nat) (c : Fin w → Nat) : Nat :=
  dot w c (fun i => b ^ i.val)

def chipMass (w : Nat) (c : Fin w → Nat) : Nat :=
  finSum w c

def carryEchoBeta (b w : Nat) : Fin w → Nat :=
  fun i => (if i.val = 0 then 1 else 0) + (if i.val + 1 = w then b else 0)

def sweepState (b w k : Nat) : Fin w → Nat :=
  fun j =>
    if j.val < k then
      b + (if j.val = 0 then 1 else 0) + (if j.val + 1 = k then b else 0)
    else if j.val = k ∧ 0 < k then
      b - 1
    else
      b

theorem sweepState_step (b w k : Nat) (hb : 2 ≤ b) (hk : k + 1 ≤ w) :
    (carryEchoSys b w).Step (sweepState b w (k + 1)) ⟨k, hk⟩ (sweepState b w k) := by
  refine ⟨?_, ?_⟩
  · change b + 1 ≤ sweepState b w (k + 1) ⟨k, hk⟩
    unfold sweepState
    simp only [Nat.lt_succ_self, ite_true]
    omega
  · funext j
    unfold AbelianToppleSys.fire carryEchoSys sweepState
    dsimp only
    by_cases hjk : j = ⟨k, hk⟩
    · subst hjk
      simp only [ite_true, Nat.lt_succ_self, Nat.lt_irrefl, ite_false]
      by_cases hk0 : k = 0
      · simp [hk0]
      · have hpos : 0 < k := by omega
        simp [hk0, hpos]; omega
    · have hne_val : j.val ≠ k := fun hv => hjk (Fin.ext hv)
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hjk h))]
      by_cases hjlt : j.val < k
      · have hjlt1 : j.val < k + 1 := by omega
        have hup : ¬ (j.val = k + 1) := by omega
        have hnot_top : ¬ (j.val + 1 = k + 1) := by omega
        simp only [hjlt, hjlt1, hup, hnot_top, ite_true, ite_false, Nat.add_zero]
        by_cases hdn : k = j.val + 1
        · have hdn' : j.val + 1 = k := hdn.symm
          rw [ite_eq_left_iff.mpr (fun h => False.elim (h hdn)),
              ite_eq_left_iff.mpr (fun h => False.elim (h hdn')), Nat.zero_add]
        · have hdn' : ¬ (j.val + 1 = k) := fun h => hdn h.symm
          rw [ite_eq_right_iff.mpr (fun h => False.elim (hdn h)),
              ite_eq_right_iff.mpr (fun h => False.elim (hdn' h)), Nat.add_zero]
      · have hjgt : k < j.val := by omega
        have hjnotlt1 : ¬ (j.val < k + 1) := by omega
        have hdn : ¬ (k = j.val + 1) := by omega
        have hne_and : ¬ (j.val = k ∧ 0 < k) := by omega
        simp only [hjlt, hjnotlt1, hne_and, hdn, ite_false, Nat.add_zero]
        by_cases hup : j.val = k + 1
        · have hpos1 : 0 < k + 1 := Nat.succ_pos k
          have hup_and : j.val = k + 1 ∧ 0 < k + 1 := ⟨hup, hpos1⟩
          rw [ite_eq_left_iff.mpr (fun h => False.elim (h hup_and)),
              ite_eq_left_iff.mpr (fun h => False.elim (h hup))]
          omega
        · have hnot_and : ¬ (j.val = k + 1 ∧ 0 < k + 1) := fun h => hup h.1
          rw [ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)),
              ite_eq_right_iff.mpr (fun h => False.elim (hup h)), Nat.add_zero]

theorem sweepState_steps (b w k : Nat) (hb : 2 ≤ b) (hk : k ≤ w) :
    (carryEchoSys b w).Steps (sweepState b w k)
      (fun j => if j.val < k then 1 else 0)
      (sweepState b w 0) := by
  induction k with
  | zero =>
    have h0 : (fun j : Fin w => if j.val < 0 then 1 else 0) = zeroCfg w := by
      funext j; simp [zeroCfg]
    rw [h0]
    exact AbelianToppleSys.Steps.refl _
  | succ k ih =>
    have hs := sweepState_step b w k hb hk
    have hrest := ih (Nat.le_of_lt hk)
    have hodom : addCfg (singleCfg ⟨k, hk⟩ 1) (fun j : Fin w => if j.val < k then 1 else 0) =
                 (fun j : Fin w => if j.val < k + 1 then 1 else 0) := by
      funext j
      simp only [addCfg, singleCfg]
      by_cases hjk : j = ⟨k, hk⟩
      · subst hjk; simp
      · have hv : j.val ≠ k := fun h => hjk (Fin.ext h)
        by_cases hjlt : j.val < k
        · have hjlt1 : j.val < k + 1 := by omega
          simp [hjk, hjlt, hjlt1]
        · have hjnot1 : ¬ (j.val < k + 1) := by omega
          simp [hjk, hjlt, hjnot1]
    rw [← hodom]
    exact AbelianToppleSys.Steps.step hs hrest

theorem carryEcho_maxStable_burns (b w : Nat) (hb : 2 ≤ b) :
    (carryEchoSys b w).Steps
      (addCfg (carryEchoSys b w).maxStable (carryEchoBeta b w))
      (oneCfg w)
      (carryEchoSys b w).maxStable := by
  have hstart : sweepState b w w = addCfg (carryEchoSys b w).maxStable (carryEchoBeta b w) := by
    funext j
    unfold sweepState addCfg AbelianToppleSys.maxStable carryEchoSys carryEchoBeta
    simp only [j.isLt, ite_true, Nat.add_sub_cancel]
    omega
  have hend : sweepState b w 0 = (carryEchoSys b w).maxStable := by
    funext j
    unfold sweepState AbelianToppleSys.maxStable carryEchoSys
    simp
  have h1 : (fun j : Fin w => if j.val < w then 1 else 0) = oneCfg w := by
    funext j; simp [oneCfg, j.isLt]
  have hsteps := sweepState_steps b w w hb (Nat.le_refl w)
  rw [hstart, hend, h1] at hsteps
  exact hsteps

/-! ### Interval Barrier Lemma: Burning Implies Canonical Dual Skew-Base-b -/

/-- Dual canonical skew-base-b predicate:
    every digit ≤ b, and whenever c(j) = 0, every lower digit i < j must equal b. -/
def IsDualSkew (b w : Nat) (c : Fin w → Nat) : Prop :=
  (∀ i, c i ≤ b) ∧ ∀ i j : Fin w, i.val < j.val → c j = 0 → c i = b

/-- Canonical skew-base-b predicate:
    every digit ≤ b, and whenever d(j) = b, every lower digit i < j must equal 0. -/
def IsSkewCanon (b w : Nat) (d : Fin w → Nat) : Prop :=
  (∀ i, d i ≤ b) ∧ ∀ i j : Fin w, i.val < j.val → d j = b → d i = 0

/-- Interval Barrier Invariant: if no site in [i₀, j₀] can reach threshold b+1
    even after receiving at most one carry from i₀-1 or one echo from j₀+1,
    then i₀ never fires in any odometer-≤1 firing trace. -/
theorem carryEcho_barrier_lemma {b w : Nat} (hb : 2 ≤ b) (i₀ j₀ : Fin w) (hij : i₀.val < j₀.val)
    {s c_end f : Fin w → Nat} (hsteps : (carryEchoSys b w).Steps s f c_end)
    (hf_le : ∀ k, f k ≤ 1)
    (hmid : ∀ k : Fin w, i₀.val < k.val → k.val < j₀.val → s k ≤ b)
    (hleft : s i₀ ≤ b - 1 + (if h : 0 < i₀.val then 1 - f ⟨i₀.val - 1, by omega⟩ else 1))
    (hright : s j₀ ≤ (if h : j₀.val + 1 < w then b * (1 - f ⟨j₀.val + 1, h⟩) else b)) :
    f i₀ = 0 := by
  induction hsteps with
  | refl s => rfl
  | @step s s₁ c_end u f' hsu hrest ih =>
    have hf'_le : ∀ k, f' k ≤ 1 := by
      intro k
      have hk := hf_le k
      simp only [addCfg, singleCfg] at hk
      by_cases hku : k = u
      · subst hku; simp at hk; omega
      · simp [hku] at hk; omega
    have hfu_zero : f' u = 0 := by
      have hu := hf_le u
      simp only [addCfg, singleCfg, ite_true] at hu
      omega
    have htau : b + 1 ≤ s u := hsu.1
    have hu_out : u.val < i₀.val ∨ j₀.val < u.val := by
      by_cases h1 : u.val < i₀.val
      · exact Or.inl h1
      · by_cases h2 : j₀.val < u.val
        · exact Or.inr h2
        · exfalso
          by_cases heqi : u = i₀
          · subst heqi
            by_cases h0 : 0 < u.val
            · simp only [h0, dite_true] at hleft; omega
            · simp only [h0, dite_false] at hleft; omega
          · by_cases heqj : u = j₀
            · subst heqj
              by_cases hw : u.val + 1 < w
              · simp only [hw, dite_true] at hright
                have hle2 : 1 - addCfg (singleCfg u 1) f' ⟨u.val + 1, hw⟩ ≤ 1 := by omega
                have hmul : b * (1 - addCfg (singleCfg u 1) f' ⟨u.val + 1, hw⟩) ≤ b * 1 :=
                  Nat.mul_le_mul_left b hle2
                omega
              · simp only [hw, dite_false] at hright; omega
            · have hlt1 : i₀.val < u.val := by
                have : u.val ≠ i₀.val := fun hv => heqi (Fin.ext hv); omega
              have hlt2 : u.val < j₀.val := by
                have : u.val ≠ j₀.val := fun hv => heqj (Fin.ext hv); omega
              have hm := hmid u hlt1 hlt2
              omega
    have hui_ne : u ≠ i₀ := by intro h; subst h; omega
    have huj_ne : u ≠ j₀ := by intro h; subst h; omega
    have hmid' : ∀ k : Fin w, i₀.val < k.val → k.val < j₀.val → s₁ k ≤ b := by
      intro k hk1 hk2
      rw [hsu.2]
      unfold AbelianToppleSys.fire carryEchoSys
      have hku : k ≠ u := by intro h; subst h; omega
      simp only [ite_eq_right_iff.mpr (fun h => False.elim (hku h))]
      have h1 : k.val ≠ u.val + 1 := by omega
      have h2 : u.val ≠ k.val + 1 := by omega
      simp only [h1, h2, ite_false, Nat.add_zero]
      exact hmid k hk1 hk2
    have hleft' : s₁ i₀ ≤ b - 1 + (if h : 0 < i₀.val then 1 - f' ⟨i₀.val - 1, by omega⟩ else 1) := by
      rw [hsu.2]
      unfold AbelianToppleSys.fire carryEchoSys
      have hiu : i₀ ≠ u := fun h => hui_ne h.symm
      simp only [ite_eq_right_iff.mpr (fun h => False.elim (hiu h))]
      have hno_echo : u.val ≠ i₀.val + 1 := by omega
      simp only [hno_echo, ite_false, Nat.add_zero]
      by_cases h0 : 0 < i₀.val
      · simp only [h0, dite_true] at hleft ⊢
        let im : Fin w := ⟨i₀.val - 1, by omega⟩
        by_cases hum : u = im
        · have heq_up : i₀.val = u.val + 1 := by rw [hum]; simp [im]; omega
          have hfm : addCfg (singleCfg u 1) f' im = 1 := by
            rw [← hum]; simp [addCfg, singleCfg, hfu_zero]
          rw [hfm] at hleft
          have hfu' : f' im = 0 := by rw [← hum]; exact hfu_zero
          change s i₀ + (if i₀.val = u.val + 1 then 1 else 0) ≤ b - 1 + (1 - f' im)
          simp only [heq_up, ite_true]
          rw [hfu']
          omega
        · have hne_up : i₀.val ≠ u.val + 1 := by
            intro hv; apply hum; exact Fin.ext (by simp [im]; omega)
          simp only [hne_up, ite_false, Nat.add_zero]
          have hfm : addCfg (singleCfg u 1) f' im = f' im := by
            simp [addCfg, singleCfg, Ne.symm hum]
          rw [hfm] at hleft
          exact hleft
      · simp only [h0, dite_false] at hleft ⊢
        have hne_up : i₀.val ≠ u.val + 1 := by omega
        simp only [hne_up, ite_false, Nat.add_zero]
        exact hleft
    have hright' : s₁ j₀ ≤ (if h : j₀.val + 1 < w then b * (1 - f' ⟨j₀.val + 1, h⟩) else b) := by
      rw [hsu.2]
      unfold AbelianToppleSys.fire carryEchoSys
      have hju : j₀ ≠ u := fun h => huj_ne h.symm
      simp only [ite_eq_right_iff.mpr (fun h => False.elim (hju h))]
      have hno_carry : j₀.val ≠ u.val + 1 := by omega
      simp only [hno_carry, ite_false, Nat.zero_add]
      by_cases hw : j₀.val + 1 < w
      · simp only [hw, dite_true] at hright ⊢
        let jp : Fin w := ⟨j₀.val + 1, hw⟩
        by_cases hup : u = jp
        · have heq_dn : u.val = j₀.val + 1 := by rw [hup]
          simp only [heq_dn, ite_true]
          have hfp : addCfg (singleCfg u 1) f' jp = 1 := by
            rw [← hup]; simp [addCfg, singleCfg, hfu_zero]
          rw [hfp] at hright
          have hfu' : f' jp = 0 := by rw [← hup]; exact hfu_zero
          rw [hfu']
          simp at hright ⊢
          omega
        · have hne_dn : u.val ≠ j₀.val + 1 := by
            intro hv; apply hup; exact Fin.ext hv
          simp only [hne_dn, ite_false, Nat.add_zero]
          have hfp : addCfg (singleCfg u 1) f' jp = f' jp := by
            simp [addCfg, singleCfg, Ne.symm hup]
          rw [hfp] at hright
          exact hright
      · simp only [hw, dite_false] at hright ⊢
        have hne_dn : u.val ≠ j₀.val + 1 := by omega
        simp only [hne_dn, ite_false, Nat.add_zero]
        exact hright
    have hi0_zero := ih hf'_le hmid' hleft' hright'
    simp only [addCfg, singleCfg]
    have hiu : i₀ ≠ u := fun h => hui_ne h.symm
    simp [hiu, hi0_zero]

theorem carryEcho_burn_implies_dualSkew {b w : Nat} (hb : 2 ≤ b) (c : Fin w → Nat)
    (hstab : (carryEchoSys b w).IsStable c)
    (hburn : (carryEchoSys b w).Steps (addCfg c (carryEchoBeta b w)) (oneCfg w) c) :
    IsDualSkew b w c := by
  have hle : ∀ i, c i ≤ b := fun i => by
    have := hstab i; change c i < b + 1 at this; omega
  refine ⟨hle, ?_⟩
  intro i₀ j₀ hij hcj0
  by_cases hci : c i₀ = b
  · exact hci
  · exfalso
    have hci_lt : c i₀ ≤ b - 1 := by have := hle i₀; omega
    have hmid : ∀ k : Fin w, i₀.val < k.val → k.val < j₀.val →
                addCfg c (carryEchoBeta b w) k ≤ b := by
      intro k hk1 hk2
      unfold addCfg carryEchoBeta
      have h1 : k.val ≠ 0 := by omega
      have h2 : k.val + 1 ≠ w := by omega
      simp [h1, h2]; exact hle k
    have hleft : addCfg c (carryEchoBeta b w) i₀ ≤
                 b - 1 + (if h : 0 < i₀.val then 1 - oneCfg w ⟨i₀.val - 1, by omega⟩ else 1) := by
      unfold addCfg carryEchoBeta oneCfg
      have hnot_top : i₀.val + 1 ≠ w := by omega
      simp only [hnot_top, ite_false, Nat.add_zero]
      by_cases h0 : 0 < i₀.val
      · have hne0 : i₀.val ≠ 0 := by omega
        simp [h0, hne0]; omega
      · have heq0 : i₀.val = 0 := by omega
        simp [heq0]; omega
    have hright : addCfg c (carryEchoBeta b w) j₀ ≤
                  (if h : j₀.val + 1 < w then b * (1 - oneCfg w ⟨j₀.val + 1, h⟩) else b) := by
      unfold addCfg carryEchoBeta oneCfg
      have hne0 : j₀.val ≠ 0 := by omega
      simp only [hne0, ite_false, Nat.zero_add, hcj0]
      by_cases hw : j₀.val + 1 < w
      · have hnot_top : j₀.val + 1 ≠ w := by omega
        simp [hw, hnot_top]
      · have htop : j₀.val + 1 = w := by omega
        simp [htop]
    have hzero := carryEcho_barrier_lemma hb i₀ j₀ hij hburn (fun _ => Nat.le_refl 1) hmid hleft hright
    simp [oneCfg] at hzero

/-! ### Canonical Skew-Base-b Uniqueness, Greedy Encoder & Injectivity -/

theorem skewWeight_lt_repunit {b w : Nat} (hb : 2 ≤ b) {d : Fin w → Nat}
    (hcanon : IsSkewCanon b w d) :
    skewWeight b w d < repunit b (w + 1) := by
  induction w with
  | zero =>
    unfold skewWeight dot finSum
    exact repunit_pos b 1 (Nat.succ_pos 0)
  | succ w ih =>
    unfold skewWeight dot finSum
    let d' : Fin w → Nat := fun i => d i.castSucc
    have hd'_canon : IsSkewCanon b w d' := by
      refine ⟨fun i => hcanon.1 i.castSucc, fun i j hij hjb => ?_⟩
      exact hcanon.2 i.castSucc j.castSucc hij hjb
    have htop_le : d ⟨w, Nat.lt_succ_self w⟩ ≤ b := hcanon.1 ⟨w, Nat.lt_succ_self w⟩
    by_cases htop_eq : d ⟨w, Nat.lt_succ_self w⟩ = b
    · have hzero : finSum w (fun i => d i.castSucc * repunit b (i.castSucc.val + 1)) = 0 := by
        have hc : finSum w (fun i => d i.castSucc * repunit b (i.castSucc.val + 1)) =
                  finSum w (fun _ => 0) := by
          apply finSum_congr
          intro i
          have hdi : d i.castSucc = 0 := hcanon.2 i.castSucc ⟨w, Nat.lt_succ_self w⟩ i.isLt htop_eq
          simp [hdi]
        rw [hc, finSum_zero]
      dsimp only
      rw [hzero, Nat.zero_add, htop_eq]
      simp only [repunit]
      omega
    · have htop_lt : d ⟨w, Nat.lt_succ_self w⟩ ≤ b - 1 := by omega
      have hlow : skewWeight b w d' < repunit b (w + 1) := ih hd'_canon
      change skewWeight b w d' + d ⟨w, Nat.lt_succ_self w⟩ * repunit b (w + 1) < repunit b (w + 2)
      have hmul : d ⟨w, Nat.lt_succ_self w⟩ * repunit b (w + 1) ≤ (b - 1) * repunit b (w + 1) :=
        Nat.mul_le_mul_right _ htop_lt
      have hstep : (b - 1) * repunit b (w + 1) + repunit b (w + 1) = b * repunit b (w + 1) := by
        have := (Nat.add_mul (b - 1) 1 (repunit b (w + 1))).symm
        rw [Nat.one_mul] at this
        have hb1 : b - 1 + 1 = b := by omega
        rw [hb1] at this; exact this
      have hrep : repunit b (w + 2) = b * repunit b (w + 1) + 1 := rfl
      omega

theorem skewWeight_inj {b w : Nat} (hb : 2 ≤ b) {d₁ d₂ : Fin w → Nat}
    (h1 : IsSkewCanon b w d₁) (h2 : IsSkewCanon b w d₂)
    (heq : skewWeight b w d₁ = skewWeight b w d₂) :
    d₁ = d₂ := by
  induction w with
  | zero =>
    funext i; exact Fin.elim0 i
  | succ w ih =>
    unfold skewWeight dot finSum at heq
    let d₁' : Fin w → Nat := fun i => d₁ i.castSucc
    let d₂' : Fin w → Nat := fun i => d₂ i.castSucc
    have h1' : IsSkewCanon b w d₁' := ⟨fun i => h1.1 i.castSucc, fun i j hij hjb => h1.2 i.castSucc j.castSucc hij hjb⟩
    have h2' : IsSkewCanon b w d₂' := ⟨fun i => h2.1 i.castSucc, fun i j hij hjb => h2.2 i.castSucc j.castSucc hij hjb⟩
    have hlt1 : skewWeight b w d₁' < repunit b (w + 1) := skewWeight_lt_repunit hb h1'
    have hlt2 : skewWeight b w d₂' < repunit b (w + 1) := skewWeight_lt_repunit hb h2'
    change skewWeight b w d₁' + d₁ ⟨w, Nat.lt_succ_self w⟩ * repunit b (w + 1) =
           skewWeight b w d₂' + d₂ ⟨w, Nat.lt_succ_self w⟩ * repunit b (w + 1) at heq
    have htop : d₁ ⟨w, Nat.lt_succ_self w⟩ = d₂ ⟨w, Nat.lt_succ_self w⟩ := by
      by_cases hlt : d₁ ⟨w, Nat.lt_succ_self w⟩ < d₂ ⟨w, Nat.lt_succ_self w⟩
      · exfalso
        have hle : (d₁ ⟨w, Nat.lt_succ_self w⟩ + 1) * repunit b (w + 1) ≤
                   d₂ ⟨w, Nat.lt_succ_self w⟩ * repunit b (w + 1) :=
          Nat.mul_le_mul_right _ hlt
        rw [Nat.add_mul, Nat.one_mul] at hle
        omega
      · by_cases hgt : d₂ ⟨w, Nat.lt_succ_self w⟩ < d₁ ⟨w, Nat.lt_succ_self w⟩
        · exfalso
          have hle : (d₂ ⟨w, Nat.lt_succ_self w⟩ + 1) * repunit b (w + 1) ≤
                     d₁ ⟨w, Nat.lt_succ_self w⟩ * repunit b (w + 1) :=
            Nat.mul_le_mul_right _ hgt
          rw [Nat.add_mul, Nat.one_mul] at hle
          omega
        · omega
    have hlow_eq : skewWeight b w d₁' = skewWeight b w d₂' := by rw [htop] at heq; omega
    have hlow : d₁' = d₂' := ih h1' h2' hlow_eq
    funext i
    by_cases hi : i.val = w
    · have hieq : i = ⟨w, Nat.lt_succ_self w⟩ := Fin.ext hi
      rw [hieq]; exact htop
    · have hilt : i.val < w := by omega
      have hieq : i = (⟨i.val, hilt⟩ : Fin w).castSucc := Fin.ext rfl
      rw [hieq]
      exact congrFun hlow ⟨i.val, hilt⟩

def dualCfg (b w : Nat) (c : Fin w → Nat) : Fin w → Nat := fun i => b - c i

theorem dualCfg_isSkewCanon {b w : Nat} {c : Fin w → Nat} (hc : IsDualSkew b w c) :
    IsSkewCanon b w (dualCfg b w c) := by
  refine ⟨fun i => by unfold dualCfg; omega, ?_⟩
  intro i j hij hjb
  unfold dualCfg at hjb ⊢
  have hle_j := hc.1 j
  have hcj0 : c j = 0 := by omega
  have hci : c i = b := hc.2 i j hij hcj0
  omega

theorem dualCfg_skewWeight_add {b w : Nat} {c : Fin w → Nat} (hle : ∀ i, c i ≤ b) :
    skewWeight b w c + skewWeight b w (dualCfg b w c) =
    skewWeight b w (carryEchoSys b w).maxStable := by
  unfold skewWeight dot dualCfg AbelianToppleSys.maxStable carryEchoSys
  rw [← finSum_add]
  apply finSum_congr
  intro i
  rw [← Nat.add_mul]
  have hi := hle i
  have hsub : c i + (b - c i) = b + 1 - 1 := by omega
  rw [hsub]

theorem carryEcho_H_inj_on_dualSkew {b w : Nat} (hb : 2 ≤ b) {c₁ c₂ : Fin w → Nat}
    (h1 : IsDualSkew b w c₁) (h2 : IsDualSkew b w c₂)
    (hmod : skewWeight b w c₁ % repunit b (w + 1) = skewWeight b w c₂ % repunit b (w + 1)) :
    c₁ = c₂ := by
  let M := repunit b (w + 1)
  have hMpos : 0 < M := repunit_pos b (w + 1) (Nat.succ_pos w)
  have hd1 := dualCfg_isSkewCanon h1
  have hd2 := dualCfg_isSkewCanon h2
  have hlt1 : skewWeight b w (dualCfg b w c₁) < M := skewWeight_lt_repunit hb hd1
  have hlt2 : skewWeight b w (dualCfg b w c₂) < M := skewWeight_lt_repunit hb hd2
  have hadd1 := dualCfg_skewWeight_add h1.1
  have hadd2 := dualCfg_skewWeight_add h2.1
  have hsum_eq : skewWeight b w c₁ + skewWeight b w (dualCfg b w c₁) =
                 skewWeight b w c₂ + skewWeight b w (dualCfg b w c₂) := by
    rw [hadd1, hadd2]
  have hmod_add : (skewWeight b w c₁ + skewWeight b w (dualCfg b w c₁)) % M =
                  (skewWeight b w c₂ + skewWeight b w (dualCfg b w c₂)) % M :=
    congrArg (· % M) hsum_eq
  rw [Nat.add_mod, Nat.add_mod (skewWeight b w c₂), hmod,
      Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod_add
  have hmod_c2 : skewWeight b w c₂ % M < M := Nat.mod_lt _ hMpos
  have hd_eq_val : skewWeight b w (dualCfg b w c₁) = skewWeight b w (dualCfg b w c₂) := by
    let a := skewWeight b w c₂ % M
    let x := skewWeight b w (dualCfg b w c₁)
    let y := skewWeight b w (dualCfg b w c₂)
    change (a + x) % M = (a + y) % M at hmod_add
    by_cases hax : a + x < M
    · by_cases hay : a + y < M
      · rw [Nat.mod_eq_of_lt hax, Nat.mod_eq_of_lt hay] at hmod_add; omega
      · have hsub : a + y - M < M := by omega
        have hmy : (a + y) % M = a + y - M := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsub]
        rw [Nat.mod_eq_of_lt hax, hmy] at hmod_add; omega
    · have hsubx : a + x - M < M := by omega
      have hmx : (a + x) % M = a + x - M := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsubx]
      by_cases hay : a + y < M
      · rw [hmx, Nat.mod_eq_of_lt hay] at hmod_add; omega
      · have hsuby : a + y - M < M := by omega
        have hmy : (a + y) % M = a + y - M := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsuby]
        rw [hmx, hmy] at hmod_add; omega
  have hd_eq : dualCfg b w c₁ = dualCfg b w c₂ := skewWeight_inj hb hd1 hd2 hd_eq_val
  funext i
  have hdi : b - c₁ i = b - c₂ i := congrFun hd_eq i
  have hle1 := h1.1 i
  have hle2 := h2.1 i
  omega

/-! ### Lifting E_{b, w} Through `HarmonicGroupCert` (∀ b ≥ 2, ∀ w ≥ 1) -/

def carryEchoGroupCert (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) :
    (carryEchoSys b w).HarmonicGroupCert (carryEchoM1Pot b w hb) where
  beta := carryEchoBeta b w
  burn_mu := carryEcho_maxStable_burns b w hb
  M := repunit b (w + 1)
  M_pos := repunit_pos b (w + 1) (Nat.succ_pos w)
  Hbal := carryEchoHBal b w
  H_mod_dvd := fun i => by
    change repunit b (w + 1) ∣ (if i.val + 1 = w then repunit b (w + 1) else 0)
    split
    · exact Nat.dvd_refl _
    · exact Nat.dvd_zero _
  gen := ⟨0, hw⟩
  gen_unit := by
    change repunit b (0 + 1) % repunit b (w + 1) = 1 % repunit b (w + 1)
    simp [repunit]
  Pred := IsDualSkew b w
  burn_implies_Pred := carryEcho_burn_implies_dualSkew hb
  H_inj_on_Pred := fun c₁ c₂ h1 h2 hmod => carryEcho_H_inj_on_dualSkew hb h1 h2 hmod

def skewEncode (b : Nat) : (w : Nat) → Nat → Fin w → Nat
  | 0, _ => Fin.elim0
  | w + 1, n =>
    let r := repunit b (w + 1)
    let q := n / r
    let rem := n % r
    fun i =>
      if h : i.val < w then
        skewEncode b w rem ⟨i.val, h⟩
      else
        q

/-- Explicit closed-form identity element of E_{b, w} for all b ≥ 2, w ≥ 1:
    e_{b, w}(i) = b - skewEncode(b, w, H_b(μ_w) mod R_{b, w+1})(i). -/
def explicitIdentity (b w : Nat) : Fin w → Nat :=
  let M := repunit b (w + 1)
  let hmu := skewWeight b w (carryEchoSys b w).maxStable
  fun i => b - skewEncode b w (hmu % M) i

end CarryEcho

section DirectedCarry


/-- Pure Directed Radix-b Carry Sandpile D_{b, w}:
    threshold b at every bit position; firing bit i sends 1 chip to i+1 (and 0 down). -/
def directedCarrySys (b w : Nat) (hb : 2 ≤ b) : AbelianToppleSys w where
  tau := fun _ => b
  tau_pos := fun _ => by omega
  A := fun i j => if j.val = i.val + 1 then 1 else 0
  A_diag := fun i => by simp

theorem dot_directedCarry_row (b w : Nat) (hb : 2 ≤ b) (p : Fin w → Nat) (i : Fin w) :
    dot w (fun j => (directedCarrySys b w hb).A i j) p =
    if h : i.val + 1 < w then p ⟨i.val + 1, h⟩ else 0 := by
  unfold dot directedCarrySys
  dsimp only
  by_cases h : i.val + 1 < w
  · simp only [h, dite_true]
    let idx : Fin w := ⟨i.val + 1, h⟩
    have hc : finSum w (fun j => (if j.val = i.val + 1 then 1 else 0) * p j) =
              finSum w (fun j => if j = idx then p idx else 0) := by
      apply finSum_congr
      intro j
      by_cases hje : j = idx
      · subst hje; simp [idx]
      · have hv : j.val ≠ i.val + 1 := fun hv => hje (Fin.ext hv)
        simp [hje, hv]
    rw [hc, finSum_single]
  · simp only [h, dite_false]
    have hc : finSum w (fun j => (if j.val = i.val + 1 then 1 else 0) * p j) =
              finSum w (fun _ => 0) := by
      apply finSum_congr
      intro j
      have hv : j.val ≠ i.val + 1 := by omega
      simp [hv]
    rw [hc, finSum_zero]

/-- Strict potential W(c) = sum c_i for D_{b, w} (gives Legendre/Kummer carry conservation!). -/
def directedCarryMassPot (b w : Nat) (hb : 2 ≤ b) : (directedCarrySys b w hb).StrictPotential where
  p := fun _ => 1
  delta := fun i => if i.val + 1 = w then b else b - 1
  balance := fun i => by
    rw [dot_directedCarry_row]
    change b * 1 = (if i.val + 1 = w then b else b - 1) + (if h : i.val + 1 < w then 1 else 0)
    by_cases h : i.val + 1 < w
    · have hne : i.val + 1 ≠ w := by omega
      simp only [hne, ite_false, h, dite_true]; omega
    · have heq : i.val + 1 = w := by omega
      simp only [h, dite_false]
      simp only [heq, ite_true]; omega
  delta_pos := fun i => by split <;> omega

/-- Harmonic value balance Φ_b(c) = sum c_i * b^i for D_{b, w} (drops only at MSB by b^w). -/
def directedCarryPhiBal (b w : Nat) (hb : 2 ≤ b) : (directedCarrySys b w hb).LinearBalance where
  p := fun i => b ^ i.val
  delta := fun i => if i.val + 1 = w then b ^ w else 0
  balance := fun i => by
    rw [dot_directedCarry_row]
    change b * b ^ i.val = (if i.val + 1 = w then b ^ w else 0) +
                           (if h : i.val + 1 < w then b ^ (i.val + 1) else 0)
    by_cases h : i.val + 1 < w
    · have hne : i.val + 1 ≠ w := by omega
      simp only [hne, ite_false, h, dite_true, Nat.pow_succ']; omega
    · have heq : i.val + 1 = w := by omega
      simp only [h, dite_false]
      simp only [heq, ite_true]
      have hpow : b ^ w = b * b ^ i.val := by
        have h1 : b ^ w = b ^ (i.val + 1) := congrArg (b ^ ·) heq.symm
        rw [h1, Nat.pow_succ']
      rw [hpow, Nat.add_zero]

def directedCarryBeta (b w : Nat) : Fin w → Nat :=
  fun i => if i.val = 0 then b else b - 1

def dcSweepState (b w k : Nat) : Fin w → Nat :=
  fun j =>
    if j.val < k then b - 1
    else if j.val = k then (b - 1) + b
    else (b - 1) + (b - 1)

theorem dcSweep_step (b w k : Nat) (hb : 2 ≤ b) (hk : k < w) :
    (directedCarrySys b w hb).Step (dcSweepState b w k) ⟨k, hk⟩ (dcSweepState b w (k + 1)) := by
  refine ⟨?_, ?_⟩
  · change b ≤ dcSweepState b w k ⟨k, hk⟩
    unfold dcSweepState; simp
  · funext j
    unfold AbelianToppleSys.fire directedCarrySys dcSweepState
    dsimp only
    by_cases hjk : j = ⟨k, hk⟩
    · subst hjk; simp
    · have hne : j.val ≠ k := fun h => hjk (Fin.ext h)
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hjk h))]
      by_cases hjlt : j.val < k
      · have hjlt1 : j.val < k + 1 := by omega
        have hnot1 : j.val ≠ k + 1 := by omega
        simp [hjlt, hjlt1, hnot1]
      · by_cases hjeq1 : j.val = k + 1
        · have hjnot1 : ¬ (j.val < k + 1) := by omega
          simp only [hjnot1, hjlt, hne, ite_false]
          simp only [hjeq1, ite_true]
          omega
        · have hjnot1 : ¬ (j.val < k + 1) := by omega
          simp [hjlt, hne, hjeq1, hjnot1]

theorem dcSweep_steps (b w k : Nat) (hb : 2 ≤ b) (hk : k ≤ w) :
    (directedCarrySys b w hb).Steps (dcSweepState b w k)
      (fun j => if k ≤ j.val then 1 else 0)
      (dcSweepState b w w) := by
  obtain ⟨d, hd⟩ : ∃ d, w = k + d := ⟨w - k, by omega⟩
  induction d generalizing k with
  | zero =>
    have hkw : k = w := by omega
    subst hkw
    have h0 : (fun j : Fin k => if k ≤ j.val then 1 else 0) = zeroCfg k := by
      funext j
      have hnge : ¬ (k ≤ j.val) := Nat.not_le_of_lt j.isLt
      simp [zeroCfg, hnge]
    rw [h0]; exact AbelianToppleSys.Steps.refl _
  | succ d ih =>
    have hklt : k < w := by omega
    have hs := dcSweep_step b w k hb hklt
    have hrest := ih (k + 1) (by omega) (by omega)
    have hodom : addCfg (singleCfg ⟨k, hklt⟩ 1) (fun j : Fin w => if k + 1 ≤ j.val then 1 else 0) =
                 (fun j : Fin w => if k ≤ j.val then 1 else 0) := by
      funext j
      simp only [addCfg, singleCfg]
      by_cases hjk : j = ⟨k, hklt⟩
      · subst hjk; simp
      · have hv : j.val ≠ k := fun h => hjk (Fin.ext h)
        by_cases hge : k ≤ j.val
        · have hge1 : k + 1 ≤ j.val := by omega
          simp [hjk, hge, hge1]
        · have hnge1 : ¬ (k + 1 ≤ j.val) := by omega
          simp [hjk, hge, hnge1]
    rw [← hodom]
    exact AbelianToppleSys.Steps.step hs hrest

theorem directedCarry_maxStable_burns (b w : Nat) (hb : 2 ≤ b) :
    (directedCarrySys b w hb).Steps
      (addCfg (directedCarrySys b w hb).maxStable (directedCarryBeta b w))
      (oneCfg w)
      (directedCarrySys b w hb).maxStable := by
  have hstart : dcSweepState b w 0 = addCfg (directedCarrySys b w hb).maxStable (directedCarryBeta b w) := by
    funext j
    unfold dcSweepState addCfg AbelianToppleSys.maxStable directedCarrySys directedCarryBeta
    by_cases hj0 : j.val = 0
    · simp [hj0]
    · simp [hj0]
  have hend : dcSweepState b w w = (directedCarrySys b w hb).maxStable := by
    funext j
    unfold dcSweepState AbelianToppleSys.maxStable directedCarrySys
    simp [j.isLt]
  have h1 : (fun j : Fin w => if 0 ≤ j.val then 1 else 0) = oneCfg w := by
    funext j; simp [oneCfg]
  have hsteps := dcSweep_steps b w 0 hb (Nat.zero_le w)
  rw [hstart, hend, h1] at hsteps
  exact hsteps

theorem baseValue_lt_pow {b w : Nat} {c : Fin w → Nat} (h : ∀ i, c i < b) :
    baseValue b w c < b ^ w := by
  induction w with
  | zero =>
    unfold baseValue dot finSum; simp
  | succ w ih =>
    unfold baseValue dot finSum
    have hlow := ih (fun i => h i.castSucc)
    have htop : c ⟨w, Nat.lt_succ_self w⟩ ≤ b - 1 := by have := h ⟨w, Nat.lt_succ_self w⟩; omega
    have hmul : c ⟨w, Nat.lt_succ_self w⟩ * b ^ w ≤ (b - 1) * b ^ w := Nat.mul_le_mul_right _ htop
    have h1 : (b - 1) * b ^ w + b ^ w = b * b ^ w := by
      have := (Nat.add_mul (b - 1) 1 (b ^ w)).symm
      rw [Nat.one_mul] at this
      have hb1 : b - 1 + 1 = b := by have := h ⟨w, Nat.lt_succ_self w⟩; omega
      rw [hb1] at this; exact this
    rw [Nat.pow_succ']
    change baseValue b w (fun i => c i.castSucc) + c ⟨w, Nat.lt_succ_self w⟩ * b ^ w < b * b ^ w
    omega

theorem baseValue_inj {b w : Nat} {c₁ c₂ : Fin w → Nat}
    (h1 : ∀ i, c₁ i < b) (h2 : ∀ i, c₂ i < b)
    (heq : baseValue b w c₁ = baseValue b w c₂) : c₁ = c₂ := by
  induction w with
  | zero => funext i; exact Fin.elim0 i
  | succ w ih =>
    unfold baseValue dot finSum at heq
    let c₁' : Fin w → Nat := fun i => c₁ i.castSucc
    let c₂' : Fin w → Nat := fun i => c₂ i.castSucc
    have hlt1 : baseValue b w c₁' < b ^ w := baseValue_lt_pow (fun i => h1 i.castSucc)
    have hlt2 : baseValue b w c₂' < b ^ w := baseValue_lt_pow (fun i => h2 i.castSucc)
    change baseValue b w c₁' + c₁ ⟨w, Nat.lt_succ_self w⟩ * b ^ w =
           baseValue b w c₂' + c₂ ⟨w, Nat.lt_succ_self w⟩ * b ^ w at heq
    have htop : c₁ ⟨w, Nat.lt_succ_self w⟩ = c₂ ⟨w, Nat.lt_succ_self w⟩ := by
      by_cases hlt : c₁ ⟨w, Nat.lt_succ_self w⟩ < c₂ ⟨w, Nat.lt_succ_self w⟩
      · exfalso
        have hle : (c₁ ⟨w, Nat.lt_succ_self w⟩ + 1) * b ^ w ≤ c₂ ⟨w, Nat.lt_succ_self w⟩ * b ^ w :=
          Nat.mul_le_mul_right _ hlt
        rw [Nat.add_mul, Nat.one_mul] at hle; omega
      · by_cases hgt : c₂ ⟨w, Nat.lt_succ_self w⟩ < c₁ ⟨w, Nat.lt_succ_self w⟩
        · exfalso
          have hle : (c₂ ⟨w, Nat.lt_succ_self w⟩ + 1) * b ^ w ≤ c₁ ⟨w, Nat.lt_succ_self w⟩ * b ^ w :=
            Nat.mul_le_mul_right _ hgt
          rw [Nat.add_mul, Nat.one_mul] at hle; omega
        · omega
    have hlow : c₁' = c₂' := ih (fun i => h1 i.castSucc) (fun i => h2 i.castSucc) (by rw [htop] at heq; omega)
    funext i
    by_cases hi : i.val = w
    · have hieq : i = ⟨w, Nat.lt_succ_self w⟩ := Fin.ext hi
      rw [hieq]; exact htop
    · have hilt : i.val < w := by omega
      have hieq : i = (⟨i.val, hilt⟩ : Fin w).castSucc := Fin.ext rfl
      rw [hieq]; exact congrFun hlow ⟨i.val, hilt⟩

/-- Second Instantiation of `HarmonicGroupCert`: Directed Radix-b Carry D_{b, w}. -/
def directedCarryGroupCert (b w : Nat) (hb : 2 ≤ b) (hw : 0 < w) :
    (directedCarrySys b w hb).HarmonicGroupCert (directedCarryMassPot b w hb) where
  beta := directedCarryBeta b w
  burn_mu := directedCarry_maxStable_burns b w hb
  M := b ^ w
  M_pos := pow_ge_one b w (by omega)
  Hbal := directedCarryPhiBal b w hb
  H_mod_dvd := fun i => by
    change b ^ w ∣ (if i.val + 1 = w then b ^ w else 0)
    split
    · exact Nat.dvd_refl _
    · exact Nat.dvd_zero _
  gen := ⟨0, hw⟩
  gen_unit := by simp [directedCarryPhiBal]
  Pred := (directedCarrySys b w hb).IsStable
  burn_implies_Pred := fun _ hstab _ => hstab
  H_inj_on_Pred := fun c₁ c₂ h1 h2 hmod => by
    have hlt1 : baseValue b w c₁ < b ^ w := baseValue_lt_pow h1
    have hlt2 : baseValue b w c₂ < b ^ w := baseValue_lt_pow h2
    change baseValue b w c₁ % b ^ w = baseValue b w c₂ % b ^ w at hmod
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
    exact baseValue_inj h1 h2 hmod

end DirectedCarry

section WitnessesAndSharpness


/-- Helper: concrete vector constructors for small widths (for readable kernel witnesses). -/
def vec1 (a : Nat) : Fin 1 → Nat := fun _ => a

def vec2 (a b : Nat) : Fin 2 → Nat := fun i => if i.val = 0 then a else b

def vec3 (a b c : Nat) : Fin 3 → Nat := fun i =>
  if i.val = 0 then a else if i.val = 1 then b else c

def vec4 (a b c d : Nat) : Fin 4 → Nat := fun i =>
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d

def vec5 (a b c d e : Nat) : Fin 5 → Nat := fun i =>
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else if i.val = 3 then d else e

/-! ### 5.1 Non-Vacuity Witnesses (Certificates Inhabited & Concrete Identites Verified) -/

/-- Counterexample C4 (Sharpness of boundary dissipation / `StrictPotential`):
    Wrapping 1-up + 2-down cyclically on w = 2 gives conservative system `cyclicCarryEcho2`
    with tau = 3, A(0,1) = 3, A(1,0) = 3. It admits NO `StrictPotential` AND enters an
    unbounded infinite cycle `(3, 0) → (0, 3) → (3, 0)` of arbitrary firing count `2n`. -/
def cyclicCarryEcho2 : AbelianToppleSys 2 where
  tau := fun _ => 3
  tau_pos := fun _ => by omega
  A := fun i j => if i = j then 0 else 3
  A_diag := fun i => by simp

end WitnessesAndSharpness

end SiliconSandpile
