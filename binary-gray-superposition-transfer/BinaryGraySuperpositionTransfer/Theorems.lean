import BinaryGraySuperpositionTransfer.Defs

set_option autoImplicit false

namespace BitTransfer3
theorem pEval_const (c q : Int) : pEval (pConst c) q = c := by
  simp [pConst, pEval]

theorem pEval_var (q : Int) : pEval pVar q = q := by
  simp [pVar, pEval]

theorem pEval_lin (q0 q : Int) : pEval (pLin q0) q = q - q0 := by
  simp [pLin, pEval]; grind

theorem pEval_add (p r : Poly) (q : Int) :
    pEval (pAdd p r) q = pEval p q + pEval r q := by
  induction p generalizing r with
  | nil => simp [pAdd, pEval]
  | cons a as ih =>
    cases r with
    | nil => simp [pAdd, pEval]
    | cons b bs => simp [pAdd, pEval, ih]; grind

theorem pEval_neg (p : Poly) (q : Int) :
    pEval (pNeg p) q = -pEval p q := by
  induction p with
  | nil => simp [pNeg, pEval]
  | cons a as ih => simp [pNeg, pEval, ih]; grind

theorem pEval_sub (p r : Poly) (q : Int) :
    pEval (pSub p r) q = pEval p q - pEval r q := by
  simp [pSub, pEval_add, pEval_neg]; grind

theorem pEval_scale (c : Int) (p : Poly) (q : Int) :
    pEval (pScale c p) q = c * pEval p q := by
  induction p with
  | nil => simp [pScale, pEval]
  | cons a as ih => simp [pScale, pEval, ih]; grind

theorem pEval_mul (p r : Poly) (q : Int) :
    pEval (pMul p r) q = pEval p q * pEval r q := by
  induction p with
  | nil => simp [pMul, pEval]
  | cons a as ih =>
    simp [pMul, pEval_add, pEval_scale, pEval, ih]
    grind

theorem pEval_horner (p : Poly) (a q : Int) :
    pEval p q = pEval p a + (q - a) * pEval (pQuotLin p a) q := by
  induction p with
  | nil => simp [pQuotLin, pEval]
  | cons c cs ih =>
    simp only [pQuotLin, pEval_add, pEval]
    have h := ih
    grind

/-- Exact polynomial cancellation of a linear factor `(q - a)` in `ℤ[q]`. -/
theorem pEval_cancel_lin (p r : Poly) (a : Int)
    (h : ∀ q : Int, (q - a) * pEval p q = (q - a) * pEval r q) :
    ∀ q : Int, pEval p q = pEval r q := by
  have hne : ∀ q : Int, q ≠ a → pEval p q = pEval r q := by
    intro q hqa
    have hq : q - a ≠ 0 := by omega
    have h0 := h q
    have h1 : (q - a) * (pEval p q - pEval r q) = 0 := by grind
    rcases Int.mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hq
    · omega
  intro q
  by_cases hqa : q = a
  · subst hqa
    -- Evaluate `p - r` at `a + m` where `m = |p(a) - r(a)| + 1 > 0`
    let D := pSub p r
    let d0 := pEval D q
    let m : Int := Int.natAbs d0 + 1
    have hm_pos : m > 0 := by omega
    have hneq : q + m ≠ q := by omega
    have hzero : pEval D (q + m) = 0 := by
      simp [D, pEval_sub, hne (q + m) hneq]
    have hhorn := pEval_horner D q (q + m)
    have hmul : d0 + m * pEval (pQuotLin D q) (q + m) = 0 := by
      have : (q + m) - q = m := by omega
      rw [hzero, this] at hhorn
      exact hhorn.symm
    let k := pEval (pQuotLin D q) (q + m)
    have hd0 : d0 = -(m * k) := by
      have : d0 + m * k = 0 := hmul
      omega
    have hk0 : k = 0 := by
      cases hk : Int.natAbs k with
      | zero => exact Int.natAbs_eq_zero.mp hk
      | succ k' =>
        have hge1 : 1 ≤ Int.natAbs k := by omega
        have habs : Int.natAbs d0 = Int.natAbs m * Int.natAbs k := by
          rw [hd0, Int.natAbs_neg, Int.natAbs_mul]
        have hm_abs : Int.natAbs m = Int.natAbs d0 + 1 := by omega
        rw [hm_abs] at habs
        have hmul_le : (Int.natAbs d0 + 1) * 1 ≤ (Int.natAbs d0 + 1) * Int.natAbs k :=
          Nat.mul_le_mul_left _ hge1
        omega
    have hd0_zero : d0 = 0 := by rw [hd0, hk0]; simp
    have : pEval p q - pEval r q = 0 := by simpa [D, d0, pEval_sub] using hd0_zero
    omega
  · exact hne q hqa

theorem pEval_linPow (q0 : Int) (n : Nat) (q : Int) :
    pEval (pLinPow q0 n) q = (q - q0) ^ n := by
  induction n with
  | zero => simp [pLinPow, pEval]
  | succ n ih =>
    simp only [pLinPow, pEval_mul, pEval_lin, ih, Int.pow_succ]
    grind

theorem hasLeadAt_to_ge {p : Poly} {q0 : Int} {d : Nat} {c : Int}
    (h : HasLeadAt p q0 d c) : HasOrderGe p q0 d := by
  rcases h with ⟨r, hr⟩
  refine ⟨pAdd (pConst c) (pMul (pLin q0) r), fun q => ?_⟩
  rw [hr q, pEval_add, pEval_const, pEval_mul, pEval_lin, Int.pow_succ]
  grind

theorem hasLeadAt_of_cancel {p : Poly} {q0 : Int} {d : Nat} {c : Int}
    (h : ∃ r : Poly, ∀ q : Int,
      (q - q0) * pEval p q = (q - q0) * (c * (q - q0) ^ d + (q - q0) ^ (d + 1) * pEval r q)) :
    HasLeadAt p q0 d c := by
  rcases h with ⟨r, hr⟩
  let rhs : Poly := pAdd (pScale c (pLinPow q0 d)) (pMul (pLinPow q0 (d + 1)) r)
  refine ⟨r, fun q => ?_⟩
  have hcancel := pEval_cancel_lin p rhs q0 (fun q' => by
    rw [hr q']
    simp only [rhs, pEval_add, pEval_scale, pEval_mul, pEval_linPow])
  simpa only [rhs, pEval_add, pEval_scale, pEval_mul, pEval_linPow] using hcancel q

theorem hasLeadAt_of_cancel_two {p : Poly} {q0 a : Int} {d : Nat} {c : Int}
    (h : ∃ r : Poly, ∀ q : Int,
      (q - a) * ((q - q0) * pEval p q) =
      (q - a) * ((q - q0) * (c * (q - q0) ^ d + (q - q0) ^ (d + 1) * pEval r q))) :
    HasLeadAt p q0 d c := by
  rcases h with ⟨r, hr⟩
  let rhs : Poly := pAdd (pScale c (pLinPow q0 d)) (pMul (pLinPow q0 (d + 1)) r)
  have hstep1 := pEval_cancel_lin (pMul (pLin q0) p) (pMul (pLin q0) rhs) a (fun q' => by
    simp only [pEval_mul, pEval_lin]
    rw [hr q']
    simp only [rhs, pEval_add, pEval_scale, pEval_mul, pEval_linPow])
  have hstep2 := pEval_cancel_lin p rhs q0 (fun q' => by
    simpa only [pEval_mul, pEval_lin] using hstep1 q')
  refine ⟨r, fun q => ?_⟩
  simpa only [rhs, pEval_add, pEval_scale, pEval_mul, pEval_linPow] using hstep2 q


-- ============================================================================
-- SECTION 2: Reusable Finite-Sum & Fubini Primitives (Zero Mathlib)
-- ============================================================================

theorem sumFinInt_ofNat (q : Nat) (f : Fin q → Nat) :
    (sumFin q f : Int) = sumFinInt q (fun i => (f i : Int)) := by
  induction q with
  | zero => rfl
  | succ q' ih =>
    simp only [sumFin, sumFinInt, Int.natCast_add]
    rw [ih]

theorem sumFinInt_congr {q : Nat} {f g : Fin q → Int} (h : ∀ i, f i = g i) :
    sumFinInt q f = sumFinInt q g := by
  induction q with
  | zero => rfl
  | succ q' ih =>
    simp only [sumFinInt]
    rw [ih (fun i => h i.castSucc), h (Fin.last q')]

theorem sumFinInt_add {q : Nat} (f g : Fin q → Int) :
    sumFinInt q (fun i => f i + g i) = sumFinInt q f + sumFinInt q g := by
  induction q with
  | zero => simp [sumFinInt]
  | succ q' ih =>
    simp only [sumFinInt]
    rw [ih]
    grind

theorem sumFinInt_const (q : Nat) (c : Int) :
    sumFinInt q (fun _ => c) = (q : Int) * c := by
  induction q with
  | zero => simp [sumFinInt]
  | succ q' ih =>
    simp only [sumFinInt, ih]
    grind

theorem sumFinInt_single (q : Nat) (x : Fin q) (c : Int) :
    sumFinInt q (fun i => if i = x then c else 0) = c := by
  induction q with
  | zero => exact Fin.elim0 x
  | succ q' ih =>
    simp only [sumFinInt]
    by_cases hx : x = Fin.last q'
    · subst hx
      have h0 : sumFinInt q' (fun i => if i.castSucc = Fin.last q' then c else 0) = 0 := by
        have := sumFinInt_const q' 0
        rw [sumFinInt_congr (g := fun _ => 0)]
        · simpa using this
        · intro i
          have hne : i.castSucc ≠ Fin.last q' := by
            intro h
            have := congrArg Fin.val h
            simp [Fin.castSucc, Fin.last] at this
            omega
          simp [hne]
      rw [h0]
      simp
    · have hlt : x.val < q' := by
        have := x.isLt
        have hne : x.val ≠ q' := fun h => hx (Fin.ext h)
        omega
      let x' : Fin q' := ⟨x.val, hlt⟩
      have hx' : x'.castSucc = x := Fin.ext rfl
      have h1 : sumFinInt q' (fun i => if i.castSucc = x then c else 0) = c := by
        rw [← hx']
        have := ih x'
        rw [sumFinInt_congr (g := fun i => if i = x' then c else 0)]
        · exact this
        · intro i
          have : (i.castSucc = x'.castSucc) ↔ (i = x') := by
            constructor
            · intro h; exact Fin.ext (by simpa [Fin.castSucc] using congrArg Fin.val h)
            · intro h; rw [h]
          simp [this]
      rw [h1]
      have hne' : Fin.last q' ≠ x := Ne.symm hx
      simp [hne']

/-- Core `Nodup`-list splitting lemma for evaluating symbolic `Fin q` sums into polynomials in `q`. -/
theorem sumFinInt_split (q : Nat) (xs : List (Fin q)) (hnd : xs.Nodup)
    (f : Fin q → Int) (c : Int) (hfresh : ∀ d : Fin q, d ∉ xs → f d = c) :
    sumFinInt q f = (xs.map f).sum + ((q : Int) - (xs.length : Int)) * c := by
  induction xs generalizing f with
  | nil =>
    simp only [List.map_nil, List.sum_nil, List.length_nil, Int.natCast_zero, Int.sub_zero,
               Int.zero_add]
    rw [sumFinInt_congr (g := fun _ => c) (fun d => hfresh d (by simp))]
    exact sumFinInt_const q c
  | cons x rest ih =>
    have hnd_cons : x ∉ rest ∧ rest.Nodup := List.nodup_cons.mp hnd
    let f' : Fin q → Int := fun d => if d = x then c else f d
    have hdecomp : ∀ d : Fin q, f d = f' d + (if d = x then f x - c else 0) := by
      intro d
      by_cases hdx : d = x
      · subst hdx; simp [f']; omega
      · simp [f', hdx]
    rw [sumFinInt_congr hdecomp, sumFinInt_add, sumFinInt_single]
    have hfresh' : ∀ d : Fin q, d ∉ rest → f' d = c := by
      intro d hd
      by_cases hdx : d = x
      · simp [f', hdx]
      · simp [f', hdx]
        exact hfresh d (by simp [hdx, hd])
    rw [ih hnd_cons.2 f' hfresh']
    have hmap : rest.map f' = rest.map f := by
      apply List.map_congr_left
      intro d hd
      have hne : d ≠ x := fun h => hnd_cons.1 (h ▸ hd)
      simp [f', hne]
    rw [hmap]
    simp only [List.map_cons, List.sum_cons, List.length_cons, Int.natCast_add, Int.natCast_one]
    grind

-- Helper: append two functions on `Fin n` and `Fin m` into `Fin (n + m)`
theorem appendFun_left {α : Type} {n m : Nat} (fL : Fin n → α) (fR : Fin m → α) (i : Fin n) :
    appendFun fL fR ⟨i.val, by omega⟩ = fL i := by
  simp [appendFun, i.isLt]

theorem appendFun_right {α : Type} {n m : Nat} (fL : Fin n → α) (fR : Fin m → α) (j : Fin m) :
    appendFun fL fR ⟨n + j.val, by omega⟩ = fR j := by
  have hnot : ¬ (n + j.val < n) := by omega
  simp [appendFun, hnot]

theorem appendFun_cons {α : Type} {n m : Nat} (a : α) (fL : Fin n → α) (fR : Fin m → α) :
    (fun i : Fin (n + 1 + m) =>
      appendFun (consFun a fL) fR i) =
    (fun i : Fin (n + 1 + m) =>
      consFun a (appendFun fL fR) ⟨i.val, by omega⟩) := by
  funext i
  by_cases h0 : i.val = 0
  · simp [appendFun, consFun, h0]
  · by_cases hlt : i.val < n + 1
    · have hlt' : i.val - 1 < n := by omega
      simp [appendFun, consFun, h0, hlt, hlt']
    · have hlt' : ¬ (i.val - 1 < n) := by omega
      have hsub : i.val - (n + 1) = (i.val - 1) - n := by omega
      simp [appendFun, consFun, h0, hlt, hlt', hsub]

theorem sumBoolFun_congr {n : Nat} {f g : (Fin n → Bool) → Nat} (h : ∀ x, f x = g x) :
    sumBoolFun n f = sumBoolFun n g := by
  induction n with
  | zero => exact h _
  | succ n ih =>
    simp only [sumBoolFun]
    rw [ih (fun x => h _), ih (fun x => h _)]

theorem sumBoolFun_add {n : Nat} (f g : (Fin n → Bool) → Nat) :
    sumBoolFun n (fun x => f x + g x) = sumBoolFun n f + sumBoolFun n g := by
  induction n with
  | zero => simp [sumBoolFun]
  | succ n ih =>
    simp only [sumBoolFun, ih]
    omega

theorem sumBoolFun_mul_left {n : Nat} (c : Nat) (f : (Fin n → Bool) → Nat) :
    sumBoolFun n (fun x => c * f x) = c * sumBoolFun n f := by
  induction n with
  | zero => simp [sumBoolFun]
  | succ n ih =>
    simp only [sumBoolFun, ih, Nat.mul_add]

theorem sumBoolFun_mul_right {n : Nat} (f : (Fin n → Bool) → Nat) (c : Nat) :
    sumBoolFun n (fun x => f x * c) = sumBoolFun n f * c := by
  induction n with
  | zero => simp [sumBoolFun]
  | succ n ih =>
    simp only [sumBoolFun, ih, Nat.add_mul]

theorem sumBoolFun_cast {k1 k2 : Nat} (heq : k1 = k2) (f : (Fin k1 → Bool) → Nat) :
    sumBoolFun k1 f = sumBoolFun k2 (fun g => f (fun i => g ⟨i.val, by omega⟩)) := by
  subst heq; rfl

/-- Exact Fubini split for `sumBoolFun (n + m)`. -/
theorem sumBoolFun_append (n m : Nat) (f : (Fin (n + m) → Bool) → Nat) :
    sumBoolFun (n + m) f =
      sumBoolFun n (fun gL => sumBoolFun m (fun gR => f (appendFun gL gR))) := by
  induction n with
  | zero =>
    rw [sumBoolFun_cast (Nat.zero_add m) f]
    simp only [sumBoolFun]
    apply sumBoolFun_congr
    intro gR
    have hfun : (fun i : Fin (0 + m) => gR ⟨i.val, by omega⟩) = appendFun (fun i => Fin.elim0 i) gR := by
      funext i; simp [appendFun]
    rw [hfun]
  | succ n ih =>
    have hstep :
        sumBoolFun (n + 1 + m) f =
        sumBoolFun (n + m) (fun g => f (fun i => consFun false g ⟨i.val, by omega⟩)) +
        sumBoolFun (n + m) (fun g => f (fun i => consFun true g ⟨i.val, by omega⟩)) := by
      rw [sumBoolFun_cast (show n + 1 + m = (n + m) + 1 by omega) f]
      rfl
    rw [hstep, ih, ih]
    simp only [sumBoolFun]
    congr 1 <;> apply sumBoolFun_congr <;> intro gL <;> apply sumBoolFun_congr <;> intro gR
    · congr 1; exact (appendFun_cons false gL gR).symm
    · congr 1; exact (appendFun_cons true gL gR).symm

theorem optMax_comm (x y : Option Nat) : optMax x y = optMax y x := by
  cases x <;> cases y <;> simp [optMax, Nat.max_comm]

theorem optMax_assoc (x y z : Option Nat) : optMax (optMax x y) z = optMax x (optMax y z) := by
  cases x <;> cases y <;> cases z <;> simp [optMax, Nat.max_assoc]

theorem optMax_none_left (x : Option Nat) : optMax none x = x := by cases x <;> rfl
theorem optMax_none_right (x : Option Nat) : optMax x none = x := by cases x <;> rfl

theorem optAdd_optMax_left (x y z : Option Nat) :
    optAdd (optMax x y) z = optMax (optAdd x z) (optAdd y z) := by
  cases x <;> cases y <;> cases z <;> simp [optAdd, optMax] <;> omega

theorem optAdd_optMax_right (x y z : Option Nat) :
    optAdd x (optMax y z) = optMax (optAdd x y) (optAdd x z) := by
  cases x <;> cases y <;> cases z <;> simp [optAdd, optMax] <;> omega

theorem maxBoolFun_congr {n : Nat} {f g : (Fin n → Bool) → Option Nat} (h : ∀ x, f x = g x) :
    maxBoolFun n f = maxBoolFun n g := by
  induction n with
  | zero => exact h _
  | succ n ih =>
    simp only [maxBoolFun]
    rw [ih (fun x => h _), ih (fun x => h _)]

theorem maxBoolFun_optMax {n : Nat} (f g : (Fin n → Bool) → Option Nat) :
    maxBoolFun n (fun x => optMax (f x) (g x)) = optMax (maxBoolFun n f) (maxBoolFun n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [maxBoolFun, ih]
    rw [optMax_assoc, optMax_assoc]
    congr 1
    rw [← optMax_assoc (maxBoolFun n _), optMax_comm (maxBoolFun n _) (maxBoolFun n _), optMax_assoc]

theorem maxBoolFun_optAdd_left {n : Nat} (c : Option Nat) (f : (Fin n → Bool) → Option Nat) :
    maxBoolFun n (fun x => optAdd c (f x)) = optAdd c (maxBoolFun n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [maxBoolFun, ih, optAdd_optMax_right]

theorem maxBoolFun_optAdd_right {n : Nat} (f : (Fin n → Bool) → Option Nat) (c : Option Nat) :
    maxBoolFun n (fun x => optAdd (f x) c) = optAdd (maxBoolFun n f) c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [maxBoolFun, ih, optAdd_optMax_left]

theorem maxBoolFun_cast {k1 k2 : Nat} (heq : k1 = k2) (f : (Fin k1 → Bool) → Option Nat) :
    maxBoolFun k1 f = maxBoolFun k2 (fun g => f (fun i => g ⟨i.val, by omega⟩)) := by
  subst heq; rfl

theorem maxBoolFun_append (n m : Nat) (f : (Fin (n + m) → Bool) → Option Nat) :
    maxBoolFun (n + m) f =
      maxBoolFun n (fun gL => maxBoolFun m (fun gR => f (appendFun gL gR))) := by
  induction n with
  | zero =>
    rw [maxBoolFun_cast (Nat.zero_add m) f]
    simp only [maxBoolFun]
    apply maxBoolFun_congr
    intro gR
    have hfun : (fun i : Fin (0 + m) => gR ⟨i.val, by omega⟩) = appendFun (fun i => Fin.elim0 i) gR := by
      funext i; simp [appendFun]
    rw [hfun]
  | succ n ih =>
    have hstep :
        maxBoolFun (n + 1 + m) f =
        optMax (maxBoolFun (n + m) (fun g => f (fun i => consFun false g ⟨i.val, by omega⟩)))
               (maxBoolFun (n + m) (fun g => f (fun i => consFun true g ⟨i.val, by omega⟩))) := by
      rw [maxBoolFun_cast (show n + 1 + m = (n + m) + 1 by omega) f]
      rfl
    rw [hstep, ih, ih]
    simp only [maxBoolFun]
    congr 1 <;> apply maxBoolFun_congr <;> intro gL <;> apply maxBoolFun_congr <;> intro gR
    · congr 1; exact (appendFun_cons false gL gR).symm
    · congr 1; exact (appendFun_cons true gL gR).symm

theorem consFun_eta {α : Type} {n : Nat} (S : Fin (n + 1) → α) :
    S = consFun (S ⟨0, by omega⟩) (fun i : Fin n => S ⟨i.val + 1, by omega⟩) := by
  funext i
  by_cases h0 : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext h0
    simp only [consFun, h0, ↓reduceDIte]
    rw [hi]
  · simp only [consFun, h0, ↓reduceDIte]
    congr 1; apply Fin.ext; dsimp; omega

theorem maxBoolFun_eq_none_iff {n : Nat} {f : (Fin n → Bool) → Option Nat} :
    maxBoolFun n f = none ↔ ∀ S, f S = none := by
  induction n with
  | zero =>
    simp only [maxBoolFun]
    constructor
    · intro h S
      have : S = (fun i => Fin.elim0 i) := funext (fun i => Fin.elim0 i)
      rw [this]; exact h
    · intro h; exact h _
  | succ n ih =>
    simp only [maxBoolFun]
    constructor
    · intro h S
      have hnone : maxBoolFun n (fun g => f (consFun false g)) = none ∧
                   maxBoolFun n (fun g => f (consFun true g)) = none := by
        cases h1 : maxBoolFun n (fun g => f (consFun false g)) <;>
        cases h2 : maxBoolFun n (fun g => f (consFun true g)) <;>
        simp [optMax, h1, h2] at h
        exact ⟨rfl, rfl⟩
      rw [consFun_eta S]
      cases S ⟨0, by omega⟩
      · exact (ih.mp hnone.1) _
      · exact (ih.mp hnone.2) _
    · intro h
      have h1 : maxBoolFun n (fun g => f (consFun false g)) = none := ih.mpr (fun g => h _)
      have h2 : maxBoolFun n (fun g => f (consFun true g)) = none := ih.mpr (fun g => h _)
      rw [h1, h2]; rfl

/-- Soundness of `maxBoolFun`: `maxBoolFun n f = some d` iff `d` is achieved and upper-bounds all values. -/
theorem maxBoolFun_eq_some_iff {n : Nat} {f : (Fin n → Bool) → Option Nat} {d : Nat} :
    maxBoolFun n f = some d ↔ (∃ S, f S = some d) ∧ (∀ S d', f S = some d' → d' ≤ d) := by
  induction n generalizing d with
  | zero =>
    simp only [maxBoolFun]
    constructor
    · intro h
      refine ⟨⟨fun i => Fin.elim0 i, h⟩, ?_⟩
      intro S d' hS
      have hEq : S = (fun i => Fin.elim0 i) := funext (fun i => Fin.elim0 i)
      rw [hEq, h] at hS
      cases hS; omega
    · rintro ⟨⟨S, hS⟩, _⟩
      have hEq : S = (fun i => Fin.elim0 i) := funext (fun i => Fin.elim0 i)
      rwa [hEq] at hS
  | succ n ih =>
    simp only [maxBoolFun]
    cases hF : maxBoolFun n (fun g => f (consFun false g)) with
    | none =>
      have hFnone := maxBoolFun_eq_none_iff.mp hF
      cases hT : maxBoolFun n (fun g => f (consFun true g)) with
      | none =>
        have hTnone := maxBoolFun_eq_none_iff.mp hT
        simp only [optMax]
        constructor
        · intro h; cases h
        · rintro ⟨⟨S, hS⟩, _⟩
          rw [consFun_eta S] at hS
          cases hS0 : S ⟨0, by omega⟩
          · rw [hS0, hFnone] at hS; cases hS
          · rw [hS0, hTnone] at hS; cases hS
      | some dT =>
        have ⟨⟨gT, hgT⟩, hTmax⟩ := ih.mp hT
        simp only [optMax]
        constructor
        · intro h; cases h
          refine ⟨⟨consFun true gT, hgT⟩, ?_⟩
          intro S d' hS
          rw [consFun_eta S] at hS
          cases hS0 : S ⟨0, by omega⟩
          · rw [hS0, hFnone] at hS; cases hS
          · rw [hS0] at hS; exact hTmax _ _ hS
        · rintro ⟨⟨S, hS⟩, hmax⟩
          have hle1 : dT ≤ d := hmax (consFun true gT) dT hgT
          have hle2 : d ≤ dT := by
            rw [consFun_eta S] at hS
            cases hS0 : S ⟨0, by omega⟩
            · rw [hS0, hFnone] at hS; cases hS
            · rw [hS0] at hS; exact hTmax _ _ hS
          congr 1; omega
    | some dF =>
      have ⟨⟨gF, hgF⟩, hFmax⟩ := ih.mp hF
      cases hT : maxBoolFun n (fun g => f (consFun true g)) with
      | none =>
        have hTnone := maxBoolFun_eq_none_iff.mp hT
        simp only [optMax]
        constructor
        · intro h; cases h
          refine ⟨⟨consFun false gF, hgF⟩, ?_⟩
          intro S d' hS
          rw [consFun_eta S] at hS
          cases hS0 : S ⟨0, by omega⟩
          · rw [hS0] at hS; exact hFmax _ _ hS
          · rw [hS0, hTnone] at hS; cases hS
        · rintro ⟨⟨S, hS⟩, hmax⟩
          have hle1 : dF ≤ d := hmax (consFun false gF) dF hgF
          have hle2 : d ≤ dF := by
            rw [consFun_eta S] at hS
            cases hS0 : S ⟨0, by omega⟩
            · rw [hS0] at hS; exact hFmax _ _ hS
            · rw [hS0, hTnone] at hS; cases hS
          congr 1; omega
      | some dT =>
        have ⟨⟨gT, hgT⟩, hTmax⟩ := ih.mp hT
        simp only [optMax]
        constructor
        · intro h; cases h
          constructor
          · by_cases hle : dF ≤ dT
            · exact ⟨consFun true gT, by rw [Nat.max_eq_right hle]; exact hgT⟩
            · exact ⟨consFun false gF, by rw [Nat.max_eq_left (by omega)]; exact hgF⟩
          · intro S d' hS
            rw [consFun_eta S] at hS
            cases hS0 : S ⟨0, by omega⟩
            · rw [hS0] at hS; have := hFmax _ _ hS; omega
            · rw [hS0] at hS; have := hTmax _ _ hS; omega
        · rintro ⟨⟨S, hS⟩, hmax⟩
          have h1 : dF ≤ d := hmax (consFun false gF) dF hgF
          have h2 : dT ≤ d := hmax (consFun true gT) dT hgT
          have h3 : d ≤ max dF dT := by
            rw [consFun_eta S] at hS
            cases hS0 : S ⟨0, by omega⟩
            · rw [hS0] at hS; have := hFmax _ _ hS; omega
            · rw [hS0] at hS; have := hTmax _ _ hS; omega
          congr 1; omega

theorem sumFin_congr {m : Nat} {a b : Fin m → Nat} (hab : ∀ i, a i = b i) :
    sumFin m a = sumFin m b := by
  induction m with
  | zero => rfl
  | succ m' ihm => simp only [sumFin]; rw [ihm (fun i => hab _), hab _]

theorem sumFin_add {m : Nat} (a b : Fin m → Nat) :
    sumFin m (fun i => a i + b i) = sumFin m a + sumFin m b := by
  induction m with
  | zero => simp [sumFin]
  | succ m' ih => simp only [sumFin, ih]; omega

theorem sumFin_mul_left {m : Nat} (c : Nat) (a : Fin m → Nat) :
    sumFin m (fun i => c * a i) = c * sumFin m a := by
  induction m with
  | zero => simp [sumFin]
  | succ m' ih => simp only [sumFin, ih, Nat.mul_add]

theorem sumFin_mul_right {m : Nat} (a : Fin m → Nat) (c : Nat) :
    sumFin m (fun i => a i * c) = sumFin m a * c := by
  induction m with
  | zero => simp [sumFin]
  | succ m' ih => simp only [sumFin, ih, Nat.add_mul]

theorem sumColorings_congr {q n : Nat} {f g : (Fin n → Fin q) → Nat} (h : ∀ x, f x = g x) :
    sumColorings q n f = sumColorings q n g := by
  induction n with
  | zero => exact h _
  | succ n ih =>
    simp only [sumColorings]
    exact sumFin_congr (fun c => ih (fun x => h _))

theorem sumColorings_add {q n : Nat} (f g : (Fin n → Fin q) → Nat) :
    sumColorings q n (fun x => f x + g x) = sumColorings q n f + sumColorings q n g := by
  induction n with
  | zero => simp [sumColorings]
  | succ n ih =>
    simp only [sumColorings]
    rw [← sumFin_add]
    exact sumFin_congr (fun c => ih _ _)

theorem sumColorings_mul_left {q n : Nat} (c : Nat) (f : (Fin n → Fin q) → Nat) :
    sumColorings q n (fun x => c * f x) = c * sumColorings q n f := by
  induction n with
  | zero => simp [sumColorings]
  | succ n ih =>
    simp only [sumColorings, ← sumFin_mul_left]
    exact sumFin_congr (fun col => ih _)

theorem sumColorings_mul_right {q n : Nat} (f : (Fin n → Fin q) → Nat) (c : Nat) :
    sumColorings q n (fun x => f x * c) = sumColorings q n f * c := by
  induction n with
  | zero => simp [sumColorings]
  | succ n ih =>
    simp only [sumColorings, ← sumFin_mul_right]
    exact sumFin_congr (fun col => ih _)

theorem sumColorings_cast {q k1 k2 : Nat} (heq : k1 = k2) (f : (Fin k1 → Fin q) → Nat) :
    sumColorings q k1 f = sumColorings q k2 (fun g => f (fun i => g ⟨i.val, by omega⟩)) := by
  subst heq; rfl

theorem sumColorings_append (q n m : Nat) (f : (Fin (n + m) → Fin q) → Nat) :
    sumColorings q (n + m) f =
      sumColorings q n (fun gL => sumColorings q m (fun gR => f (appendFun gL gR))) := by
  induction n with
  | zero =>
    rw [sumColorings_cast (Nat.zero_add m) f]
    simp only [sumColorings]
    apply sumColorings_congr
    intro gR
    have hfun : (fun i : Fin (0 + m) => gR ⟨i.val, by omega⟩) = appendFun (fun i => Fin.elim0 i) gR := by
      funext i; simp [appendFun]
    rw [hfun]
  | succ n ih =>
    have hstep :
        sumColorings q (n + 1 + m) f =
        sumFin q (fun c => sumColorings q (n + m) (fun g => f (fun i => consFun c g ⟨i.val, by omega⟩))) := by
      rw [sumColorings_cast (show n + 1 + m = (n + m) + 1 by omega) f]
      rfl
    rw [hstep]
    simp only [sumColorings]
    apply sumFin_congr
    intro c
    rw [ih]
    apply sumColorings_congr; intro gL
    apply sumColorings_congr; intro gR
    congr 1; exact (appendFun_cons c gL gR).symm

theorem sumSubsets_congr {α : Type} {f g : List α → Nat} {xs : List α}
    (h : ∀ s, f s = g s) : sumSubsets f xs = sumSubsets g xs := by
  induction xs generalizing f g with
  | nil => exact h []
  | cons e es ih =>
    simp only [sumSubsets]
    rw [ih h, ih (fun s => h (e :: s))]

theorem sumSubsets_add {α : Type} (f g : List α → Nat) (xs : List α) :
    sumSubsets (fun s => f s + g s) xs = sumSubsets f xs + sumSubsets g xs := by
  induction xs generalizing f g with
  | nil => simp [sumSubsets]
  | cons e es ih =>
    simp only [sumSubsets, ih]
    omega

theorem sumSubsets_mul_left {α : Type} (c : Nat) (f : List α → Nat) (xs : List α) :
    sumSubsets (fun s => c * f s) xs = c * sumSubsets f xs := by
  induction xs generalizing f with
  | nil => simp [sumSubsets]
  | cons e es ih =>
    simp only [sumSubsets, ih, Nat.mul_add]

theorem sumSubsets_mul_right {α : Type} (f : List α → Nat) (c : Nat) (xs : List α) :
    sumSubsets (fun s => f s * c) xs = sumSubsets f xs * c := by
  induction xs generalizing f with
  | nil => simp [sumSubsets]
  | cons e es ih =>
    simp only [sumSubsets, ih, Nat.add_mul]

theorem sumSubsets_append {α : Type} (f : List α → Nat) (xs ys : List α) :
    sumSubsets f (xs ++ ys) = sumSubsets (fun s1 => sumSubsets (fun s2 => f (s1 ++ s2)) ys) xs := by
  induction xs generalizing f with
  | nil => simp [sumSubsets]
  | cons e es ih =>
    simp only [List.cons_append, sumSubsets, ih]

theorem sumSubsets_swap {α : Type} (f : List α → Nat)
    (hinv : ∀ a b s, f (a :: b :: s) = f (b :: a :: s)) (a b : α) (xs : List α) :
    sumSubsets f (a :: b :: xs) = sumSubsets f (b :: a :: xs) := by
  simp only [sumSubsets]
  have h1 : sumSubsets (fun s => f (a :: b :: s)) xs = sumSubsets (fun s => f (b :: a :: s)) xs :=
    sumSubsets_congr (fun s => hinv a b s)
  omega

/-- Permutation invariance of `sumSubsets` whenever `f` is order-invariant (`List.Perm`). -/
theorem sumSubsets_perm {α : Type} {f : List α → Nat}
    (hperm_f : ∀ s1 s2, s1.Perm s2 → f s1 = f s2)
    {xs ys : List α} (hxy : xs.Perm ys) :
    sumSubsets f xs = sumSubsets f ys := by
  induction hxy generalizing f with
  | nil => rfl
  | cons e _ ih =>
    simp only [sumSubsets]
    rw [ih hperm_f, ih (fun s1 s2 hs => hperm_f _ _ (List.Perm.cons e hs))]
  | swap a b l =>
    exact sumSubsets_swap f (fun x y s => hperm_f _ _ (List.Perm.swap y x s)) b a l
  | trans _ _ ih1 ih2 =>
    rw [ih1 hperm_f, ih2 hperm_f]

/-- Two `Nodup` lists with identical membership are permutations of each other. -/
theorem perm_of_nodup_iff {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → ys.Nodup → (∀ a, a ∈ xs ↔ a ∈ ys) → xs.Perm ys
  | [], [], _, _, _ => List.Perm.nil
  | [], y :: _, _, _, h => absurd ((h y).mpr (by simp)) (by simp)
  | x :: xs, ys, hxs, hys, h => by
    have hx_nd : x ∉ xs ∧ xs.Nodup := List.nodup_cons.mp hxs
    have hx_mem : x ∈ ys := (h x).mp (by simp)
    -- Split `ys` at `x`: `ys ~ x :: ys.erase x`
    have hperm_ys : ys.Perm (x :: ys.erase x) := List.perm_cons_erase hx_mem
    have hys_erase_nd : (ys.erase x).Nodup :=
      (List.nodup_cons.mp (hperm_ys.nodup_iff.mp hys)).2
    have hiff' : ∀ a, a ∈ xs ↔ a ∈ ys.erase x := by
      intro a
      constructor
      · intro ha
        have hax : a ≠ x := fun heq => hx_nd.1 (heq ▸ ha)
        have hay : a ∈ ys := (h a).mp (by simp [ha])
        have hay' : a ∈ x :: ys.erase x := hperm_ys.subset hay
        rcases List.mem_cons.mp hay' with rfl | hrest
        · exact absurd rfl hax
        · exact hrest
      · intro ha
        have hax : a ≠ x := by
          intro heq
          have hx_not_in : x ∉ ys.erase x := (List.nodup_cons.mp (hperm_ys.nodup_iff.mp hys)).1
          exact hx_not_in (heq ▸ ha)
        have hay : a ∈ ys := hperm_ys.symm.subset (by simp [ha])
        rcases List.mem_cons.mp ((h a).mpr hay) with rfl | hrest
        · exact absurd rfl hax
        · exact hrest
    exact List.Perm.trans (List.Perm.cons x (perm_of_nodup_iff hx_nd.2 hys_erase_nd hiff')) hperm_ys.symm


-- ============================================================================
-- SECTION 3: Reusable Generic Engine `BitTransfer3`
--   (3-Terminal Bit-Sliced Graphs + Generic PM / Alpha / Chromatic Soundness)
-- ============================================================================

theorem fin8Bit_bitsToFin8 (b0 b1 b2 : Bool) :
    fin8Bit (bitsToFin8 b0 b1 b2) 0 = b0 ∧
    fin8Bit (bitsToFin8 b0 b1 b2) 1 = b1 ∧
    fin8Bit (bitsToFin8 b0 b1 b2) 2 = b2 := by
  cases b0 <;> cases b1 <;> cases b2 <;> decide

theorem fin8Bit_bitsToFin8_at (b0 b1 b2 : Bool) (i : Fin 3) :
    fin8Bit (bitsToFin8 b0 b1 b2) i =
      match i with | ⟨0, _⟩ => b0 | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2 := by
  match i with
  | ⟨0, _⟩ => exact (fin8Bit_bitsToFin8 b0 b1 b2).1
  | ⟨1, _⟩ => exact (fin8Bit_bitsToFin8 b0 b1 b2).2.1
  | ⟨2, _⟩ => exact (fin8Bit_bitsToFin8 b0 b1 b2).2.2

theorem bitsToFin8_fin8Bit (s : Fin 8) :
    bitsToFin8 (fin8Bit s 0) (fin8Bit s 1) (fin8Bit s 2) = s := by
  revert s; decide

-- ----------------------------------------------------------------------------
-- 3A. Generic Independence Number & Tropical Transfer Soundness (`BitTransfer3.Alpha`)
-- ----------------------------------------------------------------------------

theorem cardBool_append (n m : Nat) (SL : Fin n → Bool) (SR : Fin m → Bool) :
    cardBool (n + m) (appendFun SL SR) = cardBool n SL + cardBool m SR := by
  induction m with
  | zero =>
    simp only [cardBool, sumFin, Nat.add_zero]
    exact sumFin_congr (fun i => by simp [appendFun, i.isLt])
  | succ m ih =>
    have hsplit : cardBool (n + (m + 1)) (appendFun SL SR) =
        cardBool (n + m) (appendFun SL (fun j : Fin m => SR j.castSucc)) +
        (if SR (Fin.last m) then 1 else 0) := by
      have hcast : n + (m + 1) = (n + m) + 1 := by omega
      change sumFin ((n + m) + 1) (fun i => if appendFun SL SR i then 1 else 0) = _
      simp only [sumFin, cardBool]
      have h1 : sumFin (n + m) (fun i => if appendFun SL SR i.castSucc then 1 else 0) =
                sumFin (n + m) (fun i => if appendFun SL (fun j : Fin m => SR j.castSucc) i then 1 else 0) := by
        apply sumFin_congr; intro i
        by_cases hi : i.val < n
        · simp [appendFun, hi, Fin.castSucc]
        · simp [appendFun, hi, Fin.castSucc]
      have h2 : appendFun SL SR (Fin.last (n + m)) = SR (Fin.last m) := by
        have hnot : ¬ (n + m < n) := by omega
        have hsub : n + m - n = m := by omega
        simp [appendFun, Fin.last, hnot, hsub]
      rw [h1, h2]
    rw [hsplit, ih (fun j : Fin m => SR j.castSucc)]
    simp only [cardBool, sumFin]
    omega

theorem fin8Bit_termMask {n : Nat} (G : TermGraph n) (S : Fin n → Bool) (i : Fin 3) :
    fin8Bit (termMask G S) i = S (G.t i) := by
  unfold termMask
  rw [fin8Bit_bitsToFin8_at]
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

theorem maxFin8_congr {f g : Fin 8 → Option Nat} (h : ∀ s, f s = g s) :
    maxFin8 f = maxFin8 g := by
  simp only [maxFin8, h]

theorem maxFin8_single (m : Fin 8) (f : Fin 8 → Option Nat) :
    maxFin8 (fun s => if m == s then f s else none) = f m := by
  match m with
  | ⟨0, _⟩ => simp [maxFin8, optMax_none_right]
  | ⟨1, _⟩ => simp [maxFin8, optMax_none_left, optMax_none_right]
  | ⟨2, _⟩ => simp [maxFin8, optMax_none_left, optMax_none_right]
  | ⟨3, _⟩ => simp [maxFin8, optMax_none_left, optMax_none_right]
  | ⟨4, _⟩ => simp [maxFin8, optMax_none_left, optMax_none_right]
  | ⟨5, _⟩ => simp [maxFin8, optMax_none_left, optMax_none_right]
  | ⟨6, _⟩ => simp [maxFin8, optMax_none_left, optMax_none_right]
  | ⟨7, _⟩ => simp [maxFin8, optMax_none_left]

theorem maxFin8_maxBoolFun {n : Nat} (f : Fin 8 → (Fin n → Bool) → Option Nat) :
    maxFin8 (fun s => maxBoolFun n (f s)) = maxBoolFun n (fun x => maxFin8 (fun s => f s x)) := by
  simp only [maxFin8, ← maxBoolFun_optMax]

theorem exactAlpha_eq_maxFin8 {n : Nat} (G : TermGraph n) :
    exactAlpha G.graph = maxFin8 (alphaVec G) := by
  unfold exactAlpha alphaVec
  rw [maxFin8_maxBoolFun]
  apply maxBoolFun_congr
  intro S
  cases hI : isIndep G.graph S
  · simp [maxFin8, optMax]
  · simp only [Bool.true_and]
    exact (maxFin8_single (termMask G S) (fun _ => some (cardBool n S))).symm

theorem isIndep_glue_iff {n : Nat} (spec : GlueSpec) (L R : TermGraph n)
    (SL SR : Fin n → Bool) :
    isIndep (glue spec L R).graph (appendFun SL SR) =
      (isIndep L.graph SL && isIndep R.graph SR && bridgeIndepOk spec (termMask L SL) (termMask R SR)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [isIndep, bridgeIndepOk, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro u v hu hv
      have h' := h (leftEmbed u) (leftEmbed v)
        (by simpa [appendFun, leftEmbed, u.isLt] using hu)
        (by simpa [appendFun, leftEmbed, v.isLt] using hv)
      simpa [glue, glueAdj, leftEmbed, u.isLt, v.isLt] using h'
    · intro u v hu hv
      have h' := h (rightEmbed u) (rightEmbed v)
        (by rw [rightEmbed, appendFun_right]; exact hu)
        (by rw [rightEmbed, appendFun_right]; exact hv)
      have hnotu : ¬ (n + u.val < n) := by omega
      have hnotv : ¬ (n + v.val < n) := by omega
      have hsu : n + u.val - n = u.val := by omega
      have hsv : n + v.val - n = v.val := by omega
      simpa [glue, glueAdj, rightEmbed, hnotu, hnotv, hsu, hsv] using h'
    · intro i j hbr
      rw [fin8Bit_termMask, fin8Bit_termMask]
      cases hSL : SL (L.t i) <;> cases hSR : SR (R.t j) <;> simp
      have h' := h (leftEmbed (L.t i)) (rightEmbed (R.t j))
        (by rw [leftEmbed, appendFun_left]; exact hSL)
        (by rw [rightEmbed, appendFun_right]; exact hSR)
      have hnot : ¬ (n + (R.t j).val < n) := by omega
      have hsub : n + (R.t j).val - n = (R.t j).val := by omega
      have htrue : glueAdj spec L R (leftEmbed (L.t i)) (rightEmbed (R.t j)) = true := by
        simp only [glueAdj, leftEmbed, rightEmbed, (L.t i).isLt, ↓reduceDIte, hnot, hasBridge]
        exact decide_eq_true ⟨i, j, Fin.ext rfl, Fin.ext hsub, hbr⟩
      rw [show (glue spec L R).graph.adj _ _ = true from htrue] at h'
      cases h'
  · rintro ⟨⟨hL, hR⟩, hB⟩ u v hu hv
    unfold glue; dsimp only; unfold glueAdj
    by_cases hru : u.val < n <;> by_cases hrv : v.val < n
    · simp only [hru, hrv, ↓reduceDIte]
      exact hL ⟨u.val, hru⟩ ⟨v.val, hrv⟩ (by simpa [appendFun, hru] using hu) (by simpa [appendFun, hrv] using hv)
    · simp only [hru, hrv, ↓reduceDIte, hasBridge, decide_eq_false_iff_not]
      rintro ⟨i, j, hui, hvj, hbr⟩
      have hSL : SL (L.t i) = true := by rw [← hui]; simpa [appendFun, hru] using hu
      have hSR : SR (R.t j) = true := by rw [← hvj]; simpa [appendFun, hrv] using hv
      have hb' := hB i j hbr
      rw [fin8Bit_termMask, fin8Bit_termMask, hSL, hSR] at hb'
      cases hb'
    · simp only [hru, hrv, ↓reduceDIte, hasBridge, decide_eq_false_iff_not]
      rintro ⟨i, j, hvi, huj, hbr⟩
      have hSL : SL (L.t i) = true := by rw [← hvi]; simpa [appendFun, hrv] using hv
      have hSR : SR (R.t j) = true := by rw [← huj]; simpa [appendFun, hru] using hu
      have hb' := hB i j hbr
      rw [fin8Bit_termMask, fin8Bit_termMask, hSL, hSR] at hb'
      cases hb'
    · simp only [hru, hrv, ↓reduceDIte]
      exact hR ⟨u.val - n, by omega⟩ ⟨v.val - n, by omega⟩ (by simpa [appendFun, hru] using hu) (by simpa [appendFun, hrv] using hv)

theorem termMask_glue {n : Nat} (spec : GlueSpec) (L R : TermGraph n)
    (SL SR : Fin n → Bool) :
    termMask (glue spec L R) (appendFun SL SR) = outMask spec (termMask L SL) (termMask R SR) := by
  have hbit : ∀ (p : Bool × Fin 3),
      appendFun SL SR (glueTerm L R p) =
      (if p.1 then fin8Bit (termMask R SR) p.2 else fin8Bit (termMask L SL) p.2) := by
    rintro ⟨b, idx⟩
    cases b
    · simp only [glueTerm, Bool.false_eq_true, ↓reduceIte, leftEmbed, appendFun_left, fin8Bit_termMask]
    · simp only [glueTerm, ↓reduceIte, rightEmbed, appendFun_right, fin8Bit_termMask]
  simp only [termMask, outMask, glue, hbit]

/-- **GENERIC SOUNDNESS THEOREM 1 (`BitTransfer3.Alpha`)**:
    For ANY 3-terminal gluing specification `spec` and ANY two `TermGraph n` instances `L, R`,
    the exact tropical independence-number vector of `glue spec L R` equals `stepAlpha spec`. -/
theorem glue_alpha_sound {n : Nat} (spec : GlueSpec) (L R : TermGraph n) (s : Fin 8) :
    alphaVec (glue spec L R) s = stepAlpha spec (alphaVec L) (alphaVec R) s := by
  unfold alphaVec stepAlpha maxPairsFin8
  rw [maxBoolFun_append]
  have hinner : ∀ (sL sR : Fin 8),
      (if bridgeIndepOk spec sL sR && (outMask spec sL sR == s) then
        optAdd (maxBoolFun n (fun SL => if isIndep L.graph SL && (termMask L SL == sL) then some (cardBool n SL) else none))
               (maxBoolFun n (fun SR => if isIndep R.graph SR && (termMask R SR == sR) then some (cardBool n SR) else none))
       else none) =
      maxBoolFun n (fun SL => maxBoolFun n (fun SR =>
        if termMask L SL == sL then
          if termMask R SR == sR then
            if isIndep L.graph SL && isIndep R.graph SR && bridgeIndepOk spec sL sR && (outMask spec sL sR == s)
            then some (cardBool n SL + cardBool n SR) else none
          else none
        else none)) := by
    intro sL sR
    by_cases hcond : (bridgeIndepOk spec sL sR && (outMask spec sL sR == s)) = true
    · simp only [hcond, ↓reduceIte]
      rw [← maxBoolFun_optAdd_right]
      apply maxBoolFun_congr; intro SL
      rw [← maxBoolFun_optAdd_left]
      apply maxBoolFun_congr; intro SR
      have hB : bridgeIndepOk spec sL sR = true := (Bool.and_eq_true _ _).mp hcond |>.1
      have hO : (outMask spec sL sR == s) = true := (Bool.and_eq_true _ _).mp hcond |>.2
      cases isIndep L.graph SL <;> cases (termMask L SL == sL) <;>
      cases isIndep R.graph SR <;> cases (termMask R SR == sR) <;>
      simp [optAdd, hB, hO]
    · have hfalse : (bridgeIndepOk spec sL sR && (outMask spec sL sR == s)) = false :=
        Bool.eq_false_iff.mpr hcond
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
      symm
      rw [maxBoolFun_eq_none_iff]; intro SL
      rw [maxBoolFun_eq_none_iff]; intro SR
      have hBO : (bridgeIndepOk spec sL sR && (outMask spec sL sR == s)) = false := hfalse
      cases isIndep L.graph SL <;> cases (termMask L SL == sL) <;>
      cases isIndep R.graph SR <;> cases (termMask R SR == sR) <;>
      simp [hBO]
  have hmid :
      (maxFin8 fun sL => maxFin8 fun sR =>
        maxBoolFun n fun SL => maxBoolFun n fun SR =>
          if termMask L SL == sL then
            if termMask R SR == sR then
              if isIndep L.graph SL && isIndep R.graph SR && bridgeIndepOk spec sL sR && (outMask spec sL sR == s)
              then some (cardBool n SL + cardBool n SR) else none
            else none
          else none) =
      (maxBoolFun n fun SL => maxBoolFun n fun SR =>
        if isIndep (glue spec L R).graph (appendFun SL SR) && (termMask (glue spec L R) (appendFun SL SR) == s)
        then some (cardBool (n + n) (appendFun SL SR)) else none) := by
    simp only [maxFin8_maxBoolFun]
    apply maxBoolFun_congr; intro SL
    apply maxBoolFun_congr; intro SR
    rw [isIndep_glue_iff, termMask_glue, cardBool_append]
    rw [maxFin8_congr (fun sL => by
      show (maxFin8 fun sR =>
              if (termMask L SL == sL) = true then
                if (termMask R SR == sR) = true then
                  if (isIndep L.graph SL && isIndep R.graph SR && bridgeIndepOk spec sL sR && outMask spec sL sR == s) = true
                  then some (cardBool n SL + cardBool n SR) else none
                else none
              else none) =
           (if (termMask L SL == sL) = true then
              if (isIndep L.graph SL && isIndep R.graph SR && bridgeIndepOk spec sL (termMask R SR) && outMask spec sL (termMask R SR) == s) = true
              then some (cardBool n SL + cardBool n SR) else none
            else none)
      by_cases hL : (termMask L SL == sL) = true
      · simp only [hL, ↓reduceIte]; exact maxFin8_single (termMask R SR) _
      · have hLf : (termMask L SL == sL) = false := Bool.eq_false_iff.mpr hL
        simp only [hLf, Bool.false_eq_true, ↓reduceIte]; rfl)]
    exact maxFin8_single (termMask L SL) _
  rw [← hmid]
  exact maxFin8_congr (fun sL => maxFin8_congr (fun sR => (hinner sL sR).symm))

-- ----------------------------------------------------------------------------
-- 3B. Generic Perfect-Matching Transfer Soundness (`BitTransfer3.PM`)
-- ----------------------------------------------------------------------------

theorem mem_pairsWith {n : Nat} {u : Fin n} {e : Edge n} :
    e ∈ pairsWith n u ↔ e.1 = u ∧ u.val < e.2.val := by
  simp only [pairsWith, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨v, hv⟩
    by_cases hlt : u.val < v.val
    · simp only [hlt, ↓reduceIte, Option.some.injEq] at hv
      rw [← hv]; exact ⟨rfl, hlt⟩
    · simp only [hlt, ↓reduceIte] at hv; cases hv
  · rintro ⟨rfl, hlt⟩
    exact ⟨e.2, by simp [hlt]⟩

theorem mem_allPairs {n : Nat} {e : Edge n} :
    e ∈ allPairs n ↔ e.1.val < e.2.val := by
  simp only [allPairs, List.mem_flatMap, List.mem_finRange, true_and, mem_pairsWith]
  constructor
  · rintro ⟨u, rfl, hlt⟩; exact hlt
  · intro hlt; exact ⟨e.1, rfl, hlt⟩

theorem mem_allEdges {n : Nat} {G : FinGraph n} {e : Edge n} :
    e ∈ allEdges G ↔ e.1.val < e.2.val ∧ G.adj e.1 e.2 = true := by
  simp [allEdges, mem_allPairs]

theorem nodup_map_inj {α β : Type} {f : α → β} (hinj : ∀ a1 a2, f a1 = f a2 → a1 = a2) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hnd => by
    have ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_inj hinj hxs⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
    exact hx ((hinj y x hfy) ▸ hy)

theorem nodup_filterMap_inj {α β : Type} {f : α → Option β}
    (hinj : ∀ a1 a2 b, f a1 = some b → f a2 = some b → a1 = a2) :
    ∀ {xs : List α}, xs.Nodup → (xs.filterMap f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hnd => by
    have ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
    cases hfx : f x with
    | none => simpa [List.filterMap, hfx] using nodup_filterMap_inj hinj hxs
    | some b =>
      simp only [List.filterMap, hfx, List.nodup_cons]
      refine ⟨?_, nodup_filterMap_inj hinj hxs⟩
      intro hb
      rcases List.mem_filterMap.mp hb with ⟨y, hy, hfy⟩
      have hxy := hinj x y b hfx hfy
      exact hx (hxy ▸ hy)

theorem nodup_flatMap {α β : Type} {f : α → List β}
    (hnd_f : ∀ a, (f a).Nodup)
    (hdisj : ∀ a1 a2 b, b ∈ f a1 → b ∈ f a2 → a1 = a2) :
    ∀ {xs : List α}, xs.Nodup → (xs.flatMap f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hnd => by
    have ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, List.nodup_append]
    refine ⟨hnd_f x, nodup_flatMap hnd_f hdisj hxs, ?_⟩
    intro b hb1 b' hb2 heq
    subst heq
    rcases List.mem_flatMap.mp hb2 with ⟨y, hy, hby⟩
    have hxy := hdisj x y b hb1 hby
    exact hx (hxy ▸ hy)

theorem allPairs_nodup (n : Nat) : (allPairs n).Nodup := by
  apply nodup_flatMap
  · intro u
    apply nodup_filterMap_inj
    · intro v1 v2 e h1 h2
      by_cases lt1 : u.val < v1.val <;> by_cases lt2 : u.val < v2.val <;>
        simp [lt1, lt2] at h1 h2
      rw [← h1] at h2
      exact (congrArg Prod.snd h2).symm
    · exact List.nodup_finRange n
  · intro u1 u2 e h1 h2
    have h1' := (mem_pairsWith.mp h1).1
    have h2' := (mem_pairsWith.mp h2).1
    rw [← h1', h2']
  · exact List.nodup_finRange n

theorem allEdges_nodup {n : Nat} (G : FinGraph n) : (allEdges G).Nodup :=
  (allPairs_nodup n).filter _

theorem bridgePairs_nodup (spec : GlueSpec) : (bridgePairs spec).Nodup := by
  apply List.Pairwise.filter
  apply nodup_flatMap
  · intro i
    exact nodup_map_inj (fun j1 j2 h => congrArg Prod.snd h) (List.nodup_finRange 3)
  · intro i1 i2 p h1 h2
    rcases List.mem_map.mp h1 with ⟨_, _, rfl⟩
    rcases List.mem_map.mp h2 with ⟨_, _, h⟩
    exact (congrArg Prod.fst h).symm
  · exact List.nodup_finRange 3

theorem mem_bridgePairs (spec : GlueSpec) (p : Fin 3 × Fin 3) :
    p ∈ bridgePairs spec ↔ spec.bridges p.1 p.2 = true := by
  rcases p with ⟨i, j⟩
  simp [bridgePairs]

theorem allEdges_glue_perm {n : Nat} (spec : GlueSpec) (L R : TermGraph n) :
    (allEdges (glue spec L R).graph).Perm
      ((allEdges L.graph).map mapLeftEdge ++
       (allEdges R.graph).map mapRightEdge ++
       (bridgePairs spec).map (mapBridgeEdge L R)) := by
  apply perm_of_nodup_iff (allEdges_nodup _)
  · have hLnd : ((allEdges L.graph).map mapLeftEdge).Nodup :=
      nodup_map_inj (fun e1 e2 h => by
        rcases e1 with ⟨u1, v1⟩; rcases e2 with ⟨u2, v2⟩
        simp [mapLeftEdge] at h
        exact Prod.ext (leftEmbed_inj h.1) (leftEmbed_inj h.2)) (allEdges_nodup L.graph)
    have hRnd : ((allEdges R.graph).map mapRightEdge).Nodup :=
      nodup_map_inj (fun e1 e2 h => by
        rcases e1 with ⟨u1, v1⟩; rcases e2 with ⟨u2, v2⟩
        simp [mapRightEdge] at h
        exact Prod.ext (rightEmbed_inj h.1) (rightEmbed_inj h.2)) (allEdges_nodup R.graph)
    have hBnd : ((bridgePairs spec).map (mapBridgeEdge L R)).Nodup :=
      nodup_map_inj (fun p1 p2 h => by
        rcases p1 with ⟨i1, j1⟩; rcases p2 with ⟨i2, j2⟩
        simp [mapBridgeEdge] at h
        exact Prod.ext (L.distinct _ _ (leftEmbed_inj h.1)) (R.distinct _ _ (rightEmbed_inj h.2))) (bridgePairs_nodup spec)
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hLnd, hRnd, ?_⟩, hBnd, ?_⟩
    · intro e1 h1 e2 h2 heq; subst heq
      rcases List.mem_map.mp h1 with ⟨_, _, rfl⟩
      rcases List.mem_map.mp h2 with ⟨_, _, h⟩
      exact leftEmbed_ne_rightEmbed _ _ (congrArg Prod.fst h).symm
    · intro e1 h1 e2 h2 heq; subst heq
      rcases List.mem_map.mp h2 with ⟨_, _, rfl⟩
      rcases List.mem_append.mp h1 with hL | hR
      · rcases List.mem_map.mp hL with ⟨_, _, h⟩
        exact leftEmbed_ne_rightEmbed _ _ (congrArg Prod.snd h)
      · rcases List.mem_map.mp hR with ⟨_, _, h⟩
        exact leftEmbed_ne_rightEmbed _ _ (congrArg Prod.fst h).symm
  · intro e
    rcases e with ⟨u, v⟩
    simp only [mem_allEdges, List.mem_append, List.mem_map, mem_bridgePairs]
    constructor
    · rintro ⟨hlt, hadj⟩
      unfold glue at hadj; dsimp only at hadj; unfold glueAdj at hadj
      by_cases hu : u.val < n <;> by_cases hv : v.val < n
      · simp only [hu, hv, ↓reduceDIte] at hadj
        left; left
        refine ⟨(⟨u.val, hu⟩, ⟨v.val, hv⟩), ⟨hlt, hadj⟩, ?_⟩
        exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
      · simp only [hu, hv, ↓reduceDIte, hasBridge, decide_eq_true_eq] at hadj
        rcases hadj with ⟨i, j, hui, hvj, hbr⟩
        right
        refine ⟨(i, j), hbr, ?_⟩
        refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
        · simpa [mapBridgeEdge, leftEmbed] using (congrArg Fin.val hui).symm
        · have hvv := congrArg Fin.val hvj
          dsimp only at hvv
          simp only [mapBridgeEdge, rightEmbed]
          omega
      · omega
      · simp only [hu, hv, ↓reduceDIte] at hadj
        left; right
        refine ⟨(⟨u.val - n, by omega⟩, ⟨v.val - n, by omega⟩), ⟨by dsimp; omega, hadj⟩, ?_⟩
        refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> (simp only [mapRightEdge, rightEmbed]; omega)
    · rintro ((⟨⟨u1, v1⟩, ⟨hlt, hadj⟩, heq⟩ | ⟨⟨u1, v1⟩, ⟨hlt, hadj⟩, heq⟩) | ⟨⟨i, j⟩, hbr, heq⟩)
      · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        refine ⟨hlt, ?_⟩
        simp [glue, glueAdj, leftEmbed, u1.isLt, v1.isLt, hadj]
      · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        have hnu : ¬ (n + u1.val < n) := by omega
        have hnv : ¬ (n + v1.val < n) := by omega
        have hsu : n + u1.val - n = u1.val := by omega
        have hsv : n + v1.val - n = v1.val := by omega
        refine ⟨by simp [rightEmbed]; omega, ?_⟩
        simp [glue, glueAdj, rightEmbed, hnu, hnv, hsu, hsv, hadj]
      · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        have hnv : ¬ (n + (R.t j).val < n) := by omega
        have hsv : n + (R.t j).val - n = (R.t j).val := by omega
        refine ⟨by simp [leftEmbed, rightEmbed]; omega, ?_⟩
        simp only [glue, glueAdj, leftEmbed, rightEmbed, (L.t i).isLt, ↓reduceDIte, hnv, hasBridge]
        exact decide_eq_true ⟨i, j, Fin.ext rfl, Fin.ext hsv, hbr⟩

theorem degIn_append {n : Nat} (v : Fin n) (xs ys : List (Edge n)) :
    degIn v (xs ++ ys) = degIn v xs + degIn v ys := by
  induction xs with
  | nil => simp [degIn]
  | cons e es ih => rcases e with ⟨a, b⟩; simp [degIn, ih]; omega

theorem degIn_perm {n : Nat} (v : Fin n) {xs ys : List (Edge n)} (h : xs.Perm ys) :
    degIn v xs = degIn v ys := by
  induction h with
  | nil => rfl
  | cons e _ ih => rcases e with ⟨a, b⟩; simp [degIn, ih]
  | swap e1 e2 _ => rcases e1 with ⟨a1, b1⟩; rcases e2 with ⟨a2, b2⟩; simp [degIn]; omega
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem degIn_mapLeft_left {n : Nat} (u : Fin n) (M : List (Edge n)) :
    degIn (leftEmbed u) (M.map mapLeftEdge) = degIn u M := by
  induction M with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    have ha : (leftEmbed a == leftEmbed u) = (a == u) := by
      apply Bool.eq_iff_iff.mpr; simp [leftEmbed, Fin.ext_iff]
    have hb : (leftEmbed b == leftEmbed u) = (b == u) := by
      apply Bool.eq_iff_iff.mpr; simp [leftEmbed, Fin.ext_iff]
    simp [mapLeftEdge, degIn, ha, hb, ih]

theorem degIn_mapLeft_right {n : Nat} (u : Fin n) (M : List (Edge n)) :
    degIn (rightEmbed u) (M.map mapLeftEdge) = 0 := by
  induction M with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    have ha : (leftEmbed a == rightEmbed u) = false := beq_false_of_ne (leftEmbed_ne_rightEmbed a u)
    have hb : (leftEmbed b == rightEmbed u) = false := beq_false_of_ne (leftEmbed_ne_rightEmbed b u)
    simp [mapLeftEdge, degIn, ha, hb, ih]

theorem degIn_mapRight_left {n : Nat} (u : Fin n) (M : List (Edge n)) :
    degIn (leftEmbed u) (M.map mapRightEdge) = 0 := by
  induction M with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    have ha : (rightEmbed a == leftEmbed u) = false := beq_false_of_ne (leftEmbed_ne_rightEmbed u a).symm
    have hb : (rightEmbed b == leftEmbed u) = false := beq_false_of_ne (leftEmbed_ne_rightEmbed u b).symm
    simp [mapRightEdge, degIn, ha, hb, ih]

theorem degIn_mapRight_right {n : Nat} (u : Fin n) (M : List (Edge n)) :
    degIn (rightEmbed u) (M.map mapRightEdge) = degIn u M := by
  induction M with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    have ha : (rightEmbed a == rightEmbed u) = (a == u) := by
      apply Bool.eq_iff_iff.mpr; simp [rightEmbed, Fin.ext_iff]
    have hb : (rightEmbed b == rightEmbed u) = (b == u) := by
      apply Bool.eq_iff_iff.mpr; simp [rightEmbed, Fin.ext_iff]
    simp [mapRightEdge, degIn, ha, hb, ih]

theorem degIn_mapBridge_left {n : Nat} (L R : TermGraph n) (u : Fin n) (B : List (Fin 3 × Fin 3)) :
    degIn (leftEmbed u) (B.map (mapBridgeEdge L R)) =
      if u == L.t 0 then degBridgeL 0 B
      else if u == L.t 1 then degBridgeL 1 B
      else if u == L.t 2 then degBridgeL 2 B
      else 0 := by
  induction B with
  | nil => simp [degIn, degBridgeL]
  | cons p bs ih =>
    rcases p with ⟨i, j⟩
    have hR : (rightEmbed (R.t j) == leftEmbed u) = false :=
      beq_false_of_ne (leftEmbed_ne_rightEmbed u (R.t j)).symm
    have hL : (leftEmbed (L.t i) == leftEmbed u) = (L.t i == u) := by
      apply Bool.eq_iff_iff.mpr; simp [leftEmbed, Fin.ext_iff]
    simp only [List.map_cons, mapBridgeEdge, degIn, hR, hL, Bool.false_eq_true, ↓reduceIte,
               Nat.add_zero, ih]
    by_cases h0 : u = L.t 0
    · subst h0
      have hi : (L.t i == L.t 0) = (i == 0) := by
        apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
        exact ⟨fun h => L.distinct i 0 h, fun h => by rw [h]⟩
      simp [degBridgeL, hi]
    · by_cases h1 : u = L.t 1
      · subst h1
        have hi : (L.t i == L.t 1) = (i == 1) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
          exact ⟨fun h => L.distinct i 1 h, fun h => by rw [h]⟩
        simp [degBridgeL, h0, hi]
      · by_cases h2 : u = L.t 2
        · subst h2
          have hi : (L.t i == L.t 2) = (i == 2) := by
            apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
            exact ⟨fun h => L.distinct i 2 h, fun h => by rw [h]⟩
          simp [degBridgeL, h0, h1, hi]
        · have hni : (L.t i == u) = false := by
            apply beq_false_of_ne
            match i with
            | ⟨0, _⟩ => exact Ne.symm h0
            | ⟨1, _⟩ => exact Ne.symm h1
            | ⟨2, _⟩ => exact Ne.symm h2
          simp [h0, h1, h2, hni]

theorem degIn_mapBridge_right {n : Nat} (L R : TermGraph n) (u : Fin n) (B : List (Fin 3 × Fin 3)) :
    degIn (rightEmbed u) (B.map (mapBridgeEdge L R)) =
      if u == R.t 0 then degBridgeR 0 B
      else if u == R.t 1 then degBridgeR 1 B
      else if u == R.t 2 then degBridgeR 2 B
      else 0 := by
  induction B with
  | nil => simp [degIn, degBridgeR]
  | cons p bs ih =>
    rcases p with ⟨i, j⟩
    have hL : (leftEmbed (L.t i) == rightEmbed u) = false :=
      beq_false_of_ne (leftEmbed_ne_rightEmbed (L.t i) u)
    have hR : (rightEmbed (R.t j) == rightEmbed u) = (R.t j == u) := by
      apply Bool.eq_iff_iff.mpr; simp [rightEmbed, Fin.ext_iff]
    simp only [List.map_cons, mapBridgeEdge, degIn, hL, hR, Bool.false_eq_true, ↓reduceIte,
               Nat.zero_add, ih]
    by_cases h0 : u = R.t 0
    · subst h0
      have hj : (R.t j == R.t 0) = (j == 0) := by
        apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
        exact ⟨fun h => R.distinct j 0 h, fun h => by rw [h]⟩
      simp [degBridgeR, hj]
    · by_cases h1 : u = R.t 1
      · subst h1
        have hj : (R.t j == R.t 1) = (j == 1) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
          exact ⟨fun h => R.distinct j 1 h, fun h => by rw [h]⟩
        simp [degBridgeR, h0, hj]
      · by_cases h2 : u = R.t 2
        · subst h2
          have hj : (R.t j == R.t 2) = (j == 2) := by
            apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
            exact ⟨fun h => R.distinct j 2 h, fun h => by rw [h]⟩
          simp [degBridgeR, h0, h1, hj]
        · have hnj : (R.t j == u) = false := by
            apply beq_false_of_ne
            match j with
            | ⟨0, _⟩ => exact Ne.symm h0
            | ⟨1, _⟩ => exact Ne.symm h1
            | ⟨2, _⟩ => exact Ne.symm h2
          simp [h0, h1, h2, hnj]

theorem targetDeg_term {n : Nat} (G : TermGraph n) (s : Fin 8) (i : Fin 3) :
    targetDeg G s (G.t i) = if fin8Bit s i then 1 else 0 := by
  have h01 : (G.t 1 == G.t 0) = false := beq_false_of_ne (fun h => by have := G.distinct 1 0 h; cases this)
  have h02 : (G.t 2 == G.t 0) = false := beq_false_of_ne (fun h => by have := G.distinct 2 0 h; cases this)
  have h12 : (G.t 2 == G.t 1) = false := beq_false_of_ne (fun h => by have := G.distinct 2 1 h; cases this)
  match i with
  | ⟨0, _⟩ => simp [targetDeg]
  | ⟨1, _⟩ => simp [targetDeg, h01]
  | ⟨2, _⟩ => simp [targetDeg, h02, h12]

theorem exactPM_eq_pmVec7 {n : Nat} (G : TermGraph n) :
    exactPM G.graph = pmVec G 7 := by
  unfold exactPM pmVec
  apply sumSubsets_congr; intro M
  have h : isPerfectMatching M = isInternalPM G 7 M := by
    apply Bool.eq_iff_iff.mpr
    simp only [isPerfectMatching, isInternalPM, decide_eq_true_eq]
    have ht : ∀ v : Fin n, targetDeg G 7 v = 1 := by
      intro v; unfold targetDeg
      have hb0 : fin8Bit 7 0 = true := rfl
      have hb1 : fin8Bit 7 1 = true := rfl
      have hb2 : fin8Bit 7 2 = true := rfl
      simp [hb0, hb1, hb2]
    simp [ht]
  rw [h]

theorem sumFin8_congr {f g : Fin 8 → Nat} (h : ∀ s, f s = g s) :
    sumFin8 f = sumFin8 g := by
  simp only [sumFin8, h]

theorem sumFin8_single (m : Fin 8) (f : Fin 8 → Nat) :
    sumFin8 (fun s => if m == s then f s else 0) = f m := by
  match m with
  | ⟨0, _⟩ => simp [sumFin8]
  | ⟨1, _⟩ => simp [sumFin8]
  | ⟨2, _⟩ => simp [sumFin8]
  | ⟨3, _⟩ => simp [sumFin8]
  | ⟨4, _⟩ => simp [sumFin8]
  | ⟨5, _⟩ => simp [sumFin8]
  | ⟨6, _⟩ => simp [sumFin8]
  | ⟨7, _⟩ => simp [sumFin8]

theorem sumFin8_sumSubsets {α : Type} (xs : List α) (f : Fin 8 → List α → Nat) :
    sumFin8 (fun s => sumSubsets (f s) xs) = sumSubsets (fun M => sumFin8 (fun s => f s M)) xs := by
  simp only [sumFin8, ← sumSubsets_add]

theorem sumSubsets_map {α β : Type} (g : α → β) (f : List β → Nat) (xs : List α) :
    sumSubsets f (xs.map g) = sumSubsets (fun s => f (s.map g)) xs := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, sumSubsets, ih]

theorem targetDeg_glue_left {n : Nat} (spec : GlueSpec) (L R : TermGraph n) (s : Fin 8) (u : Fin n) :
    targetDeg (glue spec L R) s (leftEmbed u) =
      if u == L.t 0 then bridgeTarget spec s (false, 0)
      else if u == L.t 1 then bridgeTarget spec s (false, 1)
      else if u == L.t 2 then bridgeTarget spec s (false, 2)
      else 1 := by
  unfold targetDeg bridgeTarget glue
  dsimp only
  have heq_t : ∀ (k : Fin 3),
      (leftEmbed u == glueTerm L R (spec.out k)) =
      (if u == L.t 0 then ((false, (0 : Fin 3)) == spec.out k)
       else if u == L.t 1 then ((false, (1 : Fin 3)) == spec.out k)
       else if u == L.t 2 then ((false, (2 : Fin 3)) == spec.out k)
       else false) := by
    intro k
    rcases hok : spec.out k with ⟨b, idx⟩
    cases b
    · simp only [glueTerm, Bool.false_eq_true, ↓reduceIte]
      have h1 : (leftEmbed u == leftEmbed (L.t idx)) = (u == L.t idx) := by
        apply Bool.eq_iff_iff.mpr; simp [leftEmbed, Fin.ext_iff]
      rw [h1]
      by_cases h0 : u = L.t 0
      · subst h0; simp only [beq_self_eq_true, ↓reduceIte]
        apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, Prod.mk.injEq, true_and]
        exact ⟨fun h => L.distinct 0 idx h, fun h => by rw [h]⟩
      · by_cases h1' : u = L.t 1
        · subst h1'; simp only [beq_false_of_ne h0, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, Prod.mk.injEq, true_and]
          exact ⟨fun h => L.distinct 1 idx h, fun h => by rw [h]⟩
        · by_cases h2 : u = L.t 2
          · subst h2; simp only [beq_false_of_ne h0, beq_false_of_ne h1', beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
            apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, Prod.mk.injEq, true_and]
            exact ⟨fun h => L.distinct 2 idx h, fun h => by rw [h]⟩
          · simp only [beq_false_of_ne h0, beq_false_of_ne h1', beq_false_of_ne h2, Bool.false_eq_true, ↓reduceIte]
            apply beq_false_of_ne
            match idx with
            | ⟨0, _⟩ => exact h0
            | ⟨1, _⟩ => exact h1'
            | ⟨2, _⟩ => exact h2
    · have hne_pair : ∀ j : Fin 3, ((false, j) == (true, idx)) = false := by
        intro j; apply beq_false_of_ne; intro h; cases h
      simp only [glueTerm, ↓reduceIte, beq_false_of_ne (leftEmbed_ne_rightEmbed u (R.t idx)),
                 hne_pair, ite_self]
  rw [heq_t 0, heq_t 1, heq_t 2]
  by_cases h0 : (u == L.t 0) = true
  · simp [h0]
  · by_cases h1 : (u == L.t 1) = true
    · simp [Bool.eq_false_iff.mpr h0, h1]
    · by_cases h2 : (u == L.t 2) = true
      · simp [Bool.eq_false_iff.mpr h0, Bool.eq_false_iff.mpr h1, h2]
      · simp [Bool.eq_false_iff.mpr h0, Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2]

theorem targetDeg_glue_right {n : Nat} (spec : GlueSpec) (L R : TermGraph n) (s : Fin 8) (u : Fin n) :
    targetDeg (glue spec L R) s (rightEmbed u) =
      if u == R.t 0 then bridgeTarget spec s (true, 0)
      else if u == R.t 1 then bridgeTarget spec s (true, 1)
      else if u == R.t 2 then bridgeTarget spec s (true, 2)
      else 1 := by
  unfold targetDeg bridgeTarget glue
  dsimp only
  have heq_t : ∀ (k : Fin 3),
      (rightEmbed u == glueTerm L R (spec.out k)) =
      (if u == R.t 0 then ((true, (0 : Fin 3)) == spec.out k)
       else if u == R.t 1 then ((true, (1 : Fin 3)) == spec.out k)
       else if u == R.t 2 then ((true, (2 : Fin 3)) == spec.out k)
       else false) := by
    intro k
    rcases hok : spec.out k with ⟨b, idx⟩
    cases b
    · have hne_pair : ∀ j : Fin 3, ((true, j) == (false, idx)) = false := by
        intro j; apply beq_false_of_ne; intro h; cases h
      simp only [glueTerm, Bool.false_eq_true, ↓reduceIte,
                 beq_false_of_ne (leftEmbed_ne_rightEmbed (L.t idx) u).symm, hne_pair, ite_self]
    · simp only [glueTerm, ↓reduceIte]
      have h1 : (rightEmbed u == rightEmbed (R.t idx)) = (u == R.t idx) := by
        apply Bool.eq_iff_iff.mpr; simp [rightEmbed, Fin.ext_iff]
      rw [h1]
      by_cases h0 : u = R.t 0
      · subst h0; simp only [beq_self_eq_true, ↓reduceIte]
        apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, Prod.mk.injEq, true_and]
        exact ⟨fun h => R.distinct 0 idx h, fun h => by rw [h]⟩
      · by_cases h1' : u = R.t 1
        · subst h1'; simp only [beq_false_of_ne h0, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, Prod.mk.injEq, true_and]
          exact ⟨fun h => R.distinct 1 idx h, fun h => by rw [h]⟩
        · by_cases h2 : u = R.t 2
          · subst h2; simp only [beq_false_of_ne h0, beq_false_of_ne h1', beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
            apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, Prod.mk.injEq, true_and]
            exact ⟨fun h => R.distinct 2 idx h, fun h => by rw [h]⟩
          · simp only [beq_false_of_ne h0, beq_false_of_ne h1', beq_false_of_ne h2, Bool.false_eq_true, ↓reduceIte]
            apply beq_false_of_ne
            match idx with
            | ⟨0, _⟩ => exact h0
            | ⟨1, _⟩ => exact h1'
            | ⟨2, _⟩ => exact h2
  rw [heq_t 0, heq_t 1, heq_t 2]
  by_cases h0 : (u == R.t 0) = true
  · simp [h0]
  · by_cases h1 : (u == R.t 1) = true
    · simp [Bool.eq_false_iff.mpr h0, h1]
    · by_cases h2 : (u == R.t 2) = true
      · simp [Bool.eq_false_iff.mpr h0, Bool.eq_false_iff.mpr h1, h2]
      · simp [Bool.eq_false_iff.mpr h0, Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2]

theorem isInternalPM_glue_iff {n : Nat} (spec : GlueSpec) (L R : TermGraph n) (s : Fin 8)
    (ML MR : List (Edge n)) (B : List (Fin 3 × Fin 3)) :
    (if isInternalPM (glue spec L R) s
        (ML.map mapLeftEdge ++ MR.map mapRightEdge ++ B.map (mapBridgeEdge L R)) then 1 else 0) =
    sumFin8 (fun sL => sumFin8 (fun sR =>
      if bridgePMOk spec sL sR B s && isInternalPM L sL ML && isInternalPM R sR MR then 1 else 0)) := by
  let mL : Fin 8 := bitsToFin8 (degIn (L.t 0) ML == 1) (degIn (L.t 1) ML == 1) (degIn (L.t 2) ML == 1)
  let mR : Fin 8 := bitsToFin8 (degIn (R.t 0) MR == 1) (degIn (R.t 1) MR == 1) (degIn (R.t 2) MR == 1)
  have huniqL : ∀ sL, isInternalPM L sL ML = true → mL = sL := by
    intro sL hL
    simp only [isInternalPM, decide_eq_true_eq] at hL
    have hb : ∀ i : Fin 3, fin8Bit mL i = fin8Bit sL i := by
      intro i
      have hi := hL (L.t i)
      rw [targetDeg_term] at hi
      have hm : fin8Bit mL i = (degIn (L.t i) ML == 1) := by
        unfold mL; rw [fin8Bit_bitsToFin8_at]
        match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
      rw [hm, hi]
      cases fin8Bit sL i <;> rfl
    rw [← bitsToFin8_fin8Bit mL, ← bitsToFin8_fin8Bit sL, hb 0, hb 1, hb 2]
  have huniqR : ∀ sR, isInternalPM R sR MR = true → mR = sR := by
    intro sR hR
    simp only [isInternalPM, decide_eq_true_eq] at hR
    have hb : ∀ j : Fin 3, fin8Bit mR j = fin8Bit sR j := by
      intro j
      have hj := hR (R.t j)
      rw [targetDeg_term] at hj
      have hm : fin8Bit mR j = (degIn (R.t j) MR == 1) := by
        unfold mR; rw [fin8Bit_bitsToFin8_at]
        match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
      rw [hm, hj]
      cases fin8Bit sR j <;> rfl
    rw [← bitsToFin8_fin8Bit mR, ← bitsToFin8_fin8Bit sR, hb 0, hb 1, hb 2]
  have hrhs :
      sumFin8 (fun sL => sumFin8 (fun sR =>
        if bridgePMOk spec sL sR B s && isInternalPM L sL ML && isInternalPM R sR MR then 1 else 0)) =
      (if bridgePMOk spec mL mR B s && isInternalPM L mL ML && isInternalPM R mR MR then 1 else 0) := by
    rw [sumFin8_congr (fun sL => by
      show (sumFin8 fun sR =>
              if bridgePMOk spec sL sR B s && isInternalPM L sL ML && isInternalPM R sR MR then 1 else 0) =
           (if mL == sL then
              if bridgePMOk spec sL mR B s && isInternalPM L sL ML && isInternalPM R mR MR then 1 else 0
            else 0)
      rw [sumFin8_congr (fun sR => by
        show (if bridgePMOk spec sL sR B s && isInternalPM L sL ML && isInternalPM R sR MR then 1 else 0) =
             (if mL == sL then (if mR == sR then
               if bridgePMOk spec sL sR B s && isInternalPM L sL ML && isInternalPM R sR MR then 1 else 0
               else 0) else 0)
        cases hL : isInternalPM L sL ML
        · simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ite_self]
        · have heqL : (mL == sL) = true := beq_iff_eq.mpr (huniqL sL hL)
          cases hR : isInternalPM R sR MR
          · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, ite_self]
          · have heqR : (mR == sR) = true := beq_iff_eq.mpr (huniqR sR hR)
            simp only [heqL, heqR, ↓reduceIte])]
      by_cases hL : (mL == sL) = true
      · simp only [hL, ↓reduceIte]; exact sumFin8_single mR _
      · have hLf : (mL == sL) = false := Bool.eq_false_iff.mpr hL
        simp only [hLf, Bool.false_eq_true, ↓reduceIte]; rfl)]
    exact sumFin8_single mL _
  rw [hrhs]
  suffices hbool :
      isInternalPM (glue spec L R) s
        (ML.map mapLeftEdge ++ MR.map mapRightEdge ++ B.map (mapBridgeEdge L R)) =
      (bridgePMOk spec mL mR B s && isInternalPM L mL ML && isInternalPM R mR MR) by
    rw [hbool]
  apply Bool.eq_iff_iff.mpr
  simp only [isInternalPM, bridgePMOk, Bool.and_eq_true, decide_eq_true_eq]
  have hdegL : ∀ u : Fin n,
      degIn (leftEmbed u) (ML.map mapLeftEdge ++ MR.map mapRightEdge ++ B.map (mapBridgeEdge L R)) =
      degIn u ML + (if u == L.t 0 then degBridgeL 0 B
                    else if u == L.t 1 then degBridgeL 1 B
                    else if u == L.t 2 then degBridgeL 2 B else 0) := by
    intro u
    rw [degIn_append, degIn_append, degIn_mapLeft_left, degIn_mapRight_left, degIn_mapBridge_left]
    omega
  have hdegR : ∀ u : Fin n,
      degIn (rightEmbed u) (ML.map mapLeftEdge ++ MR.map mapRightEdge ++ B.map (mapBridgeEdge L R)) =
      degIn u MR + (if u == R.t 0 then degBridgeR 0 B
                    else if u == R.t 1 then degBridgeR 1 B
                    else if u == R.t 2 then degBridgeR 2 B else 0) := by
    intro u
    rw [degIn_append, degIn_append, degIn_mapLeft_right, degIn_mapRight_right, degIn_mapBridge_right]
    omega
  have hbt_le : ∀ p, bridgeTarget spec s p ≤ 1 := by
    intro p; unfold bridgeTarget
    cases (p == spec.out 0) <;> cases (p == spec.out 1) <;> cases (p == spec.out 2) <;>
    cases fin8Bit s 0 <;> cases fin8Bit s 1 <;> cases fin8Bit s 2 <;> simp
  constructor
  · intro h
    have hL_deg : ∀ u : Fin n,
        degIn u ML + (if u == L.t 0 then degBridgeL 0 B
                      else if u == L.t 1 then degBridgeL 1 B
                      else if u == L.t 2 then degBridgeL 2 B else 0) =
        (if u == L.t 0 then bridgeTarget spec s (false, 0)
         else if u == L.t 1 then bridgeTarget spec s (false, 1)
         else if u == L.t 2 then bridgeTarget spec s (false, 2) else 1) := by
      intro u; have hu := h (leftEmbed u); rwa [hdegL u, targetDeg_glue_left] at hu
    have hR_deg : ∀ u : Fin n,
        degIn u MR + (if u == R.t 0 then degBridgeR 0 B
                      else if u == R.t 1 then degBridgeR 1 B
                      else if u == R.t 2 then degBridgeR 2 B else 0) =
        (if u == R.t 0 then bridgeTarget spec s (true, 0)
         else if u == R.t 1 then bridgeTarget spec s (true, 1)
         else if u == R.t 2 then bridgeTarget spec s (true, 2) else 1) := by
      intro u; have hu := h (rightEmbed u); rwa [hdegR u, targetDeg_glue_right] at hu
    have h01L : (L.t 1 == L.t 0) = false := beq_false_of_ne (fun h => by have := L.distinct 1 0 h; cases this)
    have h02L : (L.t 2 == L.t 0) = false := beq_false_of_ne (fun h => by have := L.distinct 2 0 h; cases this)
    have h12L : (L.t 2 == L.t 1) = false := beq_false_of_ne (fun h => by have := L.distinct 2 1 h; cases this)
    have h01R : (R.t 1 == R.t 0) = false := beq_false_of_ne (fun h => by have := R.distinct 1 0 h; cases this)
    have h02R : (R.t 2 == R.t 0) = false := beq_false_of_ne (fun h => by have := R.distinct 2 0 h; cases this)
    have h12R : (R.t 2 == R.t 1) = false := beq_false_of_ne (fun h => by have := R.distinct 2 1 h; cases this)
    have hL_term : ∀ i : Fin 3, degIn (L.t i) ML + degBridgeL i B = bridgeTarget spec s (false, i) := by
      intro i
      match i with
      | ⟨0, _⟩ => simpa using hL_deg (L.t 0)
      | ⟨1, _⟩ => simpa [h01L] using hL_deg (L.t 1)
      | ⟨2, _⟩ => simpa [h02L, h12L] using hL_deg (L.t 2)
    have hR_term : ∀ j : Fin 3, degIn (R.t j) MR + degBridgeR j B = bridgeTarget spec s (true, j) := by
      intro j
      match j with
      | ⟨0, _⟩ => simpa using hR_deg (R.t 0)
      | ⟨1, _⟩ => simpa [h01R] using hR_deg (R.t 1)
      | ⟨2, _⟩ => simpa [h02R, h12R] using hR_deg (R.t 2)
    have hmL_val : ∀ i : Fin 3, (if fin8Bit mL i then 1 else 0) = degIn (L.t i) ML := by
      intro i
      have hle : degIn (L.t i) ML ≤ 1 := by have := hL_term i; have := hbt_le (false, i); omega
      have hm : fin8Bit mL i = (degIn (L.t i) ML == 1) := by
        unfold mL; rw [fin8Bit_bitsToFin8_at]
        match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
      rw [hm]
      cases hd : degIn (L.t i) ML with
      | zero => rfl
      | succ d => cases d with | zero => rfl | succ _ => omega
    have hmR_val : ∀ j : Fin 3, (if fin8Bit mR j then 1 else 0) = degIn (R.t j) MR := by
      intro j
      have hle : degIn (R.t j) MR ≤ 1 := by have := hR_term j; have := hbt_le (true, j); omega
      have hm : fin8Bit mR j = (degIn (R.t j) MR == 1) := by
        unfold mR; rw [fin8Bit_bitsToFin8_at]
        match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
      rw [hm]
      cases hd : degIn (R.t j) MR with
      | zero => rfl
      | succ d => cases d with | zero => rfl | succ _ => omega
    refine ⟨⟨⟨fun i => by rw [hmL_val i]; exact hL_term i,
              fun j => by rw [hmR_val j]; exact hR_term j⟩, ?_⟩, ?_⟩
    · intro u
      by_cases h0 : u = L.t 0
      · subst h0; rw [targetDeg_term, hmL_val 0]
      · by_cases h1 : u = L.t 1
        · subst h1; rw [targetDeg_term, hmL_val 1]
        · by_cases h2 : u = L.t 2
          · subst h2; rw [targetDeg_term, hmL_val 2]
          · have hu := hL_deg u
            simp [targetDeg, beq_false_of_ne h0, beq_false_of_ne h1, beq_false_of_ne h2] at hu ⊢
            exact hu
    · intro u
      by_cases h0 : u = R.t 0
      · subst h0; rw [targetDeg_term, hmR_val 0]
      · by_cases h1 : u = R.t 1
        · subst h1; rw [targetDeg_term, hmR_val 1]
        · by_cases h2 : u = R.t 2
          · subst h2; rw [targetDeg_term, hmR_val 2]
          · have hu := hR_deg u
            simp [targetDeg, beq_false_of_ne h0, beq_false_of_ne h1, beq_false_of_ne h2] at hu ⊢
            exact hu
  · rintro ⟨⟨⟨hBL, hBR⟩, hL⟩, hR⟩ v
    by_cases hv : v.val < n
    · have hv_eq : v = leftEmbed ⟨v.val, hv⟩ := Fin.ext rfl
      rw [hv_eq, hdegL, targetDeg_glue_left]
      generalize (⟨v.val, hv⟩ : Fin n) = u
      by_cases h0 : u = L.t 0
      · subst h0; have := hL (L.t 0); rw [targetDeg_term] at this; simpa [this] using hBL 0
      · by_cases h1 : u = L.t 1
        · subst h1; have := hL (L.t 1); rw [targetDeg_term] at this
          simpa [beq_false_of_ne h0, this] using hBL 1
        · by_cases h2 : u = L.t 2
          · subst h2; have := hL (L.t 2); rw [targetDeg_term] at this
            simpa [beq_false_of_ne h0, beq_false_of_ne h1, this] using hBL 2
          · have := hL u
            simp [targetDeg, beq_false_of_ne h0, beq_false_of_ne h1, beq_false_of_ne h2] at this ⊢
            exact this
    · have hv_eq : v = rightEmbed ⟨v.val - n, by omega⟩ := Fin.ext (by simp [rightEmbed]; omega)
      rw [hv_eq, hdegR, targetDeg_glue_right]
      generalize (⟨v.val - n, by omega⟩ : Fin n) = u
      by_cases h0 : u = R.t 0
      · subst h0; have := hR (R.t 0); rw [targetDeg_term] at this; simpa [this] using hBR 0
      · by_cases h1 : u = R.t 1
        · subst h1; have := hR (R.t 1); rw [targetDeg_term] at this
          simpa [beq_false_of_ne h0, this] using hBR 1
        · by_cases h2 : u = R.t 2
          · subst h2; have := hR (R.t 2); rw [targetDeg_term] at this
            simpa [beq_false_of_ne h0, beq_false_of_ne h1, this] using hBR 2
          · have := hR u
            simp [targetDeg, beq_false_of_ne h0, beq_false_of_ne h1, beq_false_of_ne h2] at this ⊢
            exact this

/-- **GENERIC SOUNDNESS THEOREM 2 (`BitTransfer3.PM`)**:
    For ANY 3-terminal gluing specification `spec` and ANY two `TermGraph n` instances `L, R`,
    the exact 8-state perfect-matching vector of `glue spec L R` equals `stepPM spec`. -/
theorem glue_pm_sound {n : Nat} (spec : GlueSpec) (L R : TermGraph n) (s : Fin 8) :
    pmVec (glue spec L R) s = stepPM spec (pmVec L) (pmVec R) s := by
  unfold pmVec stepPM
  have hperm_inv : ∀ s1 s2 : List (Edge (n + n)), s1.Perm s2 →
      (if isInternalPM (glue spec L R) s s1 then 1 else 0) =
      (if isInternalPM (glue spec L R) s s2 then 1 else 0) := by
    intro s1 s2 hp
    suffices h : isInternalPM (glue spec L R) s s1 = isInternalPM (glue spec L R) s s2 by rw [h]
    apply Bool.eq_iff_iff.mpr
    simp only [isInternalPM, decide_eq_true_eq]
    constructor
    · intro h v; rw [← degIn_perm v hp]; exact h v
    · intro h v; rw [degIn_perm v hp]; exact h v
  rw [sumSubsets_perm hperm_inv (allEdges_glue_perm spec L R)]
  rw [sumSubsets_append, sumSubsets_append]
  simp only [sumSubsets_map]
  rw [sumSubsets_congr (fun ML => sumSubsets_congr (fun MR => sumSubsets_congr (fun B =>
    isInternalPM_glue_iff spec L R s ML MR B)))]
  simp only [← sumFin8_sumSubsets]
  apply sumFin8_congr; intro sL
  apply sumFin8_congr; intro sR
  have hfactor : ∀ ML MR B,
      (if bridgePMOk spec sL sR B s && isInternalPM L sL ML && isInternalPM R sR MR then 1 else 0) =
      (if isInternalPM L sL ML then 1 else 0) *
      ((if isInternalPM R sR MR then 1 else 0) *
       (if bridgePMOk spec sL sR B s then 1 else 0)) := by
    intro ML MR B
    cases bridgePMOk spec sL sR B s <;> cases isInternalPM L sL ML <;> cases isInternalPM R sR MR <;> rfl
  rw [sumSubsets_congr (fun ML => sumSubsets_congr (fun MR => sumSubsets_congr (fun B => hfactor ML MR B)))]
  simp only [sumSubsets_mul_left, sumSubsets_mul_right]
  have hrhs_f : ∀ B,
      (if bridgePMOk spec sL sR B s then
        sumSubsets (fun ML => if isInternalPM L sL ML then 1 else 0) (allEdges L.graph) *
        sumSubsets (fun MR => if isInternalPM R sR MR then 1 else 0) (allEdges R.graph)
       else 0) =
      (sumSubsets (fun ML => if isInternalPM L sL ML then 1 else 0) (allEdges L.graph) *
       sumSubsets (fun MR => if isInternalPM R sR MR then 1 else 0) (allEdges R.graph)) *
      (if bridgePMOk spec sL sR B s then 1 else 0) := by
    intro B; cases bridgePMOk spec sL sR B s <;> simp
  rw [sumSubsets_congr hrhs_f, sumSubsets_mul_left, Nat.mul_assoc]

-- ----------------------------------------------------------------------------
-- 3C. Generic Chromatic Polynomial & Bell-Partition Soundness (`BitTransfer3.Chrom`)
-- ----------------------------------------------------------------------------

theorem pat3_congr {α β : Type} [DecidableEq α] [DecidableEq β]
    {a1 b1 c1 : α} {a2 b2 c2 : β}
    (hab : a1 = b1 ↔ a2 = b2) (hac : a1 = c1 ↔ a2 = c2) (hbc : b1 = c1 ↔ b2 = c2) :
    pat3 a1 b1 c1 = pat3 a2 b2 c2 := by
  unfold pat3
  by_cases h1 : a1 = b1
  · have h1' := hab.mp h1
    by_cases h2 : b1 = c1
    · have h2' := hbc.mp h2
      simp only [h1, h1', h2, h2', ↓reduceIte]
    · have h2' := mt hbc.mpr h2
      simp only [h1, h1', h2, h2', ↓reduceIte]
  · have h1' := mt hab.mpr h1
    by_cases h2 : a1 = c1
    · have h2' := hac.mp h2
      rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_right_iff.mpr (fun h => absurd h h1'),
          ite_eq_left_iff.mpr (fun h => absurd h2 h), ite_eq_left_iff.mpr (fun h => absurd h2' h)]
    · have h2' := mt hac.mpr h2
      rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_right_iff.mpr (fun h => absurd h h1'),
          ite_eq_right_iff.mpr (fun h => absurd h h2), ite_eq_right_iff.mpr (fun h => absurd h h2')]
      by_cases h3 : b1 = c1
      · have h3' := hbc.mp h3
        simp only [h3, h3', ↓reduceIte]
      · have h3' := mt hbc.mpr h3
        simp only [h3, h3', ↓reduceIte]

theorem pEval_sumFinRangePoly (m : Nat) (f : Nat → Poly) (q : Int) :
    pEval (sumFinRangePoly m f) q = ((List.range m).map (fun c => pEval (f c) q)).sum := by
  induction m with
  | zero => simp [sumFinRangePoly, pEval]
  | succ m ih =>
    rw [sumFinRangePoly, pEval_add, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem list_map_sum_eq_range_sum {α : Type} (xs : List α) (g : α → Int) (h : Nat → Int)
    (hmatch : ∀ (i : Nat) (hi : i < xs.length), g (xs[i]'hi) = h i) :
    (xs.map g).sum = ((List.range xs.length).map h).sum := by
  induction xs generalizing h with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.range_succ_eq_map]
    rw [List.map_map]
    have h0 : g x = h 0 := hmatch 0 (by simp)
    rw [h0]
    congr 1
    exact ih (fun i => h (i + 1)) (fun i hi => hmatch (i + 1) (by simp; omega))

theorem nodup_append_singleton {α : Type} {xs : List α} {y : α} (hnd : xs.Nodup) (hy : y ∉ xs) :
    (xs ++ [y]).Nodup := by
  rw [List.nodup_append]
  refine ⟨hnd, by simp, ?_⟩
  intro a ha b hb heq
  subst heq
  have hby : a = y := List.mem_singleton.mp hb
  exact hy (hby ▸ ha)

/-- **Master Symbolic Summation Lemma**: evaluates any `depth`-fold sum over `Fin q` of a
    pattern-invariant function into `pEval (sumChoicePoly depth xs.length f) q` for ALL `q : Nat`. -/
theorem sumChoicePoly_sound (q : Nat) (depth : Nat)
    (xs : List (Fin q)) (hnd : xs.Nodup)
    (F : List (Fin q) → Int) (f : List Nat → Poly)
    (hmatch : ∀ ys ls, ys.length = depth → MatchesPalette xs ys ls → F ys = pEval (f ls) (q : Int)) :
    sumColoringsList q depth F = pEval (sumChoicePoly depth xs.length f) (q : Int) := by
  induction depth generalizing xs F f with
  | zero =>
    exact hmatch [] [] rfl (MatchesPalette.nil xs)
  | succ d ih =>
    simp only [sumColoringsList, sumChoicePoly, pEval_add, pEval_mul, pEval_lin,
               pEval_sumFinRangePoly]
    let cFresh : Int := pEval (sumChoicePoly d (xs.length + 1) (fun rest => f (xs.length :: rest))) (q : Int)
    have hfresh : ∀ y : Fin q, y ∉ xs →
        sumColoringsList q d (fun ys => F (y :: ys)) = cFresh := by
      intro y hy
      have hnd' := nodup_append_singleton hnd hy
      have hlen : (xs ++ [y]).length = xs.length + 1 := by simp
      have h1 := ih (xs ++ [y]) hnd' (fun ys => F (y :: ys)) (fun rest => f (xs.length :: rest))
        (fun ys ls hyl hm => hmatch (y :: ys) (xs.length :: ls) (by simp [hyl]) (MatchesPalette.fresh xs y hy ys ls hm))
      rw [h1, hlen]
    rw [sumFinInt_split q xs hnd _ cFresh hfresh]
    congr 1
    apply list_map_sum_eq_range_sum
    intro i hi
    exact ih xs hnd (fun ys => F (xs[i]'hi :: ys)) (fun rest => f (i :: rest))
      (fun ys ls hyl hm => hmatch (xs[i]'hi :: ys) (i :: ls) (by simp [hyl]) (MatchesPalette.old xs i hi ys ls hm))

theorem sumFin_zero_fn (m : Nat) : sumFin m (fun _ => 0) = 0 := by
  induction m with
  | zero => rfl
  | succ k ih => simp [sumFin, ih]

theorem sumColorings_zero_fn (q n : Nat) : sumColorings q n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumColorings]
    rw [sumFin_congr (fun _ => ih)]
    exact sumFin_zero_fn q

theorem sumFin_sumColorings (q n m : Nat) (f : Fin m → (Fin n → Fin q) → Nat) :
    sumFin m (fun i => sumColorings q n (f i)) =
    sumColorings q n (fun c => sumFin m (fun i => f i c)) := by
  induction m with
  | zero => simp only [sumFin]; exact (sumColorings_zero_fn q n).symm
  | succ m' ih => simp only [sumFin, ih, sumColorings_add]

/-- Key palette-equality invariance: colors picked via `MatchesPalette` have the exact same
    equality relation as their canonical symbolic indices! -/
theorem matchesPalette_to_env {q : Nat} {xs ys : List (Fin q)} {ls : List Nat}
    (hnd : xs.Nodup) (hm : MatchesPalette xs ys ls) :
    ∃ (pal : List (Fin q)) (hlen : ys.length = ls.length),
      pal.Nodup ∧
      (∀ (i : Nat) (hi : i < xs.length), ∃ h' : i < pal.length, pal[i]'h' = xs[i]'hi) ∧
      (∀ (k : Nat) (hk : k < ys.length),
        ∃ h' : ls[k]'(hlen ▸ hk) < pal.length, pal[ls[k]'(hlen ▸ hk)]'h' = ys[k]'hk) := by
  induction hm with
  | nil xs =>
    exact ⟨xs, rfl, hnd, fun i hi => ⟨hi, rfl⟩, fun k hk => by simp at hk⟩
  | old xs i hi ys ls hm ih =>
    rcases ih hnd with ⟨pal, hlen, hpal_nd, hxs_pal, hys_pal⟩
    refine ⟨pal, by simp [hlen], hpal_nd, hxs_pal, ?_⟩
    intro k hk
    cases k with
    | zero =>
      rcases hxs_pal i hi with ⟨h', heq⟩
      exact ⟨h', heq⟩
    | succ k' =>
      exact hys_pal k' (by simp at hk; omega)
  | fresh xs y hy ys ls hm ih =>
    have hnd' := nodup_append_singleton hnd hy
    rcases ih hnd' with ⟨pal, hlen, hpal_nd, hxs_pal, hys_pal⟩
    refine ⟨pal, by simp [hlen], hpal_nd, ?_, ?_⟩
    · intro i hi
      rcases hxs_pal i (by simp; omega) with ⟨h', heq⟩
      refine ⟨h', ?_⟩
      rw [heq]; simp [List.getElem_append_left hi]
    · intro k hk
      cases k with
      | zero =>
        rcases hxs_pal xs.length (by simp) with ⟨h', heq⟩
        refine ⟨h', ?_⟩
        simp only [List.getElem_cons_zero]
        rw [heq]; simp
      | succ k' =>
        exact hys_pal k' (by simp at hk; omega)

theorem nodup_getElem_eq_iff {α : Type} :
    ∀ {pal : List α}, pal.Nodup →
      ∀ {i j : Nat} (hi : i < pal.length) (hj : j < pal.length),
        pal[i]'hi = pal[j]'hj ↔ i = j
  | [], _, _, _, hi, _ => by simp at hi
  | x :: xs, hnd, i, j, hi, hj => by
    have ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => simp
      | succ j' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.zero_ne_add_one, iff_false]
        intro heq
        exact hx (heq ▸ List.getElem_mem _)
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_succ, List.getElem_cons_zero, Nat.add_one_ne_zero, iff_false]
        intro heq
        exact hx (heq.symm ▸ List.getElem_mem _)
      | succ j' =>
        simp only [List.getElem_cons_succ, Nat.add_right_cancel_iff]
        exact nodup_getElem_eq_iff hxs _ _

/-- **Total Chromatic Polynomial Soundness**:
    `HasChromVec G v` implies `(exactChromCount G.graph q : Int) = pEval (totalChromPoly v) q` ∀ `q`. -/
theorem totalChrom_of_hasChromVec {n : Nat} {G : TermGraph n} {v : Fin 5 → Poly}
    (hv : HasChromVec G v) (q : Nat) :
    (exactChromCount G.graph q : Int) = pEval (totalChromPoly v) (q : Int) := by
  have hsum : exactChromCount G.graph q =
      sumFin q (fun c0 => sumFin q (fun c1 => sumFin q (fun c2 => chromFixed G q c0 c1 c2))) := by
    unfold exactChromCount chromFixed
    simp only [sumFin_sumColorings]
    apply sumColorings_congr; intro c
    cases isProperColoring G.graph c
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, sumFin_zero_fn]
    · simp only [Bool.true_and]
      have h1 : ∀ (x : Fin q) (f : Fin q → Nat), sumFin q (fun d => if x == d then f d else 0) = f x := by
        intro x f
        have hInt := sumFinInt_single q x (f x : Int)
        have hcast : (sumFin q (fun d => if x == d then f d else 0) : Int) =
                     sumFinInt q (fun d => if d = x then (f x : Int) else 0) := by
          rw [sumFinInt_ofNat]
          apply sumFinInt_congr; intro d
          by_cases hdx : d = x
          · subst hdx; simp
          · have hne : (x == d) = false := beq_false_of_ne (Ne.symm hdx)
            simp [hdx, hne]
        omega
      have hstep : ∀ (x0 x1 x2 : Fin q),
          sumFin q (fun c0 => sumFin q (fun c1 => sumFin q (fun c2 =>
            if ((x0 == c0) && (x1 == c1) && (x2 == c2)) = true then 1 else 0))) = 1 := by
        intro x0 x1 x2
        have hb : ∀ c0 c1 c2,
            (if ((x0 == c0) && (x1 == c1) && (x2 == c2)) = true then 1 else 0) =
            (if x0 == c0 then if x1 == c1 then if x2 == c2 then 1 else 0 else 0 else 0) := by
          intro c0 c1 c2; cases (x0 == c0) <;> cases (x1 == c1) <;> cases (x2 == c2) <;> rfl
        simp only [hb]
        have hzero_if : ∀ (b : Bool) (g : Fin q → Nat),
            sumFin q (fun d => if b then g d else 0) = if b then sumFin q g else 0 := by
          intro b g; cases b <;> simp [sumFin_zero_fn]
        simp only [hzero_if, h1]
      exact (hstep (c (G.t 0)) (c (G.t 1)) (c (G.t 2))).symm
  rw [hsum, sumFinInt_ofNat]
  simp only [sumFinInt_ofNat]
  change sumColoringsList q 3 (fun ys => match ys with
    | [c0, c1, c2] => (chromFixed G q c0 c1 c2 : Int)
    | _ => 0) = pEval (totalChromPoly v) (q : Int)
  apply sumChoicePoly_sound q 3 [] List.nodup_nil
  intro ys ls hylen hm
  rcases matchesPalette_to_env List.nodup_nil hm with ⟨pal, hlen, hpal_nd, _, hys_pal⟩
  cases ys with
  | nil => simp at hylen
  | cons c0 r0 => cases r0 with
    | nil => simp at hylen
    | cons c1 r1 => cases r1 with
      | nil => simp at hylen
      | cons c2 r2 => cases r2 with
        | cons _ _ => simp at hylen
        | nil =>
          cases ls with
          | nil => simp at hlen
          | cons l0 s0 => cases s0 with
            | nil => simp at hlen
            | cons l1 s1 => cases s1 with
              | nil => simp at hlen
              | cons l2 s2 => cases s2 with
                | cons _ _ => simp at hlen
                | nil =>
                  dsimp only
                  rw [hv q c0 c1 c2]
                  rcases hys_pal 0 (by simp) with ⟨h0, heq0⟩
                  rcases hys_pal 1 (by simp) with ⟨h1, heq1⟩
                  rcases hys_pal 2 (by simp) with ⟨h2, heq2⟩
                  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq0 heq1 heq2
                  congr 2
                  apply pat3_congr
                  · rw [← heq0, ← heq1]; exact nodup_getElem_eq_iff hpal_nd h0 h1
                  · rw [← heq0, ← heq2]; exact nodup_getElem_eq_iff hpal_nd h0 h2
                  · rw [← heq1, ← heq2]; exact nodup_getElem_eq_iff hpal_nd h1 h2

theorem assign6_out {α : Type} (spec : GlueSpec) (o0 o1 o2 d0 d1 d2 : α) (k : Fin 3) :
    assign6 spec o0 o1 o2 d0 d1 d2 (spec.out k) =
      match k with | ⟨0, _⟩ => o0 | ⟨1, _⟩ => o1 | ⟨2, _⟩ => o2 := by
  have h10 : (spec.out 1 == spec.out 0) = false := beq_false_of_ne (fun h => by have := spec.out_distinct 1 0 h; cases this)
  have h20 : (spec.out 2 == spec.out 0) = false := beq_false_of_ne (fun h => by have := spec.out_distinct 2 0 h; cases this)
  have h21 : (spec.out 2 == spec.out 1) = false := beq_false_of_ne (fun h => by have := spec.out_distinct 2 1 h; cases this)
  match k with
  | ⟨0, _⟩ => simp [assign6]
  | ⟨1, _⟩ => simp [assign6, h10]
  | ⟨2, _⟩ => simp [assign6, h20, h21]

theorem assign6_int {α : Type} (spec : GlueSpec) (o0 o1 o2 d0 d1 d2 : α) (k : Fin 3) :
    assign6 spec o0 o1 o2 d0 d1 d2 (spec.intTerm k) =
      match k with | ⟨0, _⟩ => d0 | ⟨1, _⟩ => d1 | ⟨2, _⟩ => d2 := by
  have hd : ∀ i j : Fin 3, (spec.intTerm j == spec.out i) = false :=
    fun i j => beq_false_of_ne (spec.disjoint_out_int i j).symm
  have h10 : (spec.intTerm 1 == spec.intTerm 0) = false := beq_false_of_ne (fun h => by have := spec.int_distinct 1 0 h; cases this)
  have h20 : (spec.intTerm 2 == spec.intTerm 0) = false := beq_false_of_ne (fun h => by have := spec.int_distinct 2 0 h; cases this)
  have h21 : (spec.intTerm 2 == spec.intTerm 1) = false := beq_false_of_ne (fun h => by have := spec.int_distinct 2 1 h; cases this)
  match k with
  | ⟨0, _⟩ => simp [assign6, hd 0 0, hd 1 0, hd 2 0]
  | ⟨1, _⟩ => simp [assign6, hd 0 1, hd 1 1, hd 2 1, h10]
  | ⟨2, _⟩ => simp [assign6, hd 0 2, hd 1 2, hd 2 2, h20, h21]

theorem isProperColoring_glue_iff {n q : Nat} (spec : GlueSpec) (L R : TermGraph n)
    (cL cR : Fin n → Fin q) :
    isProperColoring (glue spec L R).graph (appendFun cL cR) =
      (isProperColoring L.graph cL && isProperColoring R.graph cR &&
       bridgesProper spec (fun p => if p.1 then cR (R.t p.2) else cL (L.t p.2))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [isProperColoring, bridgesProper, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro u v huv
      have h' := h (leftEmbed u) (leftEmbed v)
        (by simpa [glue, glueAdj, leftEmbed, u.isLt, v.isLt] using huv)
      simpa [leftEmbed, appendFun_left] using h'
    · intro u v huv
      have hnu : ¬ (n + u.val < n) := by omega
      have hnv : ¬ (n + v.val < n) := by omega
      have hsu : n + u.val - n = u.val := by omega
      have hsv : n + v.val - n = v.val := by omega
      have h' := h (rightEmbed u) (rightEmbed v)
        (by simpa [glue, glueAdj, rightEmbed, hnu, hnv, hsu, hsv] using huv)
      simpa [rightEmbed, appendFun_right] using h'
    · intro i j hbr
      have hnv : ¬ (n + (R.t j).val < n) := by omega
      have hsv : n + (R.t j).val - n = (R.t j).val := by omega
      have hadj : (glue spec L R).graph.adj (leftEmbed (L.t i)) (rightEmbed (R.t j)) = true := by
        simp only [glue, glueAdj, leftEmbed, rightEmbed, (L.t i).isLt, ↓reduceDIte, hnv, hasBridge]
        exact decide_eq_true ⟨i, j, Fin.ext rfl, Fin.ext hsv, hbr⟩
      have h' := h (leftEmbed (L.t i)) (rightEmbed (R.t j)) hadj
      simpa [leftEmbed, rightEmbed, appendFun_left, appendFun_right] using h'
  · rintro ⟨⟨hL, hR⟩, hB⟩ u v huv
    unfold glue at huv; dsimp only at huv; unfold glueAdj at huv
    by_cases hu : u.val < n <;> by_cases hv : v.val < n
    · simp only [hu, hv, ↓reduceDIte] at huv
      simpa [appendFun, hu, hv] using hL ⟨u.val, hu⟩ ⟨v.val, hv⟩ huv
    · simp only [hu, hv, ↓reduceDIte, hasBridge, decide_eq_true_eq] at huv
      rcases huv with ⟨i, j, hui, hvj, hbr⟩
      have h' := hB i j hbr
      simpa [appendFun, hu, hv, ← hui, ← hvj] using h'
    · simp only [hu, hv, ↓reduceDIte, hasBridge, decide_eq_true_eq] at huv
      rcases huv with ⟨i, j, hvi, huj, hbr⟩
      have h' := hB i j hbr
      simpa [appendFun, hu, hv, ← hvi, ← huj] using h'.symm
    · simp only [hu, hv, ↓reduceDIte] at huv
      simpa [appendFun, hu, hv] using hR ⟨u.val - n, by omega⟩ ⟨v.val - n, by omega⟩ huv

/-- **GENERIC SOUNDNESS THEOREM 3 (`BitTransfer3.Chrom`)**:
    For ANY 3-terminal gluing specification `spec` and ANY two `TermGraph n` instances `L, R`,
    if `vL` and `vR` are their 5-state Bell chromatic vectors, then `stepChromPoly spec vL vR`
    is the exact 5-state Bell chromatic vector of `glue spec L R` for ALL `q : Nat`. -/
theorem glue_chrom_sound {n : Nat} (spec : GlueSpec) (L R : TermGraph n)
    {vL vR : Fin 5 → Poly} (hvL : HasChromVec L vL) (hvR : HasChromVec R vR) :
    HasChromVec (glue spec L R) (stepChromPoly spec vL vR) := by
  intro q o0 o1 o2
  -- First express `chromFixed (glue spec L R) q o0 o1 o2` as a 3-fold sum over internalized terminal colors `(d0, d1, d2)`
  have htriple :
      chromFixed (glue spec L R) q o0 o1 o2 =
      sumFin q (fun d0 => sumFin q (fun d1 => sumFin q (fun d2 =>
        let col := assign6 spec o0 o1 o2 d0 d1 d2
        if bridgesProper spec col then
          chromFixed L q (col (false, 0)) (col (false, 1)) (col (false, 2)) *
          chromFixed R q (col (true, 0))  (col (true, 1))  (col (true, 2))
        else 0))) := by
    unfold chromFixed
    rw [sumColorings_append]
    have hrhs_pull : ∀ d0 d1 d2,
        (let col := assign6 spec o0 o1 o2 d0 d1 d2
         if bridgesProper spec col then
           sumColorings q n (fun cL => if isProperColoring L.graph cL && (cL (L.t 0) == col (false, 0)) && (cL (L.t 1) == col (false, 1)) && (cL (L.t 2) == col (false, 2)) then 1 else 0) *
           sumColorings q n (fun cR => if isProperColoring R.graph cR && (cR (R.t 0) == col (true, 0))  && (cR (R.t 1) == col (true, 1))  && (cR (R.t 2) == col (true, 2))  then 1 else 0)
         else 0) =
        sumColorings q n (fun cL => sumColorings q n (fun cR =>
          let col := assign6 spec o0 o1 o2 d0 d1 d2
          if bridgesProper spec col &&
             (isProperColoring L.graph cL && (cL (L.t 0) == col (false, 0)) && (cL (L.t 1) == col (false, 1)) && (cL (L.t 2) == col (false, 2))) &&
             (isProperColoring R.graph cR && (cR (R.t 0) == col (true, 0))  && (cR (R.t 1) == col (true, 1))  && (cR (R.t 2) == col (true, 2)))
          then 1 else 0)) := by
      intro d0 d1 d2
      dsimp only
      let col := assign6 spec o0 o1 o2 d0 d1 d2
      have hfac : ∀ (a b c : Bool),
          (if a && b && c then 1 else 0) =
          (if a then 1 else 0) * ((if b then 1 else 0) * (if c then 1 else 0)) := by
        intro a b c; cases a <;> cases b <;> cases c <;> rfl
      simp only [hfac, sumColorings_mul_left, sumColorings_mul_right]
      cases bridgesProper spec col <;> simp
    rw [sumFin_congr (fun d0 => sumFin_congr (fun d1 => sumFin_congr (fun d2 => hrhs_pull d0 d1 d2)))]
    simp only [sumFin_sumColorings]
    apply sumColorings_congr; intro cL
    apply sumColorings_congr; intro cR
    let val6 : Bool × Fin 3 → Fin q := fun p => if p.1 then cR (R.t p.2) else cL (L.t p.2)
    have hterm_eq : ∀ (k : Fin 3), appendFun cL cR ((glue spec L R).t k) = val6 (spec.out k) := by
      intro k; unfold glue glueTerm val6; dsimp only
      cases (spec.out k).1
      · simp [leftEmbed, appendFun_left]
      · simp [rightEmbed, appendFun_right]
    have hmatch6 : ∀ d0 d1 d2,
        ((cL (L.t 0) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 0)) &&
         (cL (L.t 1) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 1)) &&
         (cL (L.t 2) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 2)) &&
         (cR (R.t 0) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 0)) &&
         (cR (R.t 1) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 1)) &&
         (cR (R.t 2) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 2))) =
        ((val6 (spec.out 0) == o0) && (val6 (spec.out 1) == o1) && (val6 (spec.out 2) == o2) &&
         (val6 (spec.intTerm 0) == d0) && (val6 (spec.intTerm 1) == d1) && (val6 (spec.intTerm 2) == d2)) := by
      intro d0 d1 d2
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩
        have hall : ∀ p : Bool × Fin 3, val6 p = assign6 spec o0 o1 o2 d0 d1 d2 p := by
          rintro ⟨b, idx⟩
          cases b
          · match idx with | ⟨0, _⟩ => exact h0 | ⟨1, _⟩ => exact h1 | ⟨2, _⟩ => exact h2
          · match idx with | ⟨0, _⟩ => exact h3 | ⟨1, _⟩ => exact h4 | ⟨2, _⟩ => exact h5
        refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
        · simpa [assign6_out] using hall (spec.out 0)
        · simpa [assign6_out] using hall (spec.out 1)
        · simpa [assign6_out] using hall (spec.out 2)
        · simpa [assign6_int] using hall (spec.intTerm 0)
        · simpa [assign6_int] using hall (spec.intTerm 1)
        · simpa [assign6_int] using hall (spec.intTerm 2)
      · rintro ⟨⟨⟨⟨⟨ho0, ho1⟩, ho2⟩, hd0⟩, hd1⟩, hd2⟩
        have hall : ∀ p : Bool × Fin 3, val6 p = assign6 spec o0 o1 o2 d0 d1 d2 p := by
          intro p
          rcases spec.cover_all p with ⟨i, rfl⟩ | ⟨j, rfl⟩
          · match i with
            | ⟨0, _⟩ => simpa [assign6_out] using ho0
            | ⟨1, _⟩ => simpa [assign6_out] using ho1
            | ⟨2, _⟩ => simpa [assign6_out] using ho2
          · match j with
            | ⟨0, _⟩ => simpa [assign6_int] using hd0
            | ⟨1, _⟩ => simpa [assign6_int] using hd1
            | ⟨2, _⟩ => simpa [assign6_int] using hd2
        exact ⟨⟨⟨⟨⟨hall (false, 0), hall (false, 1)⟩, hall (false, 2)⟩,
                  hall (true, 0)⟩, hall (true, 1)⟩, hall (true, 2)⟩
    rw [isProperColoring_glue_iff, hterm_eq 0, hterm_eq 1, hterm_eq 2]
    have hpoint : ∀ d0 d1 d2,
        (if bridgesProper spec (assign6 spec o0 o1 o2 d0 d1 d2) &&
            (isProperColoring L.graph cL &&
              (cL (L.t 0) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 0)) &&
              (cL (L.t 1) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 1)) &&
              (cL (L.t 2) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 2))) &&
            (isProperColoring R.graph cR &&
              (cR (R.t 0) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 0)) &&
              (cR (R.t 1) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 1)) &&
              (cR (R.t 2) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 2)))
         then 1 else 0) =
        (if val6 (spec.intTerm 0) == d0 then
           if val6 (spec.intTerm 1) == d1 then
             if val6 (spec.intTerm 2) == d2 then
               if isProperColoring L.graph cL && isProperColoring R.graph cR && bridgesProper spec val6 &&
                  (val6 (spec.out 0) == o0) && (val6 (spec.out 1) == o1) && (val6 (spec.out 2) == o2)
               then 1 else 0
             else 0
           else 0
         else 0) := by
      intro d0 d1 d2
      by_cases hcond :
          ((val6 (spec.out 0) == o0) && (val6 (spec.out 1) == o1) && (val6 (spec.out 2) == o2) &&
           (val6 (spec.intTerm 0) == d0) && (val6 (spec.intTerm 1) == d1) && (val6 (spec.intTerm 2) == d2)) = true
      · have h6 : ((cL (L.t 0) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 0)) &&
                   (cL (L.t 1) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 1)) &&
                   (cL (L.t 2) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 2)) &&
                   (cR (R.t 0) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 0)) &&
                   (cR (R.t 1) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 1)) &&
                   (cR (R.t 2) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 2))) = true := by
          rw [hmatch6]; exact hcond
        have heq_fn : assign6 spec o0 o1 o2 d0 d1 d2 = val6 := by
          funext p
          simp only [Bool.and_eq_true, beq_iff_eq] at h6
          rcases h6 with ⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩
          rcases p with ⟨b, idx⟩
          cases b
          · match idx with | ⟨0, _⟩ => exact e0.symm | ⟨1, _⟩ => exact e1.symm | ⟨2, _⟩ => exact e2.symm
          · match idx with | ⟨0, _⟩ => exact e3.symm | ⟨1, _⟩ => exact e4.symm | ⟨2, _⟩ => exact e5.symm
        rw [heq_fn] at h6 ⊢
        simp only [Bool.and_eq_true] at h6 hcond
        simp [h6, hcond]
        congr 1; grind
      · have hcondF : ((val6 (spec.out 0) == o0) && (val6 (spec.out 1) == o1) && (val6 (spec.out 2) == o2) &&
                       (val6 (spec.intTerm 0) == d0) && (val6 (spec.intTerm 1) == d1) && (val6 (spec.intTerm 2) == d2)) = false :=
          Bool.eq_false_iff.mpr hcond
        have h6F : ((cL (L.t 0) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 0)) &&
                    (cL (L.t 1) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 1)) &&
                    (cL (L.t 2) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 2)) &&
                    (cR (R.t 0) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 0)) &&
                    (cR (R.t 1) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 1)) &&
                    (cR (R.t 2) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 2))) = false := by
          rw [hmatch6]; exact hcondF
        have hL0 : (bridgesProper spec (assign6 spec o0 o1 o2 d0 d1 d2) &&
            (isProperColoring L.graph cL &&
              (cL (L.t 0) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 0)) &&
              (cL (L.t 1) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 1)) &&
              (cL (L.t 2) == assign6 spec o0 o1 o2 d0 d1 d2 (false, 2))) &&
            (isProperColoring R.graph cR &&
              (cR (R.t 0) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 0)) &&
              (cR (R.t 1) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 1)) &&
              (cR (R.t 2) == assign6 spec o0 o1 o2 d0 d1 d2 (true, 2)))) = false := by
          cases bridgesProper spec (assign6 spec o0 o1 o2 d0 d1 d2) <;>
          cases isProperColoring L.graph cL <;> cases isProperColoring R.graph cR <;>
          simp only [Bool.false_and, Bool.true_and, Bool.and_false] <;>
          (try rfl)
          · simpa [Bool.and_assoc] using h6F
        rw [hL0]
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases h0 : (val6 (spec.intTerm 0) == d0) <;>
        cases h1 : (val6 (spec.intTerm 1) == d1) <;>
        cases h2 : (val6 (spec.intTerm 2) == d2) <;>
        simp [h0, h1, h2] at hcondF ⊢
        cases isProperColoring L.graph cL <;> cases isProperColoring R.graph cR <;>
        cases bridgesProper spec val6 <;> simp
        exact hcondF
    rw [sumFin_congr (fun d0 => sumFin_congr (fun d1 => sumFin_congr (fun d2 => hpoint d0 d1 d2)))]
    have h1 : ∀ (x : Fin q) (f : Fin q → Nat), sumFin q (fun d => if x == d then f d else 0) = f x := by
      intro x f
      have hInt := sumFinInt_single q x (f x : Int)
      have hcast : (sumFin q (fun d => if x == d then f d else 0) : Int) =
                   sumFinInt q (fun d => if d = x then (f x : Int) else 0) := by
        rw [sumFinInt_ofNat]
        apply sumFinInt_congr; intro d
        by_cases hdx : d = x
        · subst hdx; simp
        · have hne : (x == d) = false := beq_false_of_ne (Ne.symm hdx)
          simp [hdx, hne]
      omega
    have hzero_if : ∀ (b : Bool) (g : Fin q → Nat),
        sumFin q (fun d => if b then g d else 0) = if b then sumFin q g else 0 := by
      intro b g; cases b <;> simp [sumFin_zero_fn]
    simp only [hzero_if, h1]
    rfl
  rw [htriple, sumFinInt_ofNat]
  simp only [sumFinInt_ofNat]
  have hpal_exists : ∃ (xs : List (Fin q)),
      xs.Nodup ∧
      xs.length = (canonicalRep (pat3 o0 o1 o2)).2.2.2 ∧
      (∃ h0 : (canonicalRep (pat3 o0 o1 o2)).1 < xs.length, xs[(canonicalRep (pat3 o0 o1 o2)).1]'h0 = o0) ∧
      (∃ h1 : (canonicalRep (pat3 o0 o1 o2)).2.1 < xs.length, xs[(canonicalRep (pat3 o0 o1 o2)).2.1]'h1 = o1) ∧
      (∃ h2 : (canonicalRep (pat3 o0 o1 o2)).2.2.1 < xs.length, xs[(canonicalRep (pat3 o0 o1 o2)).2.2.1]'h2 = o2) := by
    unfold pat3
    by_cases h01 : o0 = o1
    · subst h01
      by_cases h12 : o0 = o2
      · subst h12
        simp only [↓reduceIte, canonicalRep]
        exact ⟨[o0], by simp, rfl, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩⟩
      · simp only [↓reduceIte, h12, canonicalRep]
        exact ⟨[o0, o2], by simp [h12], rfl, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩⟩
    · by_cases h02 : o0 = o2
      · subst h02
        simp only [h01, ↓reduceIte, canonicalRep]
        exact ⟨[o0, o1], by simp [h01], rfl, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩⟩
      · by_cases h12 : o1 = o2
        · subst h12
          simp only [h01, ↓reduceIte, canonicalRep]
          exact ⟨[o1, o0], by simp [Ne.symm h01], rfl, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩⟩
        · simp only [h01, h02, h12, ↓reduceIte, canonicalRep]
          exact ⟨[o0, o1, o2], by simp [h01, h02, h12], rfl, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩⟩
  rcases hpal_exists with ⟨xs, hxs_nd, hxs_len, ⟨ho0_lt, ho0_eq⟩, ⟨ho1_lt, ho1_eq⟩, ⟨ho2_lt, ho2_eq⟩⟩
  unfold stepChromPoly
  dsimp only
  rw [← hxs_len]
  change sumColoringsList q 3 (fun ys => match ys with
    | [d0, d1, d2] =>
      let col := assign6 spec o0 o1 o2 d0 d1 d2
      ((if bridgesProper spec col then
          chromFixed L q (col (false, 0)) (col (false, 1)) (col (false, 2)) *
          chromFixed R q (col (true, 0))  (col (true, 1))  (col (true, 2))
        else 0 : Nat) : Int)
    | _ => 0) = _
  apply sumChoicePoly_sound q 3 xs hxs_nd
  intro ys ls hylen hm
  rcases matchesPalette_to_env hxs_nd hm with ⟨pal, hlen, hpal_nd, hxs_pal, hys_pal⟩
  cases ys with
  | nil => simp at hylen
  | cons d0 r0 => cases r0 with
    | nil => simp at hylen
    | cons d1 r1 => cases r1 with
      | nil => simp at hylen
      | cons d2 r2 => cases r2 with
        | cons _ _ => simp at hylen
        | nil =>
          cases ls with
          | nil => simp at hlen
          | cons l0 s0 => cases s0 with
            | nil => simp at hlen
            | cons l1 s1 => cases s1 with
              | nil => simp at hlen
              | cons l2 s2 => cases s2 with
                | cons _ _ => simp at hlen
                | nil =>
                  dsimp only
                  let rep := canonicalRep (pat3 o0 o1 o2)
                  let colC := assign6 spec o0 o1 o2 d0 d1 d2
                  let colS := assign6 spec rep.1 rep.2.1 rep.2.2.1 l0 l1 l2
                  -- Every `colC p` equals `pal[colS p]`!
                  have hcol_pal : ∀ p : Bool × Fin 3,
                      ∃ h : colS p < pal.length, pal[colS p]'h = colC p := by
                    intro p
                    unfold colS colC assign6
                    rcases hxs_pal rep.1 ho0_lt with ⟨hp0, heqp0⟩
                    rcases hxs_pal rep.2.1 ho1_lt with ⟨hp1, heqp1⟩
                    rcases hxs_pal rep.2.2.1 ho2_lt with ⟨hp2, heqp2⟩
                    rcases hys_pal 0 (by simp) with ⟨hd0, heqd0⟩
                    rcases hys_pal 1 (by simp) with ⟨hd1, heqd1⟩
                    rcases hys_pal 2 (by simp) with ⟨hd2, heqd2⟩
                    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heqd0 heqd1 heqd2
                    split
                    · exact ⟨hp0, by rw [heqp0, ho0_eq]⟩
                    · split
                      · exact ⟨hp1, by rw [heqp1, ho1_eq]⟩
                      · split
                        · exact ⟨hp2, by rw [heqp2, ho2_eq]⟩
                        · split
                          · exact ⟨hd0, heqd0⟩
                          · split
                            · exact ⟨hd1, heqd1⟩
                            · exact ⟨hd2, heqd2⟩
                  have heq_col : ∀ p1 p2, colC p1 = colC p2 ↔ colS p1 = colS p2 := by
                    intro p1 p2
                    rcases hcol_pal p1 with ⟨h1, e1⟩
                    rcases hcol_pal p2 with ⟨h2, e2⟩
                    rw [← e1, ← e2]
                    exact nodup_getElem_eq_iff hpal_nd h1 h2
                  have hbr_eq : bridgesProper spec colC = bridgesProper spec colS := by
                    apply Bool.eq_iff_iff.mpr
                    simp only [bridgesProper, decide_eq_true_eq]
                    constructor <;> intro h i j hbr hcontra
                    · exact h i j hbr ((heq_col _ _).mpr hcontra)
                    · exact h i j hbr ((heq_col _ _).mp hcontra)
                  have hpatL : pat3 (colC (false, 0)) (colC (false, 1)) (colC (false, 2)) =
                               pat3 (colS (false, 0)) (colS (false, 1)) (colS (false, 2)) :=
                    pat3_congr (heq_col _ _) (heq_col _ _) (heq_col _ _)
                  have hpatR : pat3 (colC (true, 0)) (colC (true, 1)) (colC (true, 2)) =
                               pat3 (colS (true, 0)) (colS (true, 1)) (colS (true, 2)) :=
                    pat3_congr (heq_col _ _) (heq_col _ _) (heq_col _ _)
                  rw [hbr_eq]
                  cases bridgesProper spec colS
                  · simp [pEval]
                  · simp only [↓reduceIte, Int.natCast_mul, pEval_mul]
                    change (chromFixed L q (colC (false, 0)) (colC (false, 1)) (colC (false, 2)) : Int) *
                           (chromFixed R q (colC (true, 0))  (colC (true, 1))  (colC (true, 2)) : Int) =
                           pEval (vL (pat3 (colS (false, 0)) (colS (false, 1)) (colS (false, 2)))) (q : Int) *
                           pEval (vR (pat3 (colS (true, 0))  (colS (true, 1))  (colS (true, 2)))) (q : Int)
                    rw [hvL, hvR, hpatL, hpatR]


-- ============================================================================
-- SECTION 4: Pure-Silicon Bit-Graph `GB_k` & Exact Bit-MSB Gluing Theorem
-- ============================================================================

theorem gray_lt {k i : Nat} (hi : i < 2 ^ k) : gray i < 2 ^ k := by
  unfold gray
  apply Nat.xor_lt_two_pow hi
  rw [Nat.shiftRight_eq_div_pow]
  have : 2 ^ 1 = 2 := rfl
  omega

theorem testBit_pow_add {k a b : Nat} (ha : a < 2 ^ k) :
    (2 ^ k + a).testBit b =
      if b < k then a.testBit b else if b == k then true else false := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  by_cases hlt : b < k
  · simp only [hlt, ↓reduceIte]
    have hpow : 2 ^ k = 2 ^ b * 2 ^ (k - b) := by rw [← Nat.pow_add]; congr 1; omega
    have h2 : 2 ∣ 2 ^ (k - b) := by
      have hpos : k - b ≥ 1 := by omega
      have : 2 ^ (k - b) = 2 * 2 ^ (k - b - 1) := by
        conv => lhs; rw [show k - b = (k - b - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      rw [this]; exact Nat.dvd_mul_right 2 _
    rw [hpow, Nat.mul_add_div (Nat.two_pow_pos b)]
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rcases h2 with ⟨m, hm⟩
    rw [hm, show 2 * m + a / 2 ^ b = a / 2 ^ b + 2 * m by omega]
    simp [Nat.add_mul_mod_self_left]
  · by_cases heq : b = k
    · subst heq
      simp only [Nat.lt_irrefl, ↓reduceIte, beq_self_eq_true]
      have hdiv : (2 ^ b + a) / 2 ^ b = 1 := by
        have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
        have h1 : 2 ^ b + a = 2 ^ b * 1 + a := by omega
        rw [h1, Nat.mul_add_div hpos, Nat.div_eq_of_lt ha]
      rw [hdiv]; rfl
    · have hgt : k < b := by omega
      have hne : (b == k) = false := beq_false_of_ne heq
      simp only [hlt, hne, ↓reduceIte, Bool.false_eq_true]
      have hle : 2 ^ (k + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
      have hlt2 : 2 ^ k + a < 2 ^ b := by
        have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
        omega
      rw [Nat.div_eq_of_lt hlt2]; rfl

theorem testBit_sub_mask {k j b : Nat} (hj : j < 2 ^ k) :
    (2 ^ k - 1 - j).testBit b = if b < k then !(j.testBit b) else false := by
  by_cases hlt : b < k
  · simp only [hlt, ↓reduceIte]
    induction k generalizing j b with
    | zero => omega
    | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      cases b with
      | zero =>
        simp only [Nat.testBit_zero]
        have hpos : 2 ^ k ≥ 1 := Nat.two_pow_pos k
        have hmod : (2 ^ (k + 1) - 1 - j) % 2 = 1 - j % 2 := by omega
        rw [hmod]
        have hlt2 : j % 2 = 0 ∨ j % 2 = 1 := by omega
        rcases hlt2 with h0 | h0 <;> simp [h0]
      | succ b' =>
        rw [Nat.testBit_succ, Nat.testBit_succ]
        have hdiv : (2 ^ (k + 1) - 1 - j) / 2 = 2 ^ k - 1 - j / 2 := by
          have : 2 ^ k ≥ 1 := Nat.two_pow_pos k
          omega
        rw [hdiv]
        exact ih (by omega) (by omega)
  · simp only [hlt, ↓reduceIte]
    have hlt2 : 2 ^ k - 1 - j < 2 ^ b := by
      have : 2 ^ k ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 ^ k ≥ 1 := Nat.two_pow_pos k
      omega
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt2]; rfl

/-- **Pure-Silicon Gray Reflection Law**: `gray (2^k + j) = 2^k + gray (2^k - 1 - j)` for `j < 2^k`. -/
theorem gray_reflect {k j : Nat} (hk : 1 ≤ k) (hj : j < 2 ^ k) :
    gray (2 ^ k + j) = 2 ^ k + gray (2 ^ k - 1 - j) := by
  apply Nat.eq_of_testBit_eq
  intro b
  have hsub_lt : 2 ^ k - 1 - j < 2 ^ k := by have := Nat.two_pow_pos k; omega
  have hgsub_lt : gray (2 ^ k - 1 - j) < 2 ^ k := gray_lt hsub_lt
  rw [testBit_pow_add hgsub_lt]
  simp only [gray, Nat.testBit_xor, Nat.testBit_shiftRight, show 1 + b = b + 1 by omega,
             testBit_pow_add hj, testBit_sub_mask hj]
  by_cases hgt : k < b
  · have h1 : ¬ (b < k) := by omega
    have h2 : ¬ (b + 1 < k) := by omega
    have h3 : (b == k) = false := beq_false_of_ne (by omega)
    have h4 : (b + 1 == k) = false := beq_false_of_ne (by omega)
    simp [h1, h2, h3, h4]
  · by_cases heq : b = k
    · subst heq
      have h1 : ¬ (b < b) := by omega
      have h2 : ¬ (b + 1 < b) := by omega
      have h4 : (b + 1 == b) = false := beq_false_of_ne (by omega)
      simp [h1, h2, h4]
    · have hlt : b < k := by omega
      by_cases htop : b + 1 = k
      · have h2 : ¬ (b + 1 < k) := by omega
        have h4 : (b + 1 == k) = true := beq_iff_eq.mpr htop
        simp only [hlt, h2, h4, ↓reduceIte, Bool.xor_true, Bool.xor_false]
      · have h2 : b + 1 < k := by omega
        simp only [hlt, h2, ↓reduceIte]
        cases j.testBit b <;> cases j.testBit (b + 1) <;> rfl

/-- **Pure-Silicon Gray Seam Law (Left)**: `gray (2^k - 1) = 2^(k - 1)` for `k ≥ 1`. -/
theorem gray_seam_left {k : Nat} (hk : 1 ≤ k) :
    gray (2 ^ k - 1) = 2 ^ (k - 1) := by
  apply Nat.eq_of_testBit_eq
  intro b
  have h0 : 0 < 2 ^ k := Nat.two_pow_pos k
  have hsub : 2 ^ k - 1 = 2 ^ k - 1 - 0 := by omega
  rw [gray, Nat.testBit_xor, Nat.testBit_shiftRight, show 1 + b = b + 1 by omega,
      hsub, testBit_sub_mask h0, testBit_sub_mask h0, Nat.testBit_two_pow]
  have hzero : ∀ m, (0 : Nat).testBit m = false := fun m => by simp
  simp only [hzero, Bool.not_false]
  by_cases h1 : b < k
  · by_cases h2 : b + 1 < k
    · simp [h1, h2]; omega
    · have heq : k - 1 = b := by omega
      simp [h1, h2, heq]
  · have h2 : ¬ (b + 1 < k) := by omega
    simp [h1, h2]; omega

/-- **Pure-Silicon Gray Seam Law (Right)**: `gray (2^k) = 2^k + 2^(k - 1)` for `k ≥ 1`. -/
theorem gray_seam_right {k : Nat} (hk : 1 ≤ k) :
    gray (2 ^ k) = 2 ^ k + 2 ^ (k - 1) := by
  have h := gray_reflect hk (Nat.two_pow_pos k)
  simpa [Nat.add_zero, Nat.sub_zero, gray_seam_left hk] using h

theorem gray_zero : gray 0 = 0 := rfl

/-- **EXACT BIT-MSB GLUING DECOMPOSITION THEOREM FOR `GB_k` (`∀ k ≥ 2`)**:
    Splitting `GB_{k+1}` along the MSB into `{0, ..., 2^k - 1}` and `{2^k, ..., 2^(k+1) - 1}`
    yields `glue gbSpec (gbGraph k) (gbGraph k)` identically! -/
theorem gbAdj_msb_split {k : Nat} (hk : 2 ≤ k) (u v : Fin (2 ^ k + 2 ^ k)) :
    gbAdj (k + 1) u.val v.val = glueAdj gbSpec (gbGraph k hk) (gbGraph k hk) u v := by
  have hk1 : 1 ≤ k := by omega
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h2ge4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  apply Bool.eq_iff_iff.mpr
  simp only [gbAdj, binAdj, grayAdj, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  have hgray_split : ∀ a b : Nat,
      (∃ i : Fin (2 ^ (k + 1) - 1),
        (gray i.val = a ∧ gray (i.val + 1) = b) ∨ (gray i.val = b ∧ gray (i.val + 1) = a)) ↔
      ((∃ i : Fin (2 ^ k - 1),
          (gray i.val = a ∧ gray (i.val + 1) = b) ∨ (gray i.val = b ∧ gray (i.val + 1) = a)) ∨
       ((a = 2 ^ (k - 1) ∧ b = 2 ^ k + 2 ^ (k - 1)) ∨ (b = 2 ^ (k - 1) ∧ a = 2 ^ k + 2 ^ (k - 1))) ∨
       (2 ^ k ≤ a ∧ 2 ^ k ≤ b ∧
        ∃ i : Fin (2 ^ k - 1),
          (gray i.val = a - 2 ^ k ∧ gray (i.val + 1) = b - 2 ^ k) ∨
          (gray i.val = b - 2 ^ k ∧ gray (i.val + 1) = a - 2 ^ k))) := by
    intro a b
    constructor
    · rintro ⟨⟨i, hi⟩, hpair⟩
      dsimp only at hpair
      by_cases hlt : i < 2 ^ k - 1
      · left; exact ⟨⟨i, hlt⟩, hpair⟩
      · by_cases hseam : i = 2 ^ k - 1
        · right; left
          have h1 : i + 1 = 2 ^ k := by omega
          rw [h1, hseam, gray_seam_left hk1, gray_seam_right hk1] at hpair
          rcases hpair with ⟨ha, hb⟩ | ⟨hb, ha⟩
          · exact Or.inl ⟨ha.symm, hb.symm⟩
          · exact Or.inr ⟨hb.symm, ha.symm⟩
        · right; right
          let j := i - 2 ^ k
          have hj1 : j + 1 < 2 ^ k := by omega
          have hi_eq : i = 2 ^ k + j := by omega
          have hi1_eq : i + 1 = 2 ^ k + (j + 1) := by omega
          rw [hi1_eq, hi_eq, gray_reflect hk1 (by omega), gray_reflect hk1 hj1] at hpair
          let i' := 2 ^ k - 2 - j
          have hi'_lt : i' < 2 ^ k - 1 := by omega
          have hsub1 : 2 ^ k - 1 - (j + 1) = i' := by omega
          have hsub2 : 2 ^ k - 1 - j = i' + 1 := by omega
          rw [hsub1, hsub2] at hpair
          rcases hpair with ⟨ha, hb⟩ | ⟨hb, ha⟩
          · refine ⟨by omega, by omega, ⟨i', hi'_lt⟩, Or.inr ⟨?_, ?_⟩⟩
            · dsimp only; omega
            · dsimp only; omega
          · refine ⟨by omega, by omega, ⟨i', hi'_lt⟩, Or.inl ⟨?_, ?_⟩⟩
            · dsimp only; omega
            · dsimp only; omega
    · rintro (⟨⟨i, hi⟩, hpair⟩ | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨ha, hb, ⟨i', hi'⟩, hpair⟩)
      · exact ⟨⟨i, by omega⟩, hpair⟩
      · refine ⟨⟨2 ^ k - 1, by omega⟩, Or.inl ?_⟩
        rw [gray_seam_left hk1, show 2 ^ k - 1 + 1 = 2 ^ k by omega, gray_seam_right hk1]
        exact ⟨rfl, rfl⟩
      · refine ⟨⟨2 ^ k - 1, by omega⟩, Or.inr ?_⟩
        rw [gray_seam_left hk1, show 2 ^ k - 1 + 1 = 2 ^ k by omega, gray_seam_right hk1]
        exact ⟨rfl, rfl⟩
      · let j := 2 ^ k - 2 - i'
        have hj1 : j + 1 < 2 ^ k := by omega
        refine ⟨⟨2 ^ k + j, by omega⟩, ?_⟩
        dsimp only at hpair ⊢
        have h1 : 2 ^ k + j + 1 = 2 ^ k + (j + 1) := by omega
        rw [h1, gray_reflect hk1 (by omega), gray_reflect hk1 hj1]
        have hs1 : 2 ^ k - 1 - j = i' + 1 := by omega
        have hs2 : 2 ^ k - 1 - (j + 1) = i' := by omega
        rw [hs1, hs2]
        rcases hpair with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · exact Or.inr ⟨by omega, by omega⟩
        · exact Or.inl ⟨by omega, by omega⟩
  rw [hgray_split]
  unfold glueAdj
  by_cases hu : u.val < 2 ^ k <;> by_cases hv : v.val < 2 ^ k
  · -- Both in Left half
    simp only [hu, hv, ↓reduceDIte, gbGraph, gbAdj, binAdj, grayAdj, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro (hbin | (hgL | (⟨_, hb⟩ | ⟨ha, _⟩) | ⟨ha, _, _⟩))
      · exact Or.inl hbin
      · exact Or.inr hgL
      · omega
      · omega
      · omega
    · rintro (hbin | hgL)
      · exact Or.inl hbin
      · exact Or.inr (Or.inl hgL)
  · -- u in Left half, v in Right half
    simp only [hu, hv, ↓reduceDIte, hasBridge, decide_eq_true_eq]
    have hbr_iff :
        (∃ i j : Fin 3, ⟨u.val, hu⟩ = (gbGraph k hk).t i ∧ ⟨v.val - 2 ^ k, by omega⟩ = (gbGraph k hk).t j ∧ gbSpec.bridges i j = true) ↔
        ((u.val = 2 ^ k - 1 ∧ v.val = 2 ^ k) ∨ (u.val = 2 ^ (k - 1) ∧ v.val = 2 ^ k + 2 ^ (k - 1))) := by
      constructor
      · rintro ⟨i, j, hui, hvj, hbr⟩
        have hui' := congrArg Fin.val hui
        have hvj' := congrArg Fin.val hvj
        match i, j with
        | ⟨2, _⟩, ⟨0, _⟩ => left; simp [gbGraph] at hui' hvj'; omega
        | ⟨1, _⟩, ⟨1, _⟩ => right; simp [gbGraph] at hui' hvj'; omega
        | ⟨0, _⟩, ⟨0, _⟩ => simp [gbSpec] at hbr
        | ⟨0, _⟩, ⟨1, _⟩ => simp [gbSpec] at hbr
        | ⟨0, _⟩, ⟨2, _⟩ => simp [gbSpec] at hbr
        | ⟨1, _⟩, ⟨0, _⟩ => simp [gbSpec] at hbr
        | ⟨1, _⟩, ⟨2, _⟩ => simp [gbSpec] at hbr
        | ⟨2, _⟩, ⟨1, _⟩ => simp [gbSpec] at hbr
        | ⟨2, _⟩, ⟨2, _⟩ => simp [gbSpec] at hbr
      · rintro (⟨hu1, hv1⟩ | ⟨hu2, hv2⟩)
        · exact ⟨2, 0, Fin.ext (by simp [gbGraph, hu1]), Fin.ext (by simp [gbGraph]; omega), by decide⟩
        · exact ⟨1, 1, Fin.ext (by simp [gbGraph, hu2]), Fin.ext (by simp [gbGraph]; omega), by decide⟩
    rw [hbr_iff]
    constructor
    · rintro ((h1 | h2) | (⟨i, ⟨_, hb⟩ | ⟨ha, _⟩⟩ | (hseam | ⟨hb, _⟩) | ⟨ha, _, _⟩))
      · left; omega
      · omega
      · have := gray_lt (k := k) (i := i.val + 1) (by omega); omega
      · have := gray_lt (k := k) (i := i.val) (by omega); omega
      · right; exact hseam
      · omega
      · omega
    · rintro (⟨hu1, hv1⟩ | hseam)
      · left; left; omega
      · right; right; left; exact Or.inl hseam
  · -- u in Right half, v in Left half (symmetric)
    simp only [hu, hv, ↓reduceDIte, hasBridge, decide_eq_true_eq]
    have hbr_iff :
        (∃ i j : Fin 3, ⟨v.val, hv⟩ = (gbGraph k hk).t i ∧ ⟨u.val - 2 ^ k, by omega⟩ = (gbGraph k hk).t j ∧ gbSpec.bridges i j = true) ↔
        ((v.val = 2 ^ k - 1 ∧ u.val = 2 ^ k) ∨ (v.val = 2 ^ (k - 1) ∧ u.val = 2 ^ k + 2 ^ (k - 1))) := by
      constructor
      · rintro ⟨i, j, hvi, huj, hbr⟩
        have hvi' := congrArg Fin.val hvi
        have huj' := congrArg Fin.val huj
        match i, j with
        | ⟨2, _⟩, ⟨0, _⟩ => left; simp [gbGraph] at hvi' huj'; omega
        | ⟨1, _⟩, ⟨1, _⟩ => right; simp [gbGraph] at hvi' huj'; omega
        | ⟨0, _⟩, ⟨0, _⟩ => simp [gbSpec] at hbr
        | ⟨0, _⟩, ⟨1, _⟩ => simp [gbSpec] at hbr
        | ⟨0, _⟩, ⟨2, _⟩ => simp [gbSpec] at hbr
        | ⟨1, _⟩, ⟨0, _⟩ => simp [gbSpec] at hbr
        | ⟨1, _⟩, ⟨2, _⟩ => simp [gbSpec] at hbr
        | ⟨2, _⟩, ⟨1, _⟩ => simp [gbSpec] at hbr
        | ⟨2, _⟩, ⟨2, _⟩ => simp [gbSpec] at hbr
      · rintro (⟨hv1, hu1⟩ | ⟨hv2, hu2⟩)
        · exact ⟨2, 0, Fin.ext (by simp [gbGraph, hv1]), Fin.ext (by simp [gbGraph]; omega), by decide⟩
        · exact ⟨1, 1, Fin.ext (by simp [gbGraph, hv2]), Fin.ext (by simp [gbGraph]; omega), by decide⟩
    rw [hbr_iff]
    constructor
    · rintro ((h1 | h2) | (⟨i, ⟨ha, _⟩ | ⟨_, hb⟩⟩ | (⟨ha, _⟩ | hseam) | ⟨_, hb, _⟩))
      · omega
      · left; omega
      · have := gray_lt (k := k) (i := i.val) (by omega); omega
      · have := gray_lt (k := k) (i := i.val + 1) (by omega); omega
      · omega
      · right; exact hseam
      · omega
    · rintro (⟨hv1, hu1⟩ | hseam)
      · left; right; omega
      · right; right; left; exact Or.inr hseam
  · -- Both in Right half
    simp only [hu, hv, ↓reduceDIte, gbGraph, gbAdj, binAdj, grayAdj, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ((h1 | h2) | (⟨i, ⟨ha, _⟩ | ⟨_, hb⟩⟩ | (⟨ha, _⟩ | ⟨hb, _⟩) | ⟨_, _, hgR⟩))
      · left; left; omega
      · left; right; omega
      · have := gray_lt (k := k) (i := i.val) (by omega); omega
      · have := gray_lt (k := k) (i := i.val + 1) (by omega); omega
      · have : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by omega); omega
      · have : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by omega); omega
      · exact Or.inr hgR
    · rintro ((h1 | h2) | hgR)
      · left; left; omega
      · left; right; omega
      · right; right; right; exact ⟨by omega, by omega, hgR⟩

theorem castTermGraph_alphaVec {n1 n2 : Nat} (h : n1 = n2) (G : TermGraph n1) (s : Fin 8) :
    alphaVec (castTermGraph h G) s = alphaVec G s := by subst h; rfl

theorem castTermGraph_pmVec {n1 n2 : Nat} (h : n1 = n2) (G : TermGraph n1) (s : Fin 8) :
    pmVec (castTermGraph h G) s = pmVec G s := by subst h; rfl

theorem castTermGraph_hasChromVec {n1 n2 : Nat} (h : n1 = n2) (G : TermGraph n1) (v : Fin 5 → Poly) :
    HasChromVec (castTermGraph h G) v ↔ HasChromVec G v := by subst h; exact Iff.rfl

theorem finGraph_ext {n : Nat} {G1 G2 : FinGraph n} (h : ∀ u v, G1.adj u v = G2.adj u v) :
    G1 = G2 := by
  cases G1; cases G2; congr; funext u v; exact h u v

theorem termGraph_ext {n : Nat} {G1 G2 : TermGraph n}
    (hadj : ∀ u v, G1.graph.adj u v = G2.graph.adj u v)
    (ht : ∀ i : Fin 3, G1.t i = G2.t i) :
    G1 = G2 := by
  cases G1; cases G2
  have hg := finGraph_ext hadj
  have htf : _ = _ := funext ht
  congr

/-- **Exact Structural Identity**: `castTermGraph (2^(k+1) = 2^k + 2^k) (gbGraph (k+1)) = glue gbSpec (gbGraph k) (gbGraph k)`! -/
theorem gbGraph_succ_eq_glue {k : Nat} (hk : 2 ≤ k) :
    castTermGraph (show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by rw [Nat.pow_succ]; omega) (gbGraph (k + 1) (by omega)) =
    glue gbSpec (gbGraph k hk) (gbGraph k hk) := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  apply termGraph_ext
  · intro u v
    have hcast_adj : (castTermGraph hpow (gbGraph (k + 1) (by omega))).graph.adj u v = gbAdj (k + 1) u.val v.val := by
      unfold castTermGraph
      have h : ∀ (m : Nat) (hm : 2 ^ (k + 1) = m) (a b : Fin m),
          ((hm ▸ gbGraph (k + 1) (by omega)) : TermGraph m).graph.adj a b = gbAdj (k + 1) a.val b.val := by
        intro m hm a b; subst hm; rfl
      exact h _ hpow u v
    rw [hcast_adj]
    exact gbAdj_msb_split hk u v
  · intro i
    have hcast_t : (castTermGraph hpow (gbGraph (k + 1) (by omega))).t i =
        ⟨((gbGraph (k + 1) (by omega)).t i).val, by omega⟩ := by
      have h : ∀ (m : Nat) (hm : 2 ^ (k + 1) = m),
          ((hm ▸ gbGraph (k + 1) (by omega)) : TermGraph m).t i =
          ⟨((gbGraph (k + 1) (by omega)).t i).val, by omega⟩ := by
        intro m hm; subst hm; rfl
      exact h _ hpow
    rw [hcast_t]
    apply Fin.ext
    match i with
    | ⟨0, _⟩ => simp [gbGraph, glue, gbSpec, glueTerm, leftEmbed]
    | ⟨1, _⟩ => simp [gbGraph, glue, gbSpec, glueTerm, rightEmbed]
    | ⟨2, _⟩ => simp [gbGraph, glue, gbSpec, glueTerm, rightEmbed]; omega

/-- Lifting corollaries for `gbGraph`: `alphaVec`, `pmVec`, and `HasChromVec` obey `gbSpec` ∀ `k ≥ 2`! -/
theorem gbGraph_alphaVec_succ {k : Nat} (hk : 2 ≤ k) (s : Fin 8) :
    alphaVec (gbGraph (k + 1) (by omega)) s =
    stepAlpha gbSpec (alphaVec (gbGraph k hk)) (alphaVec (gbGraph k hk)) s := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [← castTermGraph_alphaVec hpow, gbGraph_succ_eq_glue hk, glue_alpha_sound]

theorem gbGraph_pmVec_succ {k : Nat} (hk : 2 ≤ k) (s : Fin 8) :
    pmVec (gbGraph (k + 1) (by omega)) s =
    stepPM gbSpec (pmVec (gbGraph k hk)) (pmVec (gbGraph k hk)) s := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [← castTermGraph_pmVec hpow, gbGraph_succ_eq_glue hk, glue_pm_sound]

theorem gbGraph_hasChromVec_succ {k : Nat} (hk : 2 ≤ k) {v : Fin 5 → Poly}
    (hv : HasChromVec (gbGraph k hk) v) :
    HasChromVec (gbGraph (k + 1) (by omega)) (stepChromPoly gbSpec v v) := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [← castTermGraph_hasChromVec hpow, gbGraph_succ_eq_glue hk]
  exact glue_chrom_sound gbSpec (gbGraph k hk) (gbGraph k hk) hv hv


-- ============================================================================
-- SECTION 5: Five Infinite Theorems on `GB_k` (and 4 Boundary Closures)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- 5A. Theorem 1: Exact Perfect-Matching Quadratic Law (OEIS A000283) + 4 Closures
-- ----------------------------------------------------------------------------

theorem pmSeq_succ_eq (k : Nat) (hk : 2 ≤ k) :
    pmSeq (k + 1) = pmSeq k ^ 2 + pmSeq (k - 1) ^ 2 := by
  match k with
  | 0 | 1 => omega
  | n + 2 => simp [pmSeq]

theorem gbGraph2_pmVec (s : Fin 8) :
    pmVec (gbGraph 2 (by omega)) s = gbPmInv 2 s := by
  revert s; decide

theorem stepPM_eq_coef (spec : GlueSpec) (vL vR : Fin 8 → Nat) (s : Fin 8) :
    stepPM spec vL vR s =
      sumFin8 fun sL => sumFin8 fun sR => bridgePMCoef spec sL sR s * (vL sL * vR sR) := by
  unfold stepPM bridgePMCoef
  apply sumFin8_congr; intro sL
  apply sumFin8_congr; intro sR
  have h : ∀ B, (if bridgePMOk spec sL sR B s then vL sL * vR sR else 0) =
                (if bridgePMOk spec sL sR B s then 1 else 0) * (vL sL * vR sR) := by
    intro B; cases bridgePMOk spec sL sR B s <;> simp
  rw [sumSubsets_congr h, sumSubsets_mul_right]

theorem gbPMCoef_eq_fast : ∀ sL sR s : Fin 8,
    (sL.val == 1 || sL.val == 2 || sL.val == 4 || sL.val == 7) = true →
    (sR.val == 1 || sR.val == 2 || sR.val == 4 || sR.val == 7) = true →
    bridgePMCoef gbSpec sL sR s = gbPMCoefFast sL sR s := by
  decide

theorem stepPM_gbSpec_inv (k : Nat) (hk : 2 ≤ k) (s : Fin 8) :
    stepPM gbSpec (gbPmInv k) (gbPmInv k) s = gbPmInv (k + 1) s := by
  rw [stepPM_eq_coef]
  have hrec := pmSeq_succ_eq k hk
  have hsub : k + 1 - 1 = k := by omega
  have hcongr : ∀ sL sR : Fin 8,
      bridgePMCoef gbSpec sL sR s * (gbPmInv k sL * gbPmInv k sR) =
      gbPMCoefFast sL sR s * (gbPmInv k sL * gbPmInv k sR) := by
    intro sL sR
    by_cases hL : (sL.val == 1 || sL.val == 2 || sL.val == 4 || sL.val == 7) = true
    · by_cases hR : (sR.val == 1 || sR.val == 2 || sR.val == 4 || sR.val == 7) = true
      · rw [gbPMCoef_eq_fast sL sR s hL hR]
      · have hzero : gbPmInv k sR = 0 := by
          match sR with
          | ⟨0, _⟩ | ⟨3, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl
          | ⟨1, _⟩ | ⟨2, _⟩ | ⟨4, _⟩ | ⟨7, _⟩ => simp at hR
        simp [hzero]
    · have hzero : gbPmInv k sL = 0 := by
        match sL with
        | ⟨0, _⟩ | ⟨3, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl
        | ⟨1, _⟩ | ⟨2, _⟩ | ⟨4, _⟩ | ⟨7, _⟩ => simp at hL
      simp [hzero]
  rw [sumFin8_congr (fun sL => sumFin8_congr (fun sR => hcongr sL sR))]
  match s with
  | ⟨0, _⟩ => simp [sumFin8, gbPMCoefFast, gbPmInv]
  | ⟨1, _⟩ => simp [sumFin8, gbPMCoefFast, gbPmInv]
  | ⟨2, _⟩ => simp [sumFin8, gbPMCoefFast, gbPmInv, hrec]; grind
  | ⟨3, _⟩ => simp [sumFin8, gbPMCoefFast, gbPmInv]
  | ⟨4, _⟩ => simp [sumFin8, gbPMCoefFast, gbPmInv, hsub]; grind
  | ⟨5, _⟩ => simp [sumFin8, gbPMCoefFast, gbPmInv]
  | ⟨6, _⟩ => simp [sumFin8, gbPMCoefFast, gbPmInv]
  | ⟨7, _⟩ => simp [sumFin8, gbPMCoefFast, gbPmInv, hrec]; grind

theorem gbGraph_pmVec_eq (k : Nat) (hk : 2 ≤ k) (s : Fin 8) :
    pmVec (gbGraph k hk) s = gbPmInv k s := by
  induction k generalizing s with
  | zero => omega
  | succ k ih =>
    by_cases hk2 : k = 1
    · subst hk2; exact gbGraph2_pmVec s
    · have hkge : 2 ≤ k := by omega
      rw [gbGraph_pmVec_succ hkge]
      have hfun : pmVec (gbGraph k hkge) = gbPmInv k := funext (fun t => ih hkge t)
      rw [hfun]
      exact stepPM_gbSpec_inv k hkge s

/-- **THEOREM 1 (Exact Perfect-Matching Quadratic Law — OEIS A000283)**:
    For all `k ≥ 2`, `exactPM (GB_k) = pmSeq k`, satisfying
    `exactPM (GB_{k+1}) = exactPM (GB_k)^2 + exactPM (GB_{k-1})^2` for all `k ≥ 3`
    (with `exactPM (GB_2) = 1`, `exactPM (GB_3) = 2`). -/
theorem gb_pm_exact (k : Nat) (hk : 2 ≤ k) :
    exactPM (gbGraph k hk).graph = pmSeq k := by
  rw [exactPM_eq_pmVec7, gbGraph_pmVec_eq k hk 7]; rfl

theorem gb_pm_recurrence (k : Nat) (hk : 3 ≤ k) :
    exactPM (gbGraph (k + 1) (by omega)).graph =
    exactPM (gbGraph k (by omega)).graph ^ 2 + exactPM (gbGraph (k - 1) (by omega)).graph ^ 2 := by
  rw [gb_pm_exact (k + 1) (by omega), gb_pm_exact k (by omega), gb_pm_exact (k - 1) (by omega)]
  exact pmSeq_succ_eq k (by omega)

theorem allEdges_addEdge_perm {n : Nat} (G : FinGraph n) (u0 v0 : Fin n)
    (hlt : u0.val < v0.val) (hno : G.adj u0 v0 = false) :
    (allEdges (addEdgeGraph G u0 v0 (fun h => by have := congrArg Fin.val h; omega))).Perm
      ((u0, v0) :: allEdges G) := by
  have hne : u0 ≠ v0 := fun h => by have := congrArg Fin.val h; omega
  have hnotmem : (u0, v0) ∉ allEdges G := by
    intro hm; have := (mem_allEdges.mp hm).2; rw [hno] at this; cases this
  apply perm_of_nodup_iff (allEdges_nodup _) (List.nodup_cons.mpr ⟨hnotmem, allEdges_nodup G⟩)
  intro e
  rcases e with ⟨a, b⟩
  simp only [mem_allEdges, List.mem_cons, addEdgeGraph, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hab, (hadj | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨hab, hadj⟩
    · exact Or.inl rfl
    · omega
  · rintro (heq | ⟨hab, hadj⟩)
    · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact ⟨hlt, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩
    · exact ⟨hab, Or.inl (Or.inl hadj)⟩

/-- Generic exact perfect-matching formula upon adding a boundary edge `(t_i, t_j)` to `G : TermGraph n`. -/
theorem exactPM_addTermEdge {n : Nat} (G : TermGraph n) (i j : Fin 3)
    (hlt : (G.t i).val < (G.t j).val) (hno : G.graph.adj (G.t i) (G.t j) = false)
    (s' : Fin 8) (hs' : ∀ k : Fin 3, fin8Bit s' k = !(k == i || k == j)) :
    exactPM (addEdgeGraph G.graph (G.t i) (G.t j) (fun h => by have := congrArg Fin.val h; omega)) =
    pmVec G 7 + pmVec G s' := by
  have hne : G.t i ≠ G.t j := fun h => by have := congrArg Fin.val h; omega
  unfold exactPM
  have hperm_inv : ∀ s1 s2 : List (Edge n), s1.Perm s2 →
      (if isPerfectMatching s1 then 1 else 0) = (if isPerfectMatching s2 then 1 else 0) := by
    intro s1 s2 hp
    suffices isPerfectMatching s1 = isPerfectMatching s2 by rw [this]
    apply Bool.eq_iff_iff.mpr; simp only [isPerfectMatching, decide_eq_true_eq]
    constructor <;> intro h v
    · rw [← degIn_perm v hp]; exact h v
    · rw [degIn_perm v hp]; exact h v
  rw [sumSubsets_perm hperm_inv (allEdges_addEdge_perm G.graph (G.t i) (G.t j) hlt hno)]
  simp only [sumSubsets]
  rw [← exactPM, exactPM_eq_pmVec7]
  congr 1
  unfold pmVec
  apply sumSubsets_congr; intro M
  suffices isPerfectMatching ((G.t i, G.t j) :: M) = isInternalPM G s' M by rw [this]
  apply Bool.eq_iff_iff.mpr
  simp only [isPerfectMatching, isInternalPM, decide_eq_true_eq]
  constructor
  · intro h v
    have hv := h v
    simp only [degIn] at hv
    unfold targetDeg
    by_cases h0 : v = G.t 0
    · subst h0; simp only [beq_self_eq_true, ↓reduceIte, hs' 0]
      have h0i : (G.t i == G.t 0) = (0 == i) := by
        apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
        exact ⟨fun e => (G.distinct i 0 e).symm, fun e => by rw [← e]⟩
      have h0j : (G.t j == G.t 0) = (0 == j) := by
        apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
        exact ⟨fun e => (G.distinct j 0 e).symm, fun e => by rw [← e]⟩
      rw [h0i, h0j] at hv
      have hij : i ≠ j := fun e => hne (by rw [e])
      match i, j with
      | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl hij
      | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩ | ⟨1, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨0, _⟩ => simp at hv ⊢; omega
      | ⟨1, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ => simp at hv ⊢; omega
    · by_cases h1 : v = G.t 1
      · subst h1; simp only [beq_false_of_ne h0, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, hs' 1]
        have h1i : (G.t i == G.t 1) = (1 == i) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
          exact ⟨fun e => (G.distinct i 1 e).symm, fun e => by rw [← e]⟩
        have h1j : (G.t j == G.t 1) = (1 == j) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
          exact ⟨fun e => (G.distinct j 1 e).symm, fun e => by rw [← e]⟩
        rw [h1i, h1j] at hv
        have hij : i ≠ j := fun e => hne (by rw [e])
        match i, j with
        | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl hij
        | ⟨0, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨1, _⟩ => simp at hv ⊢; omega
        | ⟨0, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨2, _⟩ => simp at hv ⊢; omega
      · by_cases h2 : v = G.t 2
        · subst h2; simp only [beq_false_of_ne h0, beq_false_of_ne h1, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, hs' 2]
          have h2i : (G.t i == G.t 2) = (2 == i) := by
            apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
            exact ⟨fun e => (G.distinct i 2 e).symm, fun e => by rw [← e]⟩
          have h2j : (G.t j == G.t 2) = (2 == j) := by
            apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
            exact ⟨fun e => (G.distinct j 2 e).symm, fun e => by rw [← e]⟩
          rw [h2i, h2j] at hv
          have hij : i ≠ j := fun e => hne (by rw [e])
          match i, j with
          | ⟨2, _⟩, ⟨2, _⟩ => exact absurd rfl hij
          | ⟨0, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨1, _⟩ => simp at hv ⊢; omega
          | ⟨0, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ => simp at hv ⊢; omega
        · have hni : (G.t i == v) = false := beq_false_of_ne (by
            match i with | ⟨0, _⟩ => exact Ne.symm h0 | ⟨1, _⟩ => exact Ne.symm h1 | ⟨2, _⟩ => exact Ne.symm h2)
          have hnj : (G.t j == v) = false := beq_false_of_ne (by
            match j with | ⟨0, _⟩ => exact Ne.symm h0 | ⟨1, _⟩ => exact Ne.symm h1 | ⟨2, _⟩ => exact Ne.symm h2)
          simp only [beq_false_of_ne h0, beq_false_of_ne h1, beq_false_of_ne h2, Bool.false_eq_true, ↓reduceIte]
          simp [hni, hnj] at hv; exact hv
  · intro h v
    simp only [degIn]
    have hv := h v
    unfold targetDeg at hv
    by_cases h0 : v = G.t 0
    · subst h0; simp only [beq_self_eq_true, ↓reduceIte, hs' 0] at hv
      have h0i : (G.t i == G.t 0) = (0 == i) := by
        apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
        exact ⟨fun e => (G.distinct i 0 e).symm, fun e => by rw [← e]⟩
      have h0j : (G.t j == G.t 0) = (0 == j) := by
        apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
        exact ⟨fun e => (G.distinct j 0 e).symm, fun e => by rw [← e]⟩
      rw [h0i, h0j]
      have hij : i ≠ j := fun e => hne (by rw [e])
      match i, j with
      | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl hij
      | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩ | ⟨1, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨0, _⟩ => simp at hv ⊢; omega
      | ⟨1, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ => simp at hv ⊢; omega
    · by_cases h1 : v = G.t 1
      · subst h1; simp only [beq_false_of_ne h0, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, hs' 1] at hv
        have h1i : (G.t i == G.t 1) = (1 == i) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
          exact ⟨fun e => (G.distinct i 1 e).symm, fun e => by rw [← e]⟩
        have h1j : (G.t j == G.t 1) = (1 == j) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
          exact ⟨fun e => (G.distinct j 1 e).symm, fun e => by rw [← e]⟩
        rw [h1i, h1j]
        have hij : i ≠ j := fun e => hne (by rw [e])
        match i, j with
        | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl hij
        | ⟨0, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨1, _⟩ => simp at hv ⊢; omega
        | ⟨0, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨2, _⟩ => simp at hv ⊢; omega
      · by_cases h2 : v = G.t 2
        · subst h2; simp only [beq_false_of_ne h0, beq_false_of_ne h1, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, hs' 2] at hv
          have h2i : (G.t i == G.t 2) = (2 == i) := by
            apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
            exact ⟨fun e => (G.distinct i 2 e).symm, fun e => by rw [← e]⟩
          have h2j : (G.t j == G.t 2) = (2 == j) := by
            apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
            exact ⟨fun e => (G.distinct j 2 e).symm, fun e => by rw [← e]⟩
          rw [h2i, h2j]
          have hij : i ≠ j := fun e => hne (by rw [e])
          match i, j with
          | ⟨2, _⟩, ⟨2, _⟩ => exact absurd rfl hij
          | ⟨0, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨1, _⟩ => simp at hv ⊢; omega
          | ⟨0, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ => simp at hv ⊢; omega
        · have hni : (G.t i == v) = false := beq_false_of_ne (by
            match i with | ⟨0, _⟩ => exact Ne.symm h0 | ⟨1, _⟩ => exact Ne.symm h1 | ⟨2, _⟩ => exact Ne.symm h2)
          have hnj : (G.t j == v) = false := beq_false_of_ne (by
            match j with | ⟨0, _⟩ => exact Ne.symm h0 | ⟨1, _⟩ => exact Ne.symm h1 | ⟨2, _⟩ => exact Ne.symm h2)
          simp only [beq_false_of_ne h0, beq_false_of_ne h1, beq_false_of_ne h2, Bool.false_eq_true, ↓reduceIte] at hv
          simp [hni, hnj, hv]

theorem xor_eq_zero_imp_eq {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq; intro k
  have hk := congrArg (fun x => x.testBit k) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at hk
  cases h1 : a.testBit k <;> cases h2 : b.testBit k <;> simp_all

/-- Vertex `0` is ONLY adjacent to vertex `1` in `GB_k` (`∀ k ≥ 2`)! -/
theorem gbAdj_zero_iff (k : Nat) (_hk : 2 ≤ k) (v : Nat) :
    gbAdj k 0 v = true ↔ v = 1 := by
  simp only [gbAdj, binAdj, grayAdj, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ((h | h) | ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩)
    · omega
    · omega
    · have hi0 : i.val = 0 := by
        have heq : i.val = i.val >>> 1 := xor_eq_zero_imp_eq h1
        rw [Nat.shiftRight_eq_div_pow] at heq
        have : 2 ^ 1 = 2 := rfl
        omega
      rw [hi0] at h2; exact h2.symm
    · have hi1 : i.val + 1 = 0 := by
        have heq : i.val + 1 = (i.val + 1) >>> 1 := xor_eq_zero_imp_eq h2
        rw [Nat.shiftRight_eq_div_pow] at heq
        have : 2 ^ 1 = 2 := rfl
        omega
      omega
  · intro hv; subst hv; left; left; rfl

theorem gb_no_edge_0_b (k : Nat) (hk : 2 ≤ k) :
    (gbGraph k hk).graph.adj ((gbGraph k hk).t 0) ((gbGraph k hk).t 1) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have h1 := (gbAdj_zero_iff k hk _).mp h
  have hp : 2 ≤ 2 ^ (k - 1) := by
    have : 2 ^ 1 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  simp [gbGraph] at h1; omega

theorem gb_no_edge_0_c (k : Nat) (hk : 2 ≤ k) :
    (gbGraph k hk).graph.adj ((gbGraph k hk).t 0) ((gbGraph k hk).t 2) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have h1 := (gbAdj_zero_iff k hk _).mp h
  have hp : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  simp [gbGraph] at h1; omega

/-- **THEOREM 1B (Exact Perfect Matchings of All 4 Boundary Closures ∀ `k ≥ 2`)**:
    - Open `GB_k`: `pmSeq k`
    - Gray-closed `GB_k + (0, 2^(k-1))`: `pmSeq k + 1`
    - Binary-closed `GB_k + (0, 2^k - 1)`: `2 * pmSeq k`
    - Doubly-cyclic `GB_k^oo`: `2 * pmSeq k + 1`! -/
theorem gb_grayClosed_pm (k : Nat) (hk : 2 ≤ k) :
    exactPM (gbGrayClosed k hk) = pmSeq k + 1 := by
  have hlt : ((gbGraph k hk).t 0).val < ((gbGraph k hk).t 1).val := by
    simp [gbGraph]; exact Nat.two_pow_pos (k - 1)
  have h := exactPM_addTermEdge (gbGraph k hk) 0 1 hlt (gb_no_edge_0_b k hk) 1 (by decide)
  rw [gbGraph_pmVec_eq k hk 7, gbGraph_pmVec_eq k hk 1] at h
  exact h

theorem gb_binClosed_pm (k : Nat) (hk : 2 ≤ k) :
    exactPM (gbBinClosed k hk) = 2 * pmSeq k := by
  have hlt : ((gbGraph k hk).t 0).val < ((gbGraph k hk).t 2).val := by
    simp [gbGraph]; have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk; omega
  have h := exactPM_addTermEdge (gbGraph k hk) 0 2 hlt (gb_no_edge_0_c k hk) 2 (by decide)
  rw [gbGraph_pmVec_eq k hk 7, gbGraph_pmVec_eq k hk 2] at h
  change exactPM (gbBinClosed k hk) = pmSeq k + pmSeq k at h; omega

theorem gb_doublyCyclic_pm (k : Nat) (hk : 2 ≤ k) :
    exactPM (gbDoublyCyclic k hk) = 2 * pmSeq k + 1 := by
  let Gg : TermGraph (2 ^ k) := {
    graph := gbGrayClosed k hk
    t := (gbGraph k hk).t
    distinct := (gbGraph k hk).distinct
  }
  have hlt : (Gg.t 0).val < (Gg.t 2).val := by
    simp [Gg, gbGraph]; have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk; omega
  have hno : Gg.graph.adj (Gg.t 0) (Gg.t 2) = false := by
    have h0 := gb_no_edge_0_c k hk
    have h12 : ((gbGraph k hk).t 2 == (gbGraph k hk).t 1) = false :=
      beq_false_of_ne (fun e => by have := (gbGraph k hk).distinct 2 1 e; cases this)
    have h01 : ((gbGraph k hk).t 0 == (gbGraph k hk).t 1) = false :=
      beq_false_of_ne (fun e => by have := (gbGraph k hk).distinct 0 1 e; cases this)
    simp [Gg, gbGrayClosed, addEdgeGraph, h0, h12, h01]
  have hstep := exactPM_addTermEdge Gg 0 2 hlt hno 2 (by decide)
  have h7 : pmVec Gg 7 = pmSeq k + 1 := by
    rw [← exactPM_eq_pmVec7]; exact gb_grayClosed_pm k hk
  have h2 : pmVec Gg 2 = pmSeq k := by
    have hlt01 : ((gbGraph k hk).t 0).val < ((gbGraph k hk).t 1).val := by
      simp [gbGraph]; exact Nat.two_pow_pos (k - 1)
    have hperm_inv : ∀ s1 s2 : List (Edge (2 ^ k)), s1.Perm s2 →
        (if isInternalPM Gg 2 s1 then 1 else 0) = (if isInternalPM Gg 2 s2 then 1 else 0) := by
      intro s1 s2 hp
      suffices isInternalPM Gg 2 s1 = isInternalPM Gg 2 s2 by rw [this]
      apply Bool.eq_iff_iff.mpr; simp only [isInternalPM, decide_eq_true_eq]
      constructor <;> intro h v
      · rw [← degIn_perm v hp]; exact h v
      · rw [degIn_perm v hp]; exact h v
    unfold pmVec
    change sumSubsets (fun M => if isInternalPM Gg 2 M then 1 else 0) (allEdges (gbGrayClosed k hk)) = pmSeq k
    unfold gbGrayClosed
    rw [sumSubsets_perm hperm_inv (allEdges_addEdge_perm (gbGraph k hk).graph _ _ hlt01 (gb_no_edge_0_b k hk))]
    simp only [sumSubsets]
    have hzero : sumSubsets (fun s => if isInternalPM Gg 2 (((gbGraph k hk).t 0, (gbGraph k hk).t 1) :: s) then 1 else 0)
        (allEdges (gbGraph k hk).graph) = 0 := by
      have h0 : ∀ s, (if isInternalPM Gg 2 (((gbGraph k hk).t 0, (gbGraph k hk).t 1) :: s) then 1 else 0) = 0 := by
        intro s
        have hf : isInternalPM Gg 2 (((gbGraph k hk).t 0, (gbGraph k hk).t 1) :: s) = false := by
          apply Bool.eq_false_iff.mpr
          intro hall
          simp only [isInternalPM, decide_eq_true_eq] at hall
          have hv := hall (Gg.t 0)
          rw [targetDeg_term] at hv
          simp [Gg, degIn] at hv
          have hbit : fin8Bit 2 0 = false := rfl
          rw [hbit] at hv; simp at hv
        simp [hf]
      rw [sumSubsets_congr h0]
      clear h0
      induction (allEdges (gbGraph k hk).graph) with
      | nil => rfl
      | cons _ _ ih => simp [sumSubsets, ih]
    rw [hzero, Nat.add_zero]
    have hsame : pmVec (gbGraph k hk) 2 = pmSeq k := by rw [gbGraph_pmVec_eq k hk 2]; rfl
    exact hsame
  change exactPM (addEdgeGraph Gg.graph (Gg.t 0) (Gg.t 2) _) = 2 * pmSeq k + 1
  rw [hstep, h7, h2]
  omega

-- ----------------------------------------------------------------------------
-- 5B. Theorem 2: Exact Independence Number `α(GB_k) = 3 * 2^(k-3) + 1` & Forced Terminals
-- ----------------------------------------------------------------------------

theorem gbGraph2_alphaVec (s : Fin 8) :
    alphaVec (gbGraph 2 (by omega)) s = gbAlphaBase2 s := by
  revert s; decide

theorem gbGraph3_alphaVec (s : Fin 8) :
    alphaVec (gbGraph 3 (by omega)) s = gbAlphaInv 3 s := by
  rw [gbGraph_alphaVec_succ (k := 2) (by omega)]
  have h2 : alphaVec (gbGraph 2 (by omega)) = gbAlphaBase2 := funext gbGraph2_alphaVec
  rw [h2]
  revert s; decide

theorem optMax_map_add (c : Nat) (x y : Option Nat) :
    optMax (x.map (· + c)) (y.map (· + c)) = (optMax x y).map (· + c) := by
  cases x <;> cases y <;> simp [optMax] <;> omega

theorem maxFin8_map_add (c : Nat) (f : Fin 8 → Option Nat) :
    maxFin8 (fun s => (f s).map (· + c)) = (maxFin8 f).map (· + c) := by
  simp only [maxFin8, optMax_map_add]

theorem stepAlpha_shift (spec : GlueSpec) (c : Nat) (v : Fin 8 → Option Nat) (s : Fin 8) :
    stepAlpha spec (fun i => (v i).map (· + c)) (fun i => (v i).map (· + c)) s =
    (stepAlpha spec v v s).map (· + 2 * c) := by
  unfold stepAlpha maxPairsFin8
  rw [← maxFin8_map_add]
  apply maxFin8_congr; intro sL
  rw [← maxFin8_map_add]
  apply maxFin8_congr; intro sR
  dsimp only
  cases bridgeIndepOk spec sL sR && (outMask spec sL sR == s)
  · rfl
  · simp only [↓reduceIte]
    cases v sL <;> cases v sR <;> simp [optAdd]
    omega

theorem stepAlpha_gbSpec_offset : ∀ s : Fin 8,
    stepAlpha gbSpec (fun i => some (gbAlphaOffset i)) (fun i => some (gbAlphaOffset i)) s =
    some (gbAlphaOffset s + 1) := by
  decide

theorem stepAlpha_gbSpec_inv (k : Nat) (hk : 3 ≤ k) (s : Fin 8) :
    stepAlpha gbSpec (gbAlphaInv k) (gbAlphaInv k) s = gbAlphaInv (k + 1) s := by
  have hA_ge : 4 ≤ alphaFormula k := by
    unfold alphaFormula; have := Nat.two_pow_pos (k - 3); omega
  have hA_succ : alphaFormula (k + 1) = 2 * alphaFormula k - 1 := by
    unfold alphaFormula
    have hpow : 2 ^ (k + 1 - 3) = 2 * 2 ^ (k - 3) := by
      rw [show k + 1 - 3 = (k - 3) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    omega
  have hshift : gbAlphaInv k = fun i => (some (gbAlphaOffset i)).map (· + (alphaFormula k - 2)) := by
    funext i
    match i with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ =>
      simp [gbAlphaInv, gbAlphaOffset]; try omega
  rw [hshift, stepAlpha_shift, stepAlpha_gbSpec_offset s]
  match s with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ =>
    simp [gbAlphaInv, gbAlphaOffset]; omega

theorem gbGraph_alphaVec_eq (k : Nat) (hk : 3 ≤ k) (s : Fin 8) :
    alphaVec (gbGraph k (by omega)) s = gbAlphaInv k s := by
  induction k generalizing s with
  | zero => omega
  | succ k ih =>
    by_cases hk3 : k = 2
    · subst hk3; exact gbGraph3_alphaVec s
    · have hkge : 3 ≤ k := by omega
      rw [gbGraph_alphaVec_succ (by omega)]
      have hfun : alphaVec (gbGraph k (by omega)) = gbAlphaInv k := funext (fun t => ih hkge t)
      rw [hfun]
      exact stepAlpha_gbSpec_inv k hkge s

/-- **THEOREM 2A (Exact Independence Number of `GB_k` ∀ `k ≥ 3`)**:
    `exactAlpha (GB_k) = some (3 * 2^(k - 3) + 1)`. -/
theorem gb_alpha_exact (k : Nat) (hk : 3 ≤ k) :
    exactAlpha (gbGraph k (by omega)).graph = some (3 * 2 ^ (k - 3) + 1) := by
  rw [exactAlpha_eq_maxFin8]
  have hfun : alphaVec (gbGraph k (by omega)) = gbAlphaInv k := funext (gbGraph_alphaVec_eq k hk)
  rw [hfun]
  have hA : 4 ≤ alphaFormula k := by
    unfold alphaFormula; have := Nat.two_pow_pos (k - 3); omega
  simp only [maxFin8, gbAlphaInv, optMax]
  congr 1; unfold alphaFormula at hA ⊢; omega

/-- **THEOREM 2B (Forced-Terminal Theorem for Maximum Independent Sets of `GB_k` ∀ `k ≥ 3`)**:
    Every maximum independent set `S` of `GB_k` (`k ≥ 3`) MUST contain all three bit-terminals
    `0`, `2^(k - 1)`, and `2^k - 1`! -/
theorem gb_max_indep_forces_terminals (k : Nat) (hk : 3 ≤ k) (S : Fin (2 ^ k) → Bool)
    (hind : isIndep (gbGraph k (by omega)).graph S = true)
    (hcard : cardBool (2 ^ k) S = 3 * 2 ^ (k - 3) + 1) :
    S ((gbGraph k (by omega)).t 0) = true ∧
    S ((gbGraph k (by omega)).t 1) = true ∧
    S ((gbGraph k (by omega)).t 2) = true := by
  let G := gbGraph k (by omega)
  let s := termMask G S
  have hval : alphaVec G s = gbAlphaInv k s := gbGraph_alphaVec_eq k hk s
  have hA : 4 ≤ alphaFormula k := by unfold alphaFormula; have := Nat.two_pow_pos (k - 3); omega
  have hle_of : ∀ d, alphaVec G s = some d → cardBool (2 ^ k) S ≤ d := by
    intro d hd
    have hiff := (maxBoolFun_eq_some_iff.mp hd).2 S (cardBool (2 ^ k) S)
    apply hiff
    simp [G, hind, s]
  have hs7 : s = 7 := by
    match hs : s with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
      have hle := hle_of _ hval
      simp [alphaFormula] at hle
      omega
    | ⟨7, _⟩ => rfl
  have h0 : fin8Bit s 0 = true := by rw [hs7]; rfl
  have h1 : fin8Bit s 1 = true := by rw [hs7]; rfl
  have h2 : fin8Bit s 2 = true := by rw [hs7]; rfl
  rw [fin8Bit_termMask] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

/-- **THEOREM 2C (Doubly-Cyclic Independence Number Drop ∀ `k ≥ 3`)**:
    Closing both the binary cycle `(0, 2^k - 1)` and Gray cycle `(0, 2^(k-1))` drops the
    independence number by exactly 1: `α(GB_k^oo) = 3 * 2^(k - 3)`. -/
theorem gb_doublyCyclic_alpha (k : Nat) (hk : 3 ≤ k) :
    exactAlpha (gbDoublyCyclic k (by omega)) = some (3 * 2 ^ (k - 3)) := by
  let G := gbGraph k (by omega)
  have hA_eq : alphaFormula k = 3 * 2 ^ (k - 3) + 1 := rfl
  have hA_ge : 4 ≤ alphaFormula k := by unfold alphaFormula; have := Nat.two_pow_pos (k - 3); omega
  -- An independent set of `gbDoublyCyclic` is an independent set of `G` with `!(S (t 0) && (S (t 1) || S (t 2)))`!
  have hind_iff : ∀ S : Fin (2 ^ k) → Bool,
      isIndep (gbDoublyCyclic k (by omega)) S =
      (isIndep G.graph S && !(S (G.t 0) && (S (G.t 1) || S (G.t 2)))) := by
    intro S
    apply Bool.eq_iff_iff.mpr
    simp only [isIndep, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro u v hu hv
        have h' := h u v hu hv
        simp only [gbDoublyCyclic, gbGrayClosed, addEdgeGraph, Bool.or_eq_false_iff] at h'
        exact h'.1.1.1.1
      · cases h0 : S (G.t 0)
        · rfl
        · cases h1 : S (G.t 1)
          · cases h2 : S (G.t 2)
            · rfl
            · have h' := h (G.t 0) (G.t 2) h0 h2
              simp [gbDoublyCyclic, gbGrayClosed, addEdgeGraph, G] at h'
          · have h' := h (G.t 0) (G.t 1) h0 h1
            simp [gbDoublyCyclic, gbGrayClosed, addEdgeGraph, G] at h'
    · rintro ⟨hG, hterm⟩ u v hu hv
      simp only [gbDoublyCyclic, gbGrayClosed, addEdgeGraph, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
                 beq_eq_false_iff_ne]
      refine ⟨⟨⟨⟨hG u v hu hv, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · by_cases h1 : u = G.t 0
        · right; intro h2; subst h1 h2; simp [G, hu, hv] at hterm
        · left; exact h1
      · by_cases h1 : u = G.t 1
        · right; intro h2; subst h1 h2; simp [G, hu, hv] at hterm
        · left; exact h1
      · by_cases h1 : u = G.t 0
        · right; intro h2; subst h1 h2; simp [G, hu, hv] at hterm
        · left; exact h1
      · by_cases h1 : u = G.t 2
        · right; intro h2; subst h1 h2; simp [G, hu, hv] at hterm
        · left; exact h1
  unfold exactAlpha
  rw [maxBoolFun_eq_some_iff]
  have h3 : alphaVec G 3 = some (3 * 2 ^ (k - 3)) := by
    have := gbGraph_alphaVec_eq k hk 3
    simpa [G, gbAlphaInv, alphaFormula] using this
  rcases (maxBoolFun_eq_some_iff.mp h3).1 with ⟨S0, hS0⟩
  have hS0_cond : (isIndep G.graph S0 && (termMask G S0 == 3)) = true ∧ cardBool (2 ^ k) S0 = 3 * 2 ^ (k - 3) := by
    by_cases hc : (isIndep G.graph S0 && (termMask G S0 == 3)) = true
    · simp only [hc, ↓reduceIte, Option.some.injEq] at hS0; exact ⟨hc, hS0⟩
    · simp only [hc] at hS0; cases hS0
  have hS0_ind : isIndep G.graph S0 = true := (Bool.and_eq_true _ _).mp hS0_cond.1 |>.1
  have hS0_m3 : termMask G S0 = 3 := beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hS0_cond.1 |>.2)
  have hS0_t0 : S0 (G.t 0) = false := by
    rw [← fin8Bit_termMask G S0 0, hS0_m3]; rfl
  constructor
  · refine ⟨S0, ?_⟩
    rw [hind_iff S0, hS0_ind, hS0_t0]
    simp [hS0_cond.2]
  · intro S d' hS
    by_cases hc : isIndep (gbDoublyCyclic k (by omega)) S = true
    · simp only [hc, ↓reduceIte, Option.some.injEq] at hS
      rw [hind_iff S] at hc
      have ⟨hSG, hSnot⟩ := (Bool.and_eq_true _ _).mp hc
      have hle_max : cardBool (2 ^ k) S ≤ 3 * 2 ^ (k - 3) + 1 := by
        have hax := (maxBoolFun_eq_some_iff.mp (gb_alpha_exact k hk)).2 S (cardBool (2 ^ k) S)
        exact hax (by simp [G, hSG])
      by_cases heq : cardBool (2 ^ k) S = 3 * 2 ^ (k - 3) + 1
      · have ⟨ht0, ht1, ht2⟩ := gb_max_indep_forces_terminals k hk S hSG heq
        simp [G, ht0, ht1, ht2] at hSnot
      · omega
    · simp only [hc] at hS; cases hS

-- ----------------------------------------------------------------------------
-- 5C. Theorems 3, 4, 5: Chromatic Number 3, Crapo Beta Quartet, & Linear (q-2)-Multiplicity
-- ----------------------------------------------------------------------------

theorem gbChromBase_0 : gbChromBase 0 = [] := rfl
theorem gbChromBase_1 : gbChromBase 1 = pLin 2 := rfl
theorem gbChromBase_2 : gbChromBase 2 = pLin 2 := rfl
theorem gbChromBase_3 : gbChromBase 3 = [] := rfl
theorem gbChromBase_4 : gbChromBase 4 = pLin 3 := rfl
theorem gb2_adj_eq : ∀ u v : Fin 4, (gbGraph 2 (Nat.le_refl 2)).graph.adj u v =
    ((u == 0 && v == 1) || (u == 1 && v == 0) || (u == 1 && v == 2) || (u == 2 && v == 1) ||
     (u == 1 && v == 3) || (u == 3 && v == 1) || (u == 2 && v == 3) || (u == 3 && v == 2)) := by
  decide

/-- Exact base-case proof `HasChromVec (gbGraph 2) gbChromBase` for ALL `q : Nat`. -/
theorem gbGraph2_hasChromVec : HasChromVec (gbGraph 2 (by omega)) gbChromBase := by
  intro q c0 c1 c2
  -- Expand `sumColorings q 4` into 4 nested `sumFin q` over `(x0, x1, x2, x3)`
  -- In `gbGraph 2`: edges are `(0,1), (1,2), (1,3), (2,3)` and terminals are `t 0 = 0, t 1 = 2, t 2 = 3`.
  have h1 : ∀ (x : Fin q) (f : Fin q → Nat), sumFin q (fun d => if x == d then f d else 0) = f x := by
    intro x f
    have hInt := sumFinInt_single q x (f x : Int)
    have hcast : (sumFin q (fun d => if x == d then f d else 0) : Int) =
                 sumFinInt q (fun d => if d = x then (f x : Int) else 0) := by
      rw [sumFinInt_ofNat]
      apply sumFinInt_congr; intro d
      by_cases hdx : d = x
      · subst hdx; simp
      · have hne : (x == d) = false := beq_false_of_ne (Ne.symm hdx)
        simp [hdx, hne]
    omega
  have hzero_if : ∀ (b : Bool) (g : Fin q → Nat),
      sumFin q (fun d => if b then g d else 0) = if b then sumFin q g else 0 := by
    intro b g; cases b <;> simp [sumFin_zero_fn]
  have hred : chromFixed (gbGraph 2 (by omega)) q c0 c1 c2 =
      if c1 = c2 then 0
      else sumFin q (fun x1 => if x1 ≠ c0 ∧ x1 ≠ c1 ∧ x1 ≠ c2 then 1 else 0) := by
    unfold chromFixed
    change sumFin q (fun x0 => sumFin q (fun x1 => sumFin q (fun x2 => sumFin q (fun x3 =>
      let f := consFun x0 (consFun x1 (consFun x2 (consFun x3 (fun i => Fin.elim0 i))))
      if isProperColoring (gbGraph 2 (by omega)).graph f &&
         (f ((gbGraph 2 (by omega)).t 0) == c0) &&
         (f ((gbGraph 2 (by omega)).t 1) == c1) &&
         (f ((gbGraph 2 (by omega)).t 2) == c2)
      then 1 else 0)))) = _
    have hpt : ∀ x0 x1 x2 x3 : Fin q,
        (let f := consFun x0 (consFun x1 (consFun x2 (consFun x3 (fun i => Fin.elim0 i))))
         if isProperColoring (gbGraph 2 (by omega)).graph f &&
            (f ((gbGraph 2 (by omega)).t 0) == c0) &&
            (f ((gbGraph 2 (by omega)).t 1) == c1) &&
            (f ((gbGraph 2 (by omega)).t 2) == c2)
         then 1 else 0) =
        (if c0 == x0 then
           if c1 == x2 then
             if c2 == x3 then
               if c1 ≠ c2 ∧ x1 ≠ c0 ∧ x1 ≠ c1 ∧ x1 ≠ c2 then 1 else 0
             else 0
           else 0
         else 0) := by
      intro x0 x1 x2 x3
      let f := consFun x0 (consFun x1 (consFun x2 (consFun x3 (fun i => Fin.elim0 i))))
      change (if isProperColoring (gbGraph 2 (by omega)).graph f &&
                 (f ((gbGraph 2 (by omega)).t 0) == c0) &&
                 (f ((gbGraph 2 (by omega)).t 1) == c1) &&
                 (f ((gbGraph 2 (by omega)).t 2) == c2)
              then 1 else 0) = _
      have hf0 : f 0 = x0 := rfl
      have hf1 : f 1 = x1 := rfl
      have hf2 : f 2 = x2 := rfl
      have hf3 : f 3 = x3 := rfl
      have ht0 : (gbGraph 2 (by omega)).t 0 = 0 := rfl
      have ht1 : (gbGraph 2 (by omega)).t 1 = 2 := rfl
      have ht2 : (gbGraph 2 (by omega)).t 2 = 3 := rfl
      rw [ht0, ht1, ht2, hf0, hf2, hf3]
      have hprop : isProperColoring (gbGraph 2 (by omega)).graph f =
          decide (x0 ≠ x1 ∧ x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3) := by
        apply Bool.eq_iff_iff.mpr
        simp only [isProperColoring, decide_eq_true_eq]
        constructor
        · intro h
          refine ⟨h 0 1 (by rw [gb2_adj_eq]; rfl), h 1 2 (by rw [gb2_adj_eq]; rfl),
                  h 1 3 (by rw [gb2_adj_eq]; rfl), h 2 3 (by rw [gb2_adj_eq]; rfl)⟩
        · rintro ⟨h01, h12, h13, h23⟩ u v huv
          rw [gb2_adj_eq] at huv
          match u, v with
          | ⟨0, _⟩, ⟨1, _⟩ => exact h01
          | ⟨1, _⟩, ⟨0, _⟩ => exact h01.symm
          | ⟨1, _⟩, ⟨2, _⟩ => exact h12
          | ⟨2, _⟩, ⟨1, _⟩ => exact h12.symm
          | ⟨1, _⟩, ⟨3, _⟩ => exact h13
          | ⟨3, _⟩, ⟨1, _⟩ => exact h13.symm
          | ⟨2, _⟩, ⟨3, _⟩ => exact h23
          | ⟨3, _⟩, ⟨2, _⟩ => exact h23.symm
          | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨2, _⟩ | ⟨0, _⟩, ⟨3, _⟩
          | ⟨1, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨2, _⟩
          | ⟨3, _⟩, ⟨0, _⟩ | ⟨3, _⟩, ⟨3, _⟩ => cases huv
      rw [hprop]
      by_cases e0 : x0 = c0
      · by_cases e2 : x2 = c1
        · by_cases e3 : x3 = c2
          · rw [e0, e2, e3]
            simp only [beq_self_eq_true, Bool.and_true, ↓reduceIte]
            by_cases hcond : c1 ≠ c2 ∧ x1 ≠ c0 ∧ x1 ≠ c1 ∧ x1 ≠ c2
            · have hdec : decide (c0 ≠ x1 ∧ x1 ≠ c1 ∧ x1 ≠ c2 ∧ c1 ≠ c2) = true :=
                decide_eq_true ⟨hcond.2.1.symm, hcond.2.2.1, hcond.2.2.2, hcond.1⟩
              rw [hdec]; simp [hcond]
            · have hdec : decide (c0 ≠ x1 ∧ x1 ≠ c1 ∧ x1 ≠ c2 ∧ c1 ≠ c2) = false := by
                apply decide_eq_false; intro ⟨a, b, c, d⟩; exact hcond ⟨d, a.symm, b, c⟩
              rw [hdec]; simp [hcond]
          · simp [beq_false_of_ne e3, beq_false_of_ne (Ne.symm e3)]
        · simp [beq_false_of_ne e2, beq_false_of_ne (Ne.symm e2)]
      · simp [beq_false_of_ne e0, beq_false_of_ne (Ne.symm e0)]
    simp only [hpt, hzero_if, h1]
    by_cases h12 : c1 = c2
    · subst h12; simp [sumFin_zero_fn]
    · simp [h12]
  rw [hred]
  by_cases h12 : c1 = c2
  · subst h12
    simp only [↓reduceIte, Int.natCast_zero]
    unfold pat3
    by_cases h01 : c0 = c1
    · subst h01; simp [gbChromBase, pEval]
    · simp [h01, gbChromBase, pEval]
  · simp only [h12, ↓reduceIte, sumFinInt_ofNat]
    by_cases h01 : c0 = c1
    · subst h01
      have hxs : ([c0, c2] : List (Fin q)).Nodup := by simp [h12]
      have hsp := sumFinInt_split q [c0, c2] hxs
        (fun x1 => ((if x1 ≠ c0 ∧ x1 ≠ c0 ∧ x1 ≠ c2 then 1 else 0 : Nat) : Int)) 1
        (fun d hd => by simp at hd; simp [hd.1, hd.2])
      rw [hsp]
      have hp : pat3 c0 c0 c2 = 1 := by simp [pat3, h12]
      rw [hp, gbChromBase_1, pEval_lin]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
                 ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte, Int.natCast_zero]
      omega
    · by_cases h02 : c0 = c2
      · subst h02
        have hxs : ([c0, c1] : List (Fin q)).Nodup := by simp [h01]
        have hsp := sumFinInt_split q [c0, c1] hxs
          (fun x1 => ((if x1 ≠ c0 ∧ x1 ≠ c1 ∧ x1 ≠ c0 then 1 else 0 : Nat) : Int)) 1
          (fun d hd => by simp at hd; simp [hd.1, hd.2])
        rw [hsp]
        have hp : pat3 c0 c1 c0 = 2 := by
          unfold pat3
          rw [ite_eq_right_iff.mpr (fun h => absurd h h01), ite_eq_left_iff.mpr (fun h => absurd rfl h)]
        rw [hp, gbChromBase_2, pEval_lin]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
                   ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte, Int.natCast_zero]
        omega
      · have hxs : ([c0, c1, c2] : List (Fin q)).Nodup := by simp [h01, h02, h12]
        have hsp := sumFinInt_split q [c0, c1, c2] hxs
          (fun x1 => ((if x1 ≠ c0 ∧ x1 ≠ c1 ∧ x1 ≠ c2 then 1 else 0 : Nat) : Int)) 1
          (fun d hd => by simp at hd; simp [hd.1, hd.2.1, hd.2.2])
        rw [hsp]
        have hp : pat3 c0 c1 c2 = 4 := by
          unfold pat3
          rw [ite_eq_right_iff.mpr (fun h => absurd h h01),
              ite_eq_right_iff.mpr (fun h => absurd h h02),
              ite_eq_right_iff.mpr (fun h => absurd h h12)]
        rw [hp, gbChromBase_4, pEval_lin]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
                   ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte, Int.natCast_zero]
        omega

theorem gbChromVec_succ (k : Nat) (hk : 2 ≤ k) :
    gbChromVec (k + 1) = stepChromPoly gbSpec (gbChromVec k) (gbChromVec k) := by
  match k with
  | 0 | 1 => omega
  | n + 2 => rfl

/-- Exact 5-state chromatic soundness for `GB_k` (`∀ k ≥ 2`)! -/
theorem gbGraph_hasChromVec (k : Nat) (hk : 2 ≤ k) :
    HasChromVec (gbGraph k hk) (gbChromVec k) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk2 : k = 1
    · subst hk2; exact gbGraph2_hasChromVec
    · have hkge : 2 ≤ k := by omega
      rw [gbChromVec_succ k hkge]
      exact gbGraph_hasChromVec_succ hkge (ih hkge)

theorem gbGraph_exactChrom (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    (exactChromCount (gbGraph k hk).graph q : Int) = pEval (gbChromPoly k) (q : Int) :=
  totalChrom_of_hasChromVec (gbGraph_hasChromVec k hk) q

theorem pEval_sumFinRangePoly_rec (m : Nat) (f : Nat → Poly) (q : Int) :
    pEval (sumFinRangePoly m f) q = sumRangeInt m (fun c => pEval (f c) q) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumFinRangePoly, sumRangeInt, pEval_add, ih]

theorem pEval_sumChoicePoly (d m : Nat) (f : List Nat → Poly) (q : Int) :
    pEval (sumChoicePoly d m f) q = evalChoiceInt q d m (fun ls => pEval (f ls) q) := by
  induction d generalizing m f with
  | zero => rfl
  | succ d ih =>
    simp only [sumChoicePoly, evalChoiceInt, pEval_add, pEval_mul, pEval_lin, pEval_sumFinRangePoly_rec]
    congr 1
    · have hcongr : ∀ n (g1 g2 : Nat → Int), (∀ c, g1 c = g2 c) → sumRangeInt n g1 = sumRangeInt n g2 := by
        intro n g1 g2 h; induction n with
        | zero => rfl
        | succ n ihn => simp only [sumRangeInt, ihn, h]
      exact hcongr m _ _ (fun c => ih m (fun rest => f (c :: rest)))
    · rw [ih (m + 1) (fun rest => f (m :: rest))]

theorem pEval_totalChromPoly (v : Fin 5 → Poly) (q : Int) :
    pEval (totalChromPoly v) q = q * pEval (mobU4 v) q := by
  unfold totalChromPoly mobU4
  rw [pEval_sumChoicePoly]
  simp only [pEval_add, pEval_mul, pEval_lin]
  dsimp [evalChoiceInt, sumRangeInt, pat3]
  grind

theorem bridgesProper_gbSpec (c : Bool × Fin 3 → Nat) :
    bridgesProper gbSpec c = gbBridgesProper c := by
  apply Bool.eq_iff_iff.mpr
  simp only [bridgesProper, gbBridgesProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h 2 0 (by decide), h 1 1 (by decide)⟩
  · rintro ⟨h1, h2⟩ i j hij
    match i, j with
    | ⟨2, _⟩, ⟨0, _⟩ => exact h1
    | ⟨1, _⟩, ⟨1, _⟩ => exact h2
    | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩
    | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨2, _⟩
    | ⟨2, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ => cases hij

theorem pEval_stepChromPoly_gbSpec_0 (v : Fin 5 → Poly) (q : Int) :
    pEval (stepChromPoly gbSpec v v 0) q =
    gbBellStep0 q (pEval (v 0) q) (pEval (v 1) q) (pEval (v 2) q) (pEval (v 3) q) (pEval (v 4) q) := by
  unfold stepChromPoly gbBellStep0
  rw [pEval_sumChoicePoly]
  simp only [bridgesProper_gbSpec]
  dsimp [canonicalRep, evalChoiceInt, sumRangeInt, assign6, gbBridgesProper, gbSpec, pat3]
  simp only [pEval_mul, pEval]
  grind

theorem pEval_stepChromPoly_gbSpec_1 (v : Fin 5 → Poly) (q : Int) :
    pEval (stepChromPoly gbSpec v v 1) q =
    gbBellStep1 q (pEval (v 0) q) (pEval (v 1) q) (pEval (v 2) q) (pEval (v 3) q) (pEval (v 4) q) := by
  unfold stepChromPoly gbBellStep1
  rw [pEval_sumChoicePoly]
  simp only [bridgesProper_gbSpec]
  dsimp [canonicalRep, evalChoiceInt, sumRangeInt, assign6, gbBridgesProper, gbSpec, pat3]
  simp only [pEval_mul, pEval]
  grind

theorem pEval_stepChromPoly_gbSpec_2 (v : Fin 5 → Poly) (q : Int) :
    pEval (stepChromPoly gbSpec v v 2) q =
    gbBellStep2 q (pEval (v 0) q) (pEval (v 1) q) (pEval (v 2) q) (pEval (v 3) q) (pEval (v 4) q) := by
  unfold stepChromPoly gbBellStep2
  rw [pEval_sumChoicePoly]
  simp only [bridgesProper_gbSpec]
  dsimp [canonicalRep, evalChoiceInt, sumRangeInt, assign6, gbBridgesProper, gbSpec, pat3]
  simp only [pEval_mul, pEval]
  grind

theorem pEval_stepChromPoly_gbSpec_3 (v : Fin 5 → Poly) (q : Int) :
    pEval (stepChromPoly gbSpec v v 3) q =
    gbBellStep3 q (pEval (v 0) q) (pEval (v 1) q) (pEval (v 2) q) (pEval (v 3) q) (pEval (v 4) q) := by
  unfold stepChromPoly gbBellStep3
  rw [pEval_sumChoicePoly]
  simp only [bridgesProper_gbSpec]
  dsimp [canonicalRep, evalChoiceInt, sumRangeInt, assign6, gbBridgesProper, gbSpec, pat3]
  simp only [pEval_mul, pEval]
  grind

theorem pEval_stepChromPoly_gbSpec_4 (v : Fin 5 → Poly) (q : Int) :
    pEval (stepChromPoly gbSpec v v 4) q =
    gbBellStep4 q (pEval (v 0) q) (pEval (v 1) q) (pEval (v 2) q) (pEval (v 3) q) (pEval (v 4) q) := by
  unfold stepChromPoly gbBellStep4
  rw [pEval_sumChoicePoly]
  simp only [bridgesProper_gbSpec]
  dsimp [canonicalRep, evalChoiceInt, sumRangeInt, assign6, gbBridgesProper, gbSpec, pat3]
  simp only [pEval_mul, pEval]
  grind

/-- **THE 5 EXACT `Π_3` MÖBIUS-QUOTIENT TRANSFER IDENTITIES FOR `GB_k`** (valid ∀ `q : Int`, ∀ `v`). -/
theorem mobius_step_0 (v : Fin 5 → Poly) (q : Int) :
    let u0 := pEval (mobU0 v) q; let u1 := pEval (mobU1 v) q; let u2 := pEval (mobU2 v) q
    let u4 := pEval (mobU4 v) q
    (q - 1) * pEval (mobU0 (stepChromPoly gbSpec v v)) q =
    q * u0 ^ 2 + u0 * (-q * u1 - 2 * u2 + u4) + u1 * u2 + (2 - q) * u2 ^ 2 + (q - 2) * u2 * u4 := by
  simp only [mobU0, mobU1, mobU2, mobU4, pEval_add, pEval_mul, pEval_lin, pEval_stepChromPoly_gbSpec_0, gbBellStep0]
  grind

theorem mobius_step_1 (v : Fin 5 → Poly) (q : Int) :
    let u0 := pEval (mobU0 v) q; let u1 := pEval (mobU1 v) q; let u2 := pEval (mobU2 v) q
    let u4 := pEval (mobU4 v) q
    (q - 1) * pEval (mobU1 (stepChromPoly gbSpec v v)) q =
    -q * u1 ^ 2 + u0 * (q * u1 - u4) + u1 * (-u2 + 2 * u4) + (2 - q) * u2 * u4 + (q - 2) * u4 ^ 2 := by
  simp only [mobU0, mobU1, mobU2, mobU4, pEval_add, pEval_mul, pEval_lin,
             pEval_stepChromPoly_gbSpec_0, pEval_stepChromPoly_gbSpec_1, gbBellStep0, gbBellStep1]
  grind

theorem mobius_step_2 (v : Fin 5 → Poly) (q : Int) :
    let u0 := pEval (mobU0 v) q; let u1 := pEval (mobU1 v) q; let u2 := pEval (mobU2 v) q
    let u3 := pEval (mobU3 v) q; let u4 := pEval (mobU4 v) q
    (q - 2) * ((q - 1) * pEval (mobU2 (stepChromPoly gbSpec v v)) q) =
    q ^ 2 * u0 ^ 2 + u0 * (-2 * q * u1 - 2 * q * u2 - 2 * q * u3 + 4 * u4) + u1 ^ 2 +
    u1 * (-q ^ 2 * u3 + 4 * q * u3 + q * u4 + 2 * u2 - 2 * u3 - 4 * u4) +
    u2 ^ 2 * (-q ^ 2 + 3 * q - 1) + u2 * (2 * q * u4 + 2 * u3 - 6 * u4) +
    u3 ^ 2 + u3 * (q * u4 - 4 * u4) + u4 ^ 2 * (q ^ 2 - 5 * q + 7) := by
  simp only [mobU0, mobU1, mobU2, mobU3, mobU4, pEval_add, pEval_mul, pEval_lin,
             pEval_stepChromPoly_gbSpec_0, pEval_stepChromPoly_gbSpec_2, gbBellStep0, gbBellStep2]
  grind

theorem mobius_step_3 (v : Fin 5 → Poly) (q : Int) :
    let u0 := pEval (mobU0 v) q; let u2 := pEval (mobU2 v) q
    let u3 := pEval (mobU3 v) q; let u4 := pEval (mobU4 v) q
    (q - 1) * pEval (mobU3 (stepChromPoly gbSpec v v)) q =
    u0 * (q * u3 - u4) + u2 * ((q ^ 2 - 3 * q + 3) * u4 - u3) := by
  simp only [mobU0, mobU2, mobU3, mobU4, pEval_add, pEval_mul, pEval_lin,
             pEval_stepChromPoly_gbSpec_0, pEval_stepChromPoly_gbSpec_3, gbBellStep0, gbBellStep3]
  grind

theorem mobius_step_4 (v : Fin 5 → Poly) (q : Int) :
    let u1 := pEval (mobU1 v) q; let u3 := pEval (mobU3 v) q; let u4 := pEval (mobU4 v) q
    (q - 1) * pEval (mobU4 (stepChromPoly gbSpec v v)) q =
    u1 * (q * u3 - u4) + u4 * ((q ^ 2 - 3 * q + 3) * u4 - u3) := by
  simp only [mobU1, mobU3, mobU4, pEval_add, pEval_mul, pEval_lin,
             pEval_stepChromPoly_gbSpec_0, pEval_stepChromPoly_gbSpec_1,
             pEval_stepChromPoly_gbSpec_2, pEval_stepChromPoly_gbSpec_3,
             pEval_stepChromPoly_gbSpec_4,
             gbBellStep0, gbBellStep1, gbBellStep2, gbBellStep3, gbBellStep4]
  grind

-- ----------------------------------------------------------------------------
-- Generic Boundary-Closure Chromatic Polynomial Soundness (All 4 Closures!)
-- ----------------------------------------------------------------------------

theorem exactChrom_addTermEdge_sum {n : Nat} (G : TermGraph n) (v : Fin 5 → Poly)
    (_hv : HasChromVec G v) (q : Nat)
    (cond : Fin q → Fin q → Fin q → Bool) (fSym : Nat → Nat → Nat → Poly)
    (hmatch : ∀ (c0 c1 c2 : Fin q) (l0 l1 l2 : Nat),
      (c0 = c1 ↔ l0 = l1) → (c0 = c2 ↔ l0 = l2) → (c1 = c2 ↔ l1 = l2) →
      ((if cond c0 c1 c2 then chromFixed G q c0 c1 c2 else 0 : Nat) : Int) = pEval (fSym l0 l1 l2) (q : Int))
    (G' : FinGraph n)
    (hprop : ∀ c : Fin n → Fin q,
      isProperColoring G' c = (isProperColoring G.graph c && cond (c (G.t 0)) (c (G.t 1)) (c (G.t 2)))) :
    (exactChromCount G' q : Int) =
    pEval (sumChoicePoly 3 0 (fun ls => match ls with | [l0, l1, l2] => fSym l0 l1 l2 | _ => [])) (q : Int) := by
  have hsum : exactChromCount G' q =
      sumFin q (fun c0 => sumFin q (fun c1 => sumFin q (fun c2 =>
        if cond c0 c1 c2 then chromFixed G q c0 c1 c2 else 0))) := by
    unfold exactChromCount chromFixed
    have hzero_if : ∀ (b : Bool) (m : Nat) (g : (Fin m → Fin q) → Nat),
        (if b then sumColorings q m g else 0) = sumColorings q m (fun c => if b then g c else 0) := by
      intro b m g; cases b
      · simp [sumColorings_zero_fn]
      · simp
    simp only [hzero_if, sumFin_sumColorings]
    apply sumColorings_congr; intro c
    rw [hprop c]
    have h1 : ∀ (x : Fin q) (f : Fin q → Nat), sumFin q (fun d => if x == d then f d else 0) = f x := by
      intro x f
      have hInt := sumFinInt_single q x (f x : Int)
      have hcast : (sumFin q (fun d => if x == d then f d else 0) : Int) =
                   sumFinInt q (fun d => if d = x then (f x : Int) else 0) := by
        rw [sumFinInt_ofNat]
        apply sumFinInt_congr; intro d
        by_cases hdx : d = x
        · subst hdx; simp
        · simp [hdx, beq_false_of_ne (Ne.symm hdx)]
      omega
    have hz : ∀ (b : Bool) (g : Fin q → Nat), sumFin q (fun d => if b then g d else 0) = if b then sumFin q g else 0 := by
      intro b g; cases b <;> simp [sumFin_zero_fn]
    have hpt : ∀ c0 c1 c2,
        (if cond c0 c1 c2 then
          if isProperColoring G.graph c && (c (G.t 0) == c0) && (c (G.t 1) == c1) && (c (G.t 2) == c2) then 1 else 0
         else 0) =
        (if c (G.t 0) == c0 then if c (G.t 1) == c1 then if c (G.t 2) == c2 then
          if isProperColoring G.graph c && cond (c (G.t 0)) (c (G.t 1)) (c (G.t 2)) then 1 else 0
         else 0 else 0 else 0) := by
      intro c0 c1 c2
      by_cases e0 : c (G.t 0) = c0
      · subst e0
        by_cases e1 : c (G.t 1) = c1
        · subst e1
          by_cases e2 : c (G.t 2) = c2
          · subst e2
            cases cond (c (G.t 0)) (c (G.t 1)) (c (G.t 2)) <;> cases isProperColoring G.graph c <;> simp
          · simp [beq_false_of_ne e2]
        · simp [beq_false_of_ne e1]
      · simp [beq_false_of_ne e0]
    simp only [hpt, hz, h1]
  rw [hsum, sumFinInt_ofNat]
  simp only [sumFinInt_ofNat]
  change sumColoringsList q 3 (fun ys => match ys with
    | [c0, c1, c2] => ((if cond c0 c1 c2 then chromFixed G q c0 c1 c2 else 0 : Nat) : Int)
    | _ => 0) = _
  apply sumChoicePoly_sound q 3 [] List.nodup_nil
  intro ys ls hylen hm
  rcases matchesPalette_to_env List.nodup_nil hm with ⟨pal, hlen, hpal_nd, _, hys_pal⟩
  cases ys with
  | nil => simp at hylen
  | cons c0 r0 => cases r0 with
    | nil => simp at hylen
    | cons c1 r1 => cases r1 with
      | nil => simp at hylen
      | cons c2 r2 => cases r2 with
        | cons _ _ => simp at hylen
        | nil =>
          cases ls with
          | nil => simp at hlen
          | cons l0 s0 => cases s0 with
            | nil => simp at hlen
            | cons l1 s1 => cases s1 with
              | nil => simp at hlen
              | cons l2 s2 => cases s2 with
                | cons _ _ => simp at hlen
                | nil =>
                  dsimp only
                  rcases hys_pal 0 (by simp) with ⟨h0, heq0⟩
                  rcases hys_pal 1 (by simp) with ⟨h1, heq1⟩
                  rcases hys_pal 2 (by simp) with ⟨h2, heq2⟩
                  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq0 heq1 heq2
                  apply hmatch c0 c1 c2 l0 l1 l2
                  · rw [← heq0, ← heq1]; exact nodup_getElem_eq_iff hpal_nd h0 h1
                  · rw [← heq0, ← heq2]; exact nodup_getElem_eq_iff hpal_nd h0 h2
                  · rw [← heq1, ← heq2]; exact nodup_getElem_eq_iff hpal_nd h1 h2

theorem gb_grayClosed_exactChrom (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    (exactChromCount (gbGrayClosed k hk) q : Int) = pEval (grayClosedChromPoly (gbChromVec k)) (q : Int) := by
  let G := gbGraph k hk
  have hprop : ∀ c : Fin (2 ^ k) → Fin q,
      isProperColoring (gbGrayClosed k hk) c = (isProperColoring G.graph c && decide (c (G.t 0) ≠ c (G.t 1))) := by
    intro c; apply Bool.eq_iff_iff.mpr
    simp only [isProperColoring, Bool.and_eq_true, decide_eq_true_eq, gbGrayClosed, addEdgeGraph, Bool.or_eq_true, beq_iff_eq]
    constructor
    · intro h; exact ⟨fun u v huv => h u v (Or.inl (Or.inl huv)), h (G.t 0) (G.t 1) (Or.inl (Or.inr ⟨rfl, rfl⟩))⟩
    · rintro ⟨hG, h01⟩ u v ((huv | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
      · exact hG u v huv
      · exact h01
      · exact h01.symm
  rw [exactChrom_addTermEdge_sum G (gbChromVec k) (gbGraph_hasChromVec k hk) q
        (fun a b _ => decide (a ≠ b)) (fun a b c => if a ≠ b then gbChromVec k (pat3 a b c) else [])
        (fun c0 c1 c2 l0 l1 l2 hab hac hbc => by
          by_cases h01 : c0 = c1
          · have h01' := hab.mp h01; simp [h01, h01', pEval]
          · have h01' := mt hab.mpr h01
            simp only [h01, h01', ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
            rw [gbGraph_hasChromVec k hk q c0 c1 c2, pat3_congr hab hac hbc])
        (gbGrayClosed k hk) hprop]
  rw [pEval_sumChoicePoly]
  simp only [grayClosedChromPoly, mobU4, mobU1, pEval_mul, pEval_var, pEval_sub, pEval_add, pEval_lin]
  dsimp [evalChoiceInt, sumRangeInt, pat3]
  simp only [pEval]
  grind

theorem gb_binClosed_exactChrom (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    (exactChromCount (gbBinClosed k hk) q : Int) = pEval (binClosedChromPoly (gbChromVec k)) (q : Int) := by
  let G := gbGraph k hk
  have hprop : ∀ c : Fin (2 ^ k) → Fin q,
      isProperColoring (gbBinClosed k hk) c = (isProperColoring G.graph c && decide (c (G.t 0) ≠ c (G.t 2))) := by
    intro c; apply Bool.eq_iff_iff.mpr
    simp only [isProperColoring, Bool.and_eq_true, decide_eq_true_eq, gbBinClosed, addEdgeGraph, Bool.or_eq_true, beq_iff_eq]
    constructor
    · intro h; exact ⟨fun u v huv => h u v (Or.inl (Or.inl huv)), h (G.t 0) (G.t 2) (Or.inl (Or.inr ⟨rfl, rfl⟩))⟩
    · rintro ⟨hG, h02⟩ u v ((huv | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
      · exact hG u v huv
      · exact h02
      · exact h02.symm
  rw [exactChrom_addTermEdge_sum G (gbChromVec k) (gbGraph_hasChromVec k hk) q
        (fun a _ c => decide (a ≠ c)) (fun a b c => if a ≠ c then gbChromVec k (pat3 a b c) else [])
        (fun c0 c1 c2 l0 l1 l2 hab hac hbc => by
          by_cases h02 : c0 = c2
          · have h02' := hac.mp h02; simp [h02, h02', pEval]
          · have h02' := mt hac.mpr h02
            simp only [h02, h02', ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
            rw [gbGraph_hasChromVec k hk q c0 c1 c2, pat3_congr hab hac hbc])
        (gbBinClosed k hk) hprop]
  rw [pEval_sumChoicePoly]
  simp only [binClosedChromPoly, mobU4, mobU2, pEval_mul, pEval_var, pEval_sub, pEval_add, pEval_lin]
  dsimp [evalChoiceInt, sumRangeInt, pat3]
  simp only [pEval]
  grind

theorem gb_doublyCyclic_exactChrom (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    (exactChromCount (gbDoublyCyclic k hk) q : Int) = pEval (doublyCyclicChromPoly (gbChromVec k)) (q : Int) := by
  let G := gbGraph k hk
  have hprop : ∀ c : Fin (2 ^ k) → Fin q,
      isProperColoring (gbDoublyCyclic k hk) c =
      (isProperColoring G.graph c && decide (c (G.t 0) ≠ c (G.t 1) ∧ c (G.t 0) ≠ c (G.t 2))) := by
    intro c; apply Bool.eq_iff_iff.mpr
    simp only [isProperColoring, Bool.and_eq_true, decide_eq_true_eq, gbDoublyCyclic, gbGrayClosed, addEdgeGraph, Bool.or_eq_true, beq_iff_eq]
    constructor
    · intro h
      refine ⟨fun u v huv => h u v (Or.inl (Or.inl (Or.inl (Or.inl huv)))),
              h (G.t 0) (G.t 1) (Or.inl (Or.inl (Or.inl (Or.inr ⟨rfl, rfl⟩)))),
              h (G.t 0) (G.t 2) (Or.inl (Or.inr ⟨rfl, rfl⟩))⟩
    · rintro ⟨hG, h01, h02⟩ u v ((((huv | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
      · exact hG u v huv
      · exact h01
      · exact h01.symm
      · exact h02
      · exact h02.symm
  rw [exactChrom_addTermEdge_sum G (gbChromVec k) (gbGraph_hasChromVec k hk) q
        (fun a b c => decide (a ≠ b ∧ a ≠ c))
        (fun a b c => if a ≠ b ∧ a ≠ c then gbChromVec k (pat3 a b c) else [])
        (fun c0 c1 c2 l0 l1 l2 hab hac hbc => by
          by_cases hc : c0 ≠ c1 ∧ c0 ≠ c2
          · have hc' : l0 ≠ l1 ∧ l0 ≠ l2 := ⟨mt hab.mpr hc.1, mt hac.mpr hc.2⟩
            simp [hc, hc']
            rw [gbGraph_hasChromVec k hk q c0 c1 c2, pat3_congr hab hac hbc]
          · have hc' : ¬ (l0 ≠ l1 ∧ l0 ≠ l2) := fun h => hc ⟨mt hab.mp h.1, mt hac.mp h.2⟩
            simp [hc, hc', pEval])
        (gbDoublyCyclic k hk) hprop]
  rw [pEval_sumChoicePoly]
  simp only [doublyCyclicChromPoly, mobU4, mobU2, mobU1, mobU0, pEval_mul, pEval_var, pEval_sub, pEval_add, pEval_lin]
  dsimp [evalChoiceInt, sumRangeInt, pat3]
  simp only [pEval]
  grind

-- ----------------------------------------------------------------------------
-- THEOREM 3: Exact Chromatic Number `χ(GB_k) = 3` (∀ k ≥ 2)
-- ----------------------------------------------------------------------------

theorem gb_chrom_at_two_zero (k : Nat) (hk : 2 ≤ k) :
    exactChromCount (gbGraph k hk).graph 2 = 0 := by
  -- Every `GB_k` (`k ≥ 2`) contains the triangle `{1, 2, 3}` (edges `1-2, 2-3, 1-3`), hence no 2-coloring!
  have hge4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk; omega
  have h12 : (gbGraph k hk).graph.adj ⟨1, by omega⟩ ⟨2, by omega⟩ = true := by
    simp [gbGraph, gbAdj, binAdj]
  have h23 : (gbGraph k hk).graph.adj ⟨2, by omega⟩ ⟨3, by omega⟩ = true := by
    simp [gbGraph, gbAdj, binAdj]
  have h13 : (gbGraph k hk).graph.adj ⟨1, by omega⟩ ⟨3, by omega⟩ = true := by
    simp only [gbGraph, gbAdj, grayAdj, Bool.or_eq_true, decide_eq_true_eq]
    right
    have hg1 : gray 1 = 1 := rfl
    have hg2 : gray (1 + 1) = 3 := rfl
    exact ⟨⟨1, by omega⟩, Or.inl ⟨hg1, hg2⟩⟩
  unfold exactChromCount
  have h0 : ∀ c : Fin (2 ^ k) → Fin 2, (if isProperColoring (gbGraph k hk).graph c then 1 else 0) = 0 := by
    intro c
    have hf : isProperColoring (gbGraph k hk).graph c = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      simp only [isProperColoring, decide_eq_true_eq] at h
      have a := h ⟨1, by omega⟩ ⟨2, by omega⟩ h12
      have b := h ⟨2, by omega⟩ ⟨3, by omega⟩ h23
      have d := h ⟨1, by omega⟩ ⟨3, by omega⟩ h13
      have h1 := (c ⟨1, by omega⟩).isLt
      have h2 := (c ⟨2, by omega⟩).isLt
      have h3 := (c ⟨3, by omega⟩).isLt
      have na : (c ⟨1, by omega⟩).val ≠ (c ⟨2, by omega⟩).val := fun e => a (Fin.ext e)
      have nb : (c ⟨2, by omega⟩).val ≠ (c ⟨3, by omega⟩).val := fun e => b (Fin.ext e)
      have nd : (c ⟨1, by omega⟩).val ≠ (c ⟨3, by omega⟩).val := fun e => d (Fin.ext e)
      omega
    simp [hf]
  rw [sumColorings_congr h0, sumColorings_zero_fn]

theorem gb_chrom_at_three_pos_inv (k : Nat) (hk : 3 ≤ k) :
    0 ≤ pEval (gbChromVec k 0) 3 ∧
    0 ≤ pEval (gbChromVec k 1) 3 ∧
    2 ≤ pEval (gbChromVec k 2) 3 ∧
    0 ≤ pEval (gbChromVec k 3) 3 ∧
    2 ≤ pEval (gbChromVec k 4) 3 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk3 : k = 2
    · subst hk3
      rw [gbChromVec_succ 2 (by omega)]
      simp only [pEval_stepChromPoly_gbSpec_0, pEval_stepChromPoly_gbSpec_1,
                 pEval_stepChromPoly_gbSpec_2, pEval_stepChromPoly_gbSpec_3,
                 pEval_stepChromPoly_gbSpec_4, gbBellStep0, gbBellStep1, gbBellStep2, gbBellStep3, gbBellStep4,
                 gbChromVec, gbChromBase_0, gbChromBase_1, gbChromBase_2, gbChromBase_3, gbChromBase_4,
                 pEval_lin, pEval]
      omega
    · have hkge : 3 ≤ k := by omega
      have ⟨h0, h1, h2, h3, h4⟩ := ih hkge
      rw [gbChromVec_succ k (by omega)]
      simp only [pEval_stepChromPoly_gbSpec_0, pEval_stepChromPoly_gbSpec_1,
                 pEval_stepChromPoly_gbSpec_2, pEval_stepChromPoly_gbSpec_3,
                 pEval_stepChromPoly_gbSpec_4, gbBellStep0, gbBellStep1, gbBellStep2, gbBellStep3, gbBellStep4]
      -- At q = 3, the 5 Bell step formulas are sums of non-negative products!
      generalize pEval (gbChromVec k 0) 3 = a0 at h0 ⊢
      generalize pEval (gbChromVec k 1) 3 = a1 at h1 ⊢
      generalize pEval (gbChromVec k 2) 3 = a2 at h2 ⊢
      generalize pEval (gbChromVec k 3) 3 = a3 at h3 ⊢
      generalize pEval (gbChromVec k 4) 3 = a4 at h4 ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have : 3^3*a4*a2 + 3^2*a1*a2 + 3^2*a3*a2 + 3^2*a4*a0 - 5*3^2*a4*a2 - 2*3*a1*a2 + 3*a3*a0 - 3*3*a3*a2 - 3*3*a4*a0 + 8*3*a4*a2 + a1*a2 - a3*a0 + 2*a3*a2 + 2*a4*a0 - 4*a4*a2 =
               4*(a1*a2) + 2*(a3*a0) + 2*(a3*a2) + 2*(a4*a0) + 2*(a4*a2) := by grind
        rw [this]
        have m1 : 0 ≤ a1 * a2 := Int.mul_nonneg h1 (by omega)
        have m2 : 0 ≤ a3 * a0 := Int.mul_nonneg h3 h0
        have m3 : 0 ≤ a3 * a2 := Int.mul_nonneg h3 (by omega)
        have m4 : 0 ≤ a4 * a0 := Int.mul_nonneg (by omega) h0
        have m5 : 0 ≤ a4 * a2 := Int.mul_nonneg (by omega) (by omega)
        omega
      · have : 3^3*a4*a4 + 3^2*a1*a4 + 3^2*a3*a4 + 3^2*a4*a1 + 3^2*a4*a3 - 6*3^2*a4*a4 + 3*a1*a3 - 3*3*a1*a4 + 3*a3*a1 + 3*a3*a3 - 4*3*a3*a4 - 3*3*a4*a1 - 4*3*a4*a3 + 12*3*a4*a4 - a1*a3 + 2*a1*a4 - a3*a1 - 2*a3*a3 + 4*a3*a4 + 2*a4*a1 + 4*a4*a3 - 8*a4*a4 =
               4*(a1*a3) + 4*(a1*a4) + a3*a3 + 2*(a3*a4) + a4*a4 := by grind
        rw [this]
        have m1 : 0 ≤ a1 * a3 := Int.mul_nonneg h1 h3
        have m2 : 0 ≤ a1 * a4 := Int.mul_nonneg h1 (by omega)
        have m3 : 0 ≤ a3 * a3 := Int.mul_nonneg h3 h3
        have m4 : 0 ≤ a3 * a4 := Int.mul_nonneg h3 (by omega)
        have m5 : 0 ≤ a4 * a4 := Int.mul_nonneg (by omega) (by omega)
        omega
      · have : 3^3*a4*a4 + 3^2*a1*a4 + 3^2*a2*a4 + 3^2*a3*a4 + 3^2*a4*a1 + 3^2*a4*a3 - 7*3^2*a4*a4 + 3*a0*a4 + 3*a1*a1 - 4*3*a1*a4 + 3*a2*a1 + 3*a2*a3 - 4*3*a2*a4 + 3*a3*a1 + 3*a3*a3 - 5*3*a3*a4 - 5*3*a4*a1 - 4*3*a4*a3 + 17*3*a4*a4 + a0*a1 - 2*a0*a4 - 2*a1*a1 + 4*a1*a4 - 2*a2*a1 - a2*a3 + 4*a2*a4 - 2*a3*a1 - 2*a3*a3 + 6*a3*a4 + 6*a4*a1 + 4*a4*a3 - 14*a4*a4 =
               a0*a1 + a0*a4 + a1*a1 + a1*a2 + a1*a3 + a1*a4 + a2*a4 + 2*(a2*a3) + a3*a3 + a3*a4 + a4*a4 := by grind
        rw [this]
        have m1 : 0 ≤ a0 * a1 := Int.mul_nonneg h0 h1
        have m2 : 0 ≤ a0 * a4 := Int.mul_nonneg h0 (by omega)
        have m3 : 0 ≤ a1 * a1 := Int.mul_nonneg h1 h1
        have m4 : 0 ≤ a1 * a2 := Int.mul_nonneg h1 (by omega)
        have m5 : 0 ≤ a1 * a3 := Int.mul_nonneg h1 h3
        have m6 : 0 ≤ a1 * a4 := Int.mul_nonneg h1 (by omega)
        have m7 : 4 ≤ a2 * a4 := by have := Int.mul_le_mul h2 h4 (by omega) (by omega); omega
        have m8 : 0 ≤ a2 * a3 := Int.mul_nonneg (by omega) h3
        have m9 : 0 ≤ a3 * a3 := Int.mul_nonneg h3 h3
        have m10 : 0 ≤ a3 * a4 := Int.mul_nonneg h3 (by omega)
        have m11 : 4 ≤ a4 * a4 := by have := Int.mul_le_mul h4 h4 (by omega) (by omega); omega
        omega
      · have : 3^3*a4*a2 + 3^2*a1*a2 + 3^2*a2*a2 + 3^2*a3*a2 + 3^2*a4*a0 - 6*3^2*a4*a2 + 3*a0*a2 + 3*a1*a0 - 4*3*a1*a2 + 3*a2*a0 - 3*3*a2*a2 + 3*a3*a0 - 4*3*a3*a2 - 5*3*a4*a0 + 13*3*a4*a2 + a0*a0 - 2*a0*a2 - 2*a1*a0 + 4*a1*a2 - 2*a2*a0 + 3*a2*a2 - 2*a3*a0 + 4*a3*a2 + 6*a4*a0 - 10*a4*a2 =
               a0*a0 + a0*a1 + 2*(a0*a2) + a0*a3 + a1*a2 + 3*(a2*a2) + a2*a3 + 2*(a2*a4) := by grind
        rw [this]
        have m1 : 0 ≤ a0 * a0 := Int.mul_nonneg h0 h0
        have m2 : 0 ≤ a0 * a1 := Int.mul_nonneg h0 h1
        have m3 : 0 ≤ a0 * a2 := Int.mul_nonneg h0 (by omega)
        have m4 : 0 ≤ a0 * a3 := Int.mul_nonneg h0 h3
        have m5 : 0 ≤ a1 * a2 := Int.mul_nonneg h1 (by omega)
        have m6 : 0 ≤ a2 * a2 := Int.mul_nonneg (by omega) (by omega)
        have m7 : 0 ≤ a2 * a3 := Int.mul_nonneg (by omega) h3
        have m8 : 0 ≤ a2 * a4 := Int.mul_nonneg (by omega) (by omega)
        omega
      · have : 3^3*a4*a4 + 3^2*a1*a4 + 3^2*a2*a4 + 3^2*a3*a4 + 3^2*a4*a1 + 3^2*a4*a3 - 7*3^2*a4*a4 + 3*a0*a4 + 3*a1*a1 + 3*a1*a3 - 5*3*a1*a4 + 3*a2*a1 + 3*a2*a3 - 4*3*a2*a4 + 3*a3*a1 + 3*a3*a3 - 5*3*a3*a4 - 5*3*a4*a1 - 5*3*a4*a3 + 18*3*a4*a4 + a0*a1 + a0*a3 - 3*a0*a4 - 2*a1*a1 - 2*a1*a3 + 6*a1*a4 - 2*a2*a1 - 2*a2*a3 + 5*a2*a4 - 2*a3*a1 - 3*a3*a3 + 7*a3*a4 + 6*a4*a1 + 7*a4*a3 - 17*a4*a4 =
               a0*a1 + a0*a3 + a1*a1 + a1*a2 + 2*(a1*a3) + 2*(a2*a4) + a2*a3 + 2*(a3*a4) + a4*a4 := by grind
        rw [this]
        have m1 : 0 ≤ a0 * a1 := Int.mul_nonneg h0 h1
        have m2 : 0 ≤ a0 * a3 := Int.mul_nonneg h0 h3
        have m3 : 0 ≤ a1 * a1 := Int.mul_nonneg h1 h1
        have m4 : 0 ≤ a1 * a2 := Int.mul_nonneg h1 (by omega)
        have m5 : 0 ≤ a1 * a3 := Int.mul_nonneg h1 h3
        have m6 : 4 ≤ a2 * a4 := by have := Int.mul_le_mul h2 h4 (by omega) (by omega); omega
        have m7 : 0 ≤ a2 * a3 := Int.mul_nonneg (by omega) h3
        have m8 : 0 ≤ a3 * a4 := Int.mul_nonneg h3 (by omega)
        have m9 : 4 ≤ a4 * a4 := by have := Int.mul_le_mul h4 h4 (by omega) (by omega); omega
        omega

/-- **THEOREM 3 (Exact Chromatic Number `χ(GB_k) = 3` ∀ `k ≥ 2`)**:
    For every `k ≥ 2`, `GB_k` admits no proper 2-coloring (`P(GB_k, 2) = 0`) and admits at least
    `12` proper 3-colorings (`P(GB_k, 3) ≥ 12 > 0`). -/
theorem gb_chromatic_number_three (k : Nat) (hk : 2 ≤ k) :
    exactChromCount (gbGraph k hk).graph 2 = 0 ∧ 12 ≤ exactChromCount (gbGraph k hk).graph 3 := by
  refine ⟨gb_chrom_at_two_zero k hk, ?_⟩
  have hcast := gbGraph_exactChrom k hk 3
  rw [gbChromPoly, pEval_totalChromPoly] at hcast
  have h3 : ((3 : Nat) : Int) = 3 := rfl
  rw [h3] at hcast
  by_cases hk2 : k = 2
  · subst hk2
    simp only [gbChromVec, mobU4, gbChromBase_0, gbChromBase_1, gbChromBase_2, gbChromBase_3, gbChromBase_4,
               pEval_add, pEval_mul, pEval_lin, pEval] at hcast
    omega
  · have ⟨h0, h1, h2, h3', h4⟩ := gb_chrom_at_three_pos_inv k (by omega)
    simp only [mobU4, pEval_add, pEval_mul, pEval_lin] at hcast
    omega

-- ----------------------------------------------------------------------------
-- THEOREM 4: Quartet of Exact Power-of-Two Crapo Beta Invariants at `q = 1`
-- ----------------------------------------------------------------------------

/-- Exact closed-form Möbius polynomials of `GB_3` (`k = 3`), shared by Theorems 4 and 5! -/
theorem gb3_mobius_exact :
    (∀ q : Int, pEval (mobU0 (gbChromVec 3)) q = (q - 2) ^ 2 * (q - 1) * (q ^ 2 - 4 * q + 5)) ∧
    (∀ q : Int, pEval (mobU1 (gbChromVec 3)) q = (q - 2) ^ 2 * (q - 1) * (q ^ 3 - 5 * q ^ 2 + 9 * q - 7)) ∧
    (∀ q : Int, pEval (mobU2 (gbChromVec 3)) q = (q - 2) * (q - 1) * (q ^ 4 - 7 * q ^ 3 + 20 * q ^ 2 - 29 * q + 19)) ∧
    (∀ q : Int, pEval (mobU3 (gbChromVec 3)) q = (q - 2) ^ 2 * (q - 1) ^ 2 * (q ^ 2 - 3 * q + 3)) ∧
    (∀ q : Int, pEval (mobU4 (gbChromVec 3)) q = (q - 2) ^ 3 * (q - 1) ^ 2 * (q ^ 2 - 2 * q + 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hc := pEval_cancel_lin (mobU0 (gbChromVec 3)) (pMul (pLinPow 2 2) (pMul (pLin 1) [5, -4, 1])) 1 (fun q => by
      rw [gbChromVec_succ 2 (by omega), mobius_step_0]
      simp only [gbChromVec, mobU0, mobU1, mobU2, mobU4, gbChromBase_0, gbChromBase_1, gbChromBase_2, gbChromBase_3, gbChromBase_4,
                 pEval_add, pEval_mul, pEval_lin, pEval_linPow, pEval]
      grind)
    intro q; have hq := hc q; simp only [pEval_mul, pEval_lin, pEval_linPow, pEval] at hq; grind
  · have hc := pEval_cancel_lin (mobU1 (gbChromVec 3)) (pMul (pLinPow 2 2) (pMul (pLin 1) [-7, 9, -5, 1])) 1 (fun q => by
      rw [gbChromVec_succ 2 (by omega), mobius_step_1]
      simp only [gbChromVec, mobU0, mobU1, mobU2, mobU4, gbChromBase_0, gbChromBase_1, gbChromBase_2, gbChromBase_3, gbChromBase_4,
                 pEval_add, pEval_mul, pEval_lin, pEval_linPow, pEval]
      grind)
    intro q; have hq := hc q; simp only [pEval_mul, pEval_lin, pEval_linPow, pEval] at hq; grind
  · let rhs2 : Poly := pMul (pLin 2) (pMul (pLin 1) [19, -29, 20, -7, 1])
    have hc1 := pEval_cancel_lin (pMul (pLin 2) (mobU2 (gbChromVec 3))) (pMul (pLin 2) rhs2) 1 (fun q => by
      simp only [pEval_mul, pEval_lin]
      have hm := mobius_step_2 (gbChromVec 2) q
      rw [← gbChromVec_succ 2 (by omega)] at hm
      simp only [gbChromVec, mobU0, mobU1, mobU2, mobU3, mobU4, gbChromBase_0, gbChromBase_1, gbChromBase_2, gbChromBase_3, gbChromBase_4, rhs2,
                 pEval_add, pEval_mul, pEval_lin, pEval] at hm ⊢
      grind)
    have hc2 := pEval_cancel_lin (mobU2 (gbChromVec 3)) rhs2 2 (fun q => by
      simpa [pEval_mul, pEval_lin] using hc1 q)
    intro q; have hq := hc2 q; simp only [rhs2, pEval_mul, pEval_lin, pEval] at hq; grind
  · have hc := pEval_cancel_lin (mobU3 (gbChromVec 3)) (pMul (pLinPow 2 2) (pMul (pLinPow 1 2) [3, -3, 1])) 1 (fun q => by
      rw [gbChromVec_succ 2 (by omega), mobius_step_3]
      simp only [gbChromVec, mobU0, mobU2, mobU3, mobU4, gbChromBase_0, gbChromBase_1, gbChromBase_2, gbChromBase_3, gbChromBase_4,
                 pEval_add, pEval_mul, pEval_lin, pEval_linPow, pEval]
      grind)
    intro q; have hq := hc q; simp only [pEval_mul, pEval_linPow, pEval] at hq; grind
  · have hc := pEval_cancel_lin (mobU4 (gbChromVec 3)) (pMul (pLinPow 2 3) (pMul (pLinPow 1 2) [2, -2, 1])) 1 (fun q => by
      rw [gbChromVec_succ 2 (by omega), mobius_step_4]
      simp only [gbChromVec, mobU1, mobU3, mobU4, gbChromBase_0, gbChromBase_1, gbChromBase_2, gbChromBase_3, gbChromBase_4,
                 pEval_add, pEval_mul, pEval_lin, pEval_linPow, pEval]
      grind)
    intro q; have hq := hc q; simp only [pEval_mul, pEval_linPow, pEval] at hq; grind

/-- Helper: if `(q - 1) * T(q) = (q - 2)^d * Q(q)` for all `q : Int`, then since `q - 1 = 1 + (q - 2)`
    is a unit at `q = 2`, `HasLeadAt T 2 d (Q(2))`. -/
theorem hasLeadAt_two_of_unit_mul (d : Nat) (T Q : Poly)
    (hTQ : ∀ q : Int, (q - 1) * pEval T q = (q - 2) ^ d * pEval Q q) :
    HasLeadAt T 2 d (pEval Q 2) := by
  induction d generalizing T Q with
  | zero =>
    have h2 : pEval T 2 = pEval Q 2 := by have := hTQ 2; omega
    refine ⟨pQuotLin T 2, fun q => ?_⟩
    have := pEval_horner T 2 q; rw [h2] at this; grind
  | succ d ihd =>
    have hT2 : pEval T 2 = 0 := by
      have := hTQ 2
      simp only [Int.sub_self, Int.pow_succ, Int.mul_zero, Int.zero_mul] at this
      omega
    let T' := pQuotLin T 2
    have hT_eq : ∀ q : Int, pEval T q = (q - 2) * pEval T' q := fun q => by
      have := pEval_horner T 2 q; rw [hT2] at this; grind
    have hT'_Q : ∀ q : Int, (q - 1) * pEval T' q = (q - 2) ^ d * pEval Q q := by
      have hc := pEval_cancel_lin (pMul (pLin 1) T') (pMul (pLinPow 2 d) Q) 2 (fun q => by
        simp only [pEval_mul, pEval_lin, pEval_linPow]
        have h1 := hTQ q; rw [hT_eq q, Int.pow_succ] at h1; grind)
      intro q; simpa [pEval_mul, pEval_lin, pEval_linPow] using hc q
    rcases ihd T' Q hT'_Q with ⟨R, hR⟩
    refine ⟨R, fun q => ?_⟩
    rw [hT_eq q, hR q, Int.pow_succ, Int.pow_succ]; grind

/-- Exact 5-state Möbius leading-term invariant at `q = 1` for all `k ≥ 3`. -/
theorem gb_mobius_lead_at_one (k : Nat) (hk : 3 ≤ k) :
    HasLeadAt (mobU0 (gbChromVec k)) 1 1 (((2 : Int) ^ (k - 2) - 1) * (2 : Int) ^ (2 ^ (k - 1) - k)) ∧
    HasLeadAt (mobU1 (gbChromVec k)) 1 1 (-((2 : Int) ^ (2 ^ (k - 1) - k))) ∧
    HasLeadAt (mobU2 (gbChromVec k)) 1 1 (-((2 : Int) ^ (2 ^ (k - 1) - 2))) ∧
    HasLeadAt (mobU3 (gbChromVec k)) 1 2 (((2 : Int) ^ (k - 2) - 1) * (2 : Int) ^ (2 ^ (k - 1) + 2 - 2 * k)) ∧
    HasLeadAt (mobU4 (gbChromVec k)) 1 2 (-((2 : Int) ^ (2 ^ (k - 1) + 2 - 2 * k))) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk3 : k = 2
    · subst hk3
      rcases gb3_mobius_exact with ⟨h0, h1, h2, h3, h4⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · let A0 : Poly := pMul (pLinPow 2 2) [5, -4, 1]
        have hA0 : ∀ q, pEval A0 q = (q - 2) ^ 2 * (q ^ 2 - 4 * q + 5) := fun q => by
          simp only [A0, pEval_mul, pEval_linPow, pEval]; grind
        refine ⟨pQuotLin A0 1, fun q => ?_⟩
        have hq := pEval_horner A0 1 q
        rw [hA0 1] at hq
        rw [h0 q]; have := hA0 q; grind
      · let A1 : Poly := pMul (pLinPow 2 2) [-7, 9, -5, 1]
        have hA1 : ∀ q, pEval A1 q = (q - 2) ^ 2 * (q ^ 3 - 5 * q ^ 2 + 9 * q - 7) := fun q => by
          simp only [A1, pEval_mul, pEval_linPow, pEval]; grind
        refine ⟨pQuotLin A1 1, fun q => ?_⟩
        have hq := pEval_horner A1 1 q
        rw [hA1 1] at hq
        rw [h1 q]; have := hA1 q; grind
      · let A2 : Poly := pMul (pLin 2) [19, -29, 20, -7, 1]
        have hA2 : ∀ q, pEval A2 q = (q - 2) * (q ^ 4 - 7 * q ^ 3 + 20 * q ^ 2 - 29 * q + 19) := fun q => by
          simp only [A2, pEval_mul, pEval_lin, pEval]; grind
        refine ⟨pQuotLin A2 1, fun q => ?_⟩
        have hq := pEval_horner A2 1 q
        rw [hA2 1] at hq
        rw [h2 q]; have := hA2 q; grind
      · let A3 : Poly := pMul (pLinPow 2 2) [3, -3, 1]
        have hA3 : ∀ q, pEval A3 q = (q - 2) ^ 2 * (q ^ 2 - 3 * q + 3) := fun q => by
          simp only [A3, pEval_mul, pEval_linPow, pEval]; grind
        refine ⟨pQuotLin A3 1, fun q => ?_⟩
        have hq := pEval_horner A3 1 q
        rw [hA3 1] at hq
        rw [h3 q]; have := hA3 q; grind
      · let A4 : Poly := pMul (pLinPow 2 3) [2, -2, 1]
        have hA4 : ∀ q, pEval A4 q = (q - 2) ^ 3 * (q ^ 2 - 2 * q + 2) := fun q => by
          simp only [A4, pEval_mul, pEval_linPow, pEval]; grind
        refine ⟨pQuotLin A4 1, fun q => ?_⟩
        have hq := pEval_horner A4 1 q
        rw [hA4 1] at hq
        rw [h4 q]; have := hA4 q; grind
    · have hkge : 3 ≤ k := by omega
      rcases ih hkge with ⟨⟨r0, hr0⟩, ⟨r1, hr1⟩, ⟨r2, hr2⟩, ⟨r3, hr3⟩, ⟨r4, hr4⟩⟩
      -- Exponent arithmetic for `k ≥ 3`
      have hpow_ge : 2 * k ≤ 2 ^ (k - 1) + 2 := by
        -- Prove `2 * n ≤ 2 ^ (n - 1) + 2` for `n ≥ 3` by induction!
        have aux : ∀ m : Nat, 2 * (m + 3) ≤ 2 ^ (m + 2) + 2 := by
          intro m; induction m with
          | zero => decide
          | succ m ihm =>
            have : 2 ^ (m + 1 + 2) = 2 ^ (m + 2) * 2 := by
              rw [show m + 1 + 2 = (m + 2) + 1 by omega, Nat.pow_succ]
            omega
        have := aux (k - 3)
        rwa [show k - 3 + 3 = k by omega, show k - 3 + 2 = k - 1 by omega] at this
      have hk_le_pow : k ≤ 2 ^ (k - 1) := by omega
      have h2_le_pow : 2 ≤ 2 ^ (k - 1) := by omega
      have hpow_succ : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
        have h1 : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
        omega
      -- Abbreviate the 5 leading coefficients
      let c0 : Int := ((2 : Int) ^ (k - 2) - 1) * (2 : Int) ^ (2 ^ (k - 1) - k)
      let c1 : Int := -((2 : Int) ^ (2 ^ (k - 1) - k))
      let c2 : Int := -((2 : Int) ^ (2 ^ (k - 1) - 2))
      let c3 : Int := ((2 : Int) ^ (k - 2) - 1) * (2 : Int) ^ (2 ^ (k - 1) + 2 - 2 * k)
      let c4 : Int := -((2 : Int) ^ (2 ^ (k - 1) + 2 - 2 * k))
      have hc0_rel : c0 = c1 - c2 := by
        dsimp only [c0, c1, c2]
        have hsplit : (2 : Int) ^ (2 ^ (k - 1) - 2) = (2 : Int) ^ (k - 2) * (2 : Int) ^ (2 ^ (k - 1) - k) := by
          rw [← Int.pow_add]; congr 1; omega
        rw [hsplit]; grind
      have hc3_sub_c4 : c3 - c4 = (2 : Int) ^ (2 ^ (k - 1) - k) := by
        dsimp only [c3, c4]
        have hsplit : (2 : Int) ^ (k - 2) * (2 : Int) ^ (2 ^ (k - 1) + 2 - 2 * k) = (2 : Int) ^ (2 ^ (k - 1) - k) := by
          rw [← Int.pow_add]; congr 1; omega
        grind
      have hnew0 : 2 * c2 * (2 * c2 - c1) = ((2 : Int) ^ (k + 1 - 2) - 1) * (2 : Int) ^ (2 ^ k - (k + 1)) := by
        dsimp only [c1, c2]
        have h1 : (2 : Int) ^ (k + 1 - 2) = 2 * (2 : Int) ^ (k - 2) := by
          rw [show k + 1 - 2 = (k - 2) + 1 by omega, Int.pow_succ]; grind
        have h2 : (2 : Int) ^ (2 ^ (k - 1) - 2) = (2 : Int) ^ (k - 2) * (2 : Int) ^ (2 ^ (k - 1) - k) := by
          rw [← Int.pow_add]; congr 1; omega
        have h3 : 2 * (2 : Int) ^ (2 ^ (k - 1) - 2) * (2 : Int) ^ (2 ^ (k - 1) - k) = (2 : Int) ^ (2 ^ k - (k + 1)) := by
          have : (2 : Int) ^ (2 ^ k - (k + 1)) = 2 ^ 1 * ((2 : Int) ^ (2 ^ (k - 1) - 2) * (2 : Int) ^ (2 ^ (k - 1) - k)) := by
            rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          grind
        grind
      have hnew1 : -2 * c1 * c2 = -((2 : Int) ^ (2 ^ k - (k + 1))) := by
        dsimp only [c1, c2]
        have : 2 * ((2 : Int) ^ (2 ^ (k - 1) - k) * (2 : Int) ^ (2 ^ (k - 1) - 2)) = (2 : Int) ^ (2 ^ k - (k + 1)) := by
          have : (2 : Int) ^ (2 ^ k - (k + 1)) = 2 ^ 1 * ((2 : Int) ^ (2 ^ (k - 1) - k) * (2 : Int) ^ (2 ^ (k - 1) - 2)) := by
            rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          grind
        grind
      have hnew2 : -4 * c2 ^ 2 = -((2 : Int) ^ (2 ^ k - 2)) := by
        dsimp only [c2]
        have : 4 * ((2 : Int) ^ (2 ^ (k - 1) - 2)) ^ 2 = (2 : Int) ^ (2 ^ k - 2) := by
          have : (2 : Int) ^ (2 ^ k - 2) = (2 : Int) ^ 2 * ((2 : Int) ^ (2 ^ (k - 1) - 2) * (2 : Int) ^ (2 ^ (k - 1) - 2)) := by
            rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          grind
        grind
      have hnew3 : (c0 - c2) * (c3 - c4) = ((2 : Int) ^ (k + 1 - 2) - 1) * (2 : Int) ^ (2 ^ k + 2 - 2 * (k + 1)) := by
        rw [hc0_rel, hc3_sub_c4]
        dsimp only [c1, c2]
        have h1 : (2 : Int) ^ (k + 1 - 2) = 2 * (2 : Int) ^ (k - 2) := by
          rw [show k + 1 - 2 = (k - 2) + 1 by omega, Int.pow_succ]; grind
        have h2 : (2 : Int) ^ (2 ^ (k - 1) - 2) = (2 : Int) ^ (k - 2) * (2 : Int) ^ (2 ^ (k - 1) - k) := by
          rw [← Int.pow_add]; congr 1; omega
        have h3 : (2 : Int) ^ (2 ^ (k - 1) - k) * (2 : Int) ^ (2 ^ (k - 1) - k) = (2 : Int) ^ (2 ^ k + 2 - 2 * (k + 1)) := by
          rw [← Int.pow_add]; congr 1; omega
        grind
      have hnew4 : c1 * (c3 - c4) = -((2 : Int) ^ (2 ^ k + 2 - 2 * (k + 1))) := by
        rw [hc3_sub_c4]
        dsimp only [c1]
        have h3 : (2 : Int) ^ (2 ^ (k - 1) - k) * (2 : Int) ^ (2 ^ (k - 1) - k) = (2 : Int) ^ (2 ^ k + 2 - 2 * (k + 1)) := by
          rw [← Int.pow_add]; congr 1; omega
        grind
      -- Express each `(u_i k)` as `e * P_i` where `P_i = c_i + e * r_i` (`e = q - 1`), and verify the 5 steps!
      let E := pLin 1
      let P0 := pAdd (pConst c0) (pMul E r0)
      let P1 := pAdd (pConst c1) (pMul E r1)
      let P2 := pAdd (pConst c2) (pMul E r2)
      let P3 := pAdd (pConst c3) (pMul E r3)
      let P4 := pAdd (pConst c4) (pMul E r4)
      have hE : ∀ q, pEval E q = q - 1 := pEval_lin 1
      have hU0 : ∀ q, pEval (mobU0 (gbChromVec k)) q = (q - 1) * pEval P0 q := fun q => by
        rw [hr0 q]; simp [P0, pEval_add, pEval_const, pEval_mul, hE]; grind
      have hU1 : ∀ q, pEval (mobU1 (gbChromVec k)) q = (q - 1) * pEval P1 q := fun q => by
        rw [hr1 q]; simp [P1, pEval_add, pEval_const, pEval_mul, hE]; grind
      have hU2 : ∀ q, pEval (mobU2 (gbChromVec k)) q = (q - 1) * pEval P2 q := fun q => by
        rw [hr2 q]; simp [P2, pEval_add, pEval_const, pEval_mul, hE]; grind
      have hU3 : ∀ q, pEval (mobU3 (gbChromVec k)) q = (q - 1)^2 * pEval P3 q := fun q => by
        rw [hr3 q]; simp [P3, pEval_add, pEval_const, pEval_mul, hE]; grind
      have hU4 : ∀ q, pEval (mobU4 (gbChromVec k)) q = (q - 1)^2 * pEval P4 q := fun q => by
        rw [hr4 q]; simp [P4, pEval_add, pEval_const, pEval_mul, hE]; grind
      -- Helper: any polynomial `Q` satisfies `pEval Q q = pEval Q 1 + (q - 1) * pEval (pQuotLin Q 1) q`!
      have hstep_lead1 : ∀ (target : Poly) (Q : Poly) (c : Int),
          (∀ q : Int, (q - 1) * pEval target q = (q - 1) ^ 2 * pEval Q q) →
          pEval Q 1 = c → HasLeadAt target 1 1 c := by
        intro target Q c hQ hc
        apply hasLeadAt_of_cancel
        refine ⟨pQuotLin Q 1, fun q => ?_⟩
        rw [hQ q, pEval_horner Q 1 q, hc]; grind
      have hstep_lead2 : ∀ (target : Poly) (Q : Poly) (c : Int),
          (∀ q : Int, (q - 1) * pEval target q = (q - 1) ^ 3 * pEval Q q) →
          pEval Q 1 = c → HasLeadAt target 1 2 c := by
        intro target Q c hQ hc
        apply hasLeadAt_of_cancel
        refine ⟨pQuotLin Q 1, fun q => ?_⟩
        rw [hQ q, pEval_horner Q 1 q, hc]; grind
      rw [gbChromVec_succ k (by omega)]
      simp only [show k + 1 - 1 = k by omega]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- u0'
        let Q0 := pAdd (pMul pVar (pMul P0 P0))
                  (pAdd (pMul P0 (pAdd (pSub (pNeg (pMul pVar P1)) (pScale 2 P2)) (pMul E P4)))
                  (pAdd (pMul P1 P2)
                  (pAdd (pMul (pSub (pConst 2) pVar) (pMul P2 P2))
                        (pMul (pLin 2) (pMul E (pMul P2 P4))))))
        apply hstep_lead1 _ Q0 _
        · intro q; rw [mobius_step_0, hU0 q, hU1 q, hU2 q, hU4 q]
          simp only [Q0, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, hE]
          grind
        · simp only [Q0, P0, P1, P2, P4, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, hE]
          grind
      · -- u1'
        let Q1 := pAdd (pNeg (pMul pVar (pMul P1 P1)))
                  (pAdd (pMul P0 (pSub (pMul pVar P1) (pMul E P4)))
                  (pAdd (pMul P1 (pAdd (pNeg P2) (pScale 2 (pMul E P4))))
                  (pAdd (pMul (pSub (pConst 2) pVar) (pMul E (pMul P2 P4)))
                        (pMul (pLin 2) (pMul E (pMul E (pMul P4 P4)))))))
        apply hstep_lead1 _ Q1 _
        · intro q; rw [mobius_step_1, hU0 q, hU1 q, hU2 q, hU4 q]
          simp only [Q1, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, hE]
          grind
        · simp only [Q1, P0, P1, P2, P4, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, hE]
          grind
      · -- u2' (cancel `(q - 2)` and `(q - 1)`!)
        let Q2 := pAdd (pMul (pMul pVar pVar) (pMul P0 P0))
                  (pAdd (pMul P0 (pAdd (pSub (pSub (pScale (-2) (pMul pVar P1)) (pScale 2 (pMul pVar P2)))
                                             (pScale 2 (pMul pVar (pMul E P3))))
                                       (pScale 4 (pMul E P4))))
                  (pAdd (pMul P1 P1)
                  (pAdd (pMul P1 (pAdd (pMul (pAdd (pNeg (pMul pVar pVar)) (pAdd (pScale 4 pVar) (pConst (-2)))) (pMul E P3))
                                 (pAdd (pMul (pLin 4) (pMul E P4)) (pScale 2 P2))))
                  (pAdd (pMul (pAdd (pNeg (pMul pVar pVar)) (pAdd (pScale 3 pVar) (pConst (-1)))) (pMul P2 P2))
                  (pAdd (pMul P2 (pAdd (pScale 2 (pMul (pLin 3) (pMul E P4))) (pScale 2 (pMul E P3))))
                  (pAdd (pMul E (pMul E (pMul P3 P3)))
                  (pAdd (pMul (pLin 4) (pMul E (pMul E (pMul P3 P4))))
                        (pMul (pAdd (pMul pVar pVar) (pAdd (pScale (-5) pVar) (pConst 7))) (pMul E (pMul E (pMul P4 P4)))))))))))
        -- At q = 1: pEval Q2 1 = (c0 - c1 - c2)^2 = 4 * c2^2.
        -- (q - 2) * (q - 1) * pEval (mobU2 v') q = (q - 1)^2 * pEval Q2 q; cancelling (q - 1) gives
        -- (q - 2) * pEval (mobU2 v') q = (q - 1) * pEval Q2 q.
        -- At q = 1 this forces pEval (mobU2 v') 1 = 0, so pEval (mobU2 v') q = (q - 1) * pEval R q
        -- with R = pQuotLin (mobU2 v') 1, and (q - 2) * pEval R q = pEval Q2 q.
        -- At q = 1: (-1) * pEval R 1 = pEval Q2 1 = 4 * c2^2, hence pEval R 1 = -4 * c2^2.
        -- By pEval_horner R 1 q: pEval (mobU2 v') q = (q - 1) * (-4 * c2^2 + (q - 1) * pEval (pQuotLin R 1) q),
        -- so no (q - 2)-quotient is needed.
        have hQ2_eq : ∀ q : Int, (q - 2) * ((q - 1) * pEval (mobU2 (stepChromPoly gbSpec (gbChromVec k) (gbChromVec k))) q) =
            (q - 1) ^ 2 * pEval Q2 q := by
          intro q; rw [mobius_step_2, hU0 q, hU1 q, hU2 q, hU3 q, hU4 q]
          simp only [Q2, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, hE]
          grind
        have hstep1 : ∀ q : Int,
            pEval (pMul (pLin 2) (mobU2 (stepChromPoly gbSpec (gbChromVec k) (gbChromVec k)))) q =
            pEval (pMul E Q2) q := by
          apply pEval_cancel_lin _ _ 1
          intro q
          simp only [pEval_mul, pEval_lin, hE]
          have := hQ2_eq q; grind
        have hu2_at1 : pEval (mobU2 (stepChromPoly gbSpec (gbChromVec k) (gbChromVec k))) 1 = 0 := by
          have := hstep1 1
          simp only [pEval_mul, pEval_lin, hE] at this
          omega
        let R := pQuotLin (mobU2 (stepChromPoly gbSpec (gbChromVec k) (gbChromVec k))) 1
        have hR_eq : ∀ q : Int, pEval (mobU2 (stepChromPoly gbSpec (gbChromVec k) (gbChromVec k))) q = (q - 1) * pEval R q := by
          intro q
          have := pEval_horner (mobU2 (stepChromPoly gbSpec (gbChromVec k) (gbChromVec k))) 1 q
          rw [hu2_at1] at this; grind
        have hR_Q2 : ∀ q : Int, pEval (pMul (pLin 2) R) q = pEval Q2 q := by
          apply pEval_cancel_lin _ _ 1
          intro q
          have := hstep1 q
          simp only [pEval_mul, pEval_lin, hE, hR_eq q] at this ⊢
          grind
        have hR_at1 : pEval R 1 = -((2 : Int) ^ (2 ^ k - 2)) := by
          have h1 := hR_Q2 1
          simp only [pEval_mul, pEval_lin, Q2, P0, P1, P2, P3, P4, pEval_add, pEval_sub, pEval_neg,
                     pEval_scale, pEval_const, pEval_var, hE] at h1
          grind
        refine ⟨pQuotLin R 1, fun q => ?_⟩
        rw [hR_eq q, pEval_horner R 1 q, hR_at1]; grind
      · -- u3'
        let Q3 := pAdd (pMul P0 (pSub (pMul pVar P3) P4))
                       (pMul P2 (pSub (pMul (pAdd (pMul pVar pVar) (pAdd (pScale (-3) pVar) (pConst 3))) P4) P3))
        apply hstep_lead2 _ Q3 _
        · intro q; rw [mobius_step_3, hU0 q, hU2 q, hU3 q, hU4 q]
          simp only [Q3, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var]
          grind
        · simp only [Q3, P0, P2, P3, P4, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, hE]
          grind
      · -- u4'
        let Q4 := pAdd (pMul P1 (pSub (pMul pVar P3) P4))
                       (pMul (pMul E P4) (pSub (pMul (pAdd (pMul pVar pVar) (pAdd (pScale (-3) pVar) (pConst 3))) P4) P3))
        apply hstep_lead2 _ Q4 _
        · intro q; rw [mobius_step_4, hU1 q, hU3 q, hU4 q]
          simp only [Q4, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, hE]
          grind
        · simp only [Q4, P1, P3, P4, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, hE]
          grind

/-- **THEOREM 4 (Quartet of Exact Power-of-Two Crapo Beta Invariants ∀ `k ≥ 3`)**:
    Across all 4 boundary closures of `GB_k`, the leading `(q - 1)`-Taylor coefficient of the
    exact chromatic polynomial is an exact power of two:
    1. Open `GB_k`:             `P(q) = -2^(2^(k-1) - 2k + 2) * (q - 1)^2 + O((q - 1)^3)`
    2. Gray-closed:             `P(q) = +2^(2^(k-1) - k)      * (q - 1)   + O((q - 1)^2)`
    3. Binary-closed:           `P(q) = +2^(2^(k-1) - 2)      * (q - 1)   + O((q - 1)^2)`
    4. Doubly-cyclic `GB_k^oo`: `P(q) = +2^(2^(k-1) - 1)      * (q - 1)   + O((q - 1)^2)`! -/
theorem gb_crapo_beta_quartet (k : Nat) (hk : 3 ≤ k) :
    HasLeadAt (gbChromPoly k) 1 2 (-((2 : Int) ^ (2 ^ (k - 1) + 2 - 2 * k))) ∧
    HasLeadAt (grayClosedChromPoly (gbChromVec k)) 1 1 ((2 : Int) ^ (2 ^ (k - 1) - k)) ∧
    HasLeadAt (binClosedChromPoly (gbChromVec k)) 1 1 ((2 : Int) ^ (2 ^ (k - 1) - 2)) ∧
    HasLeadAt (doublyCyclicChromPoly (gbChromVec k)) 1 1 ((2 : Int) ^ (2 ^ (k - 1) - 1)) := by
  rcases gb_mobius_lead_at_one k hk with ⟨⟨r0, hr0⟩, ⟨r1, hr1⟩, ⟨r2, hr2⟩, _, ⟨r4, hr4⟩⟩
  have h2_le : 2 ≤ 2 ^ (k - 1) := by
    have : 2 ^ 2 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega); omega
  have hpow_ge : 2 * k ≤ 2 ^ (k - 1) + 2 := by
    have aux : ∀ m : Nat, 2 * (m + 3) ≤ 2 ^ (m + 2) + 2 := by
      intro m; induction m with
      | zero => decide
      | succ m ihm =>
        have : 2 ^ (m + 1 + 2) = 2 ^ (m + 2) * 2 := by
          rw [show m + 1 + 2 = (m + 2) + 1 by omega, Nat.pow_succ]
        omega
    have := aux (k - 3)
    rwa [show k - 3 + 3 = k by omega, show k - 3 + 2 = k - 1 by omega] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Open: `q * u4 = (1 + (q-1)) * (c4 * (q-1)^2 + (q-1)^3 * r4)`
    refine ⟨pAdd (pConst (-((2 : Int) ^ (2 ^ (k - 1) + 2 - 2 * k)))) (pMul pVar r4), fun q => ?_⟩
    rw [gbChromPoly, pEval_totalChromPoly, hr4 q]
    simp only [pEval_add, pEval_const, pEval_mul, pEval_var]
    grind
  · -- Gray-closed: `q * (u4 - u1)`
    refine ⟨pAdd (pConst ((2 : Int) ^ (2 ^ (k - 1) - k)))
                 (pMul pVar (pSub (pAdd (pConst (-((2 : Int) ^ (2 ^ (k - 1) + 2 - 2 * k)))) (pMul (pLin 1) r4)) r1)), fun q => ?_⟩
    simp only [grayClosedChromPoly, pEval_mul, pEval_var, pEval_sub, pEval_add, pEval_const, pEval_lin, hr4 q, hr1 q]
    grind
  · -- Binary-closed: `q * (u4 - u2)`
    refine ⟨pAdd (pConst ((2 : Int) ^ (2 ^ (k - 1) - 2)))
                 (pMul pVar (pSub (pAdd (pConst (-((2 : Int) ^ (2 ^ (k - 1) + 2 - 2 * k)))) (pMul (pLin 1) r4)) r2)), fun q => ?_⟩
    simp only [binClosedChromPoly, pEval_mul, pEval_var, pEval_sub, pEval_add, pEval_const, pEval_lin, hr4 q, hr2 q]
    grind
  · -- Doubly-cyclic: `q * (u4 - u1 - u2 + u0)`
    have hsum_c : ((2 : Int) ^ (k - 2) - 1) * (2 : Int) ^ (2 ^ (k - 1) - k) +
                  (2 : Int) ^ (2 ^ (k - 1) - k) + (2 : Int) ^ (2 ^ (k - 1) - 2) =
                  (2 : Int) ^ (2 ^ (k - 1) - 1) := by
      have h1 : (2 : Int) ^ (2 ^ (k - 1) - 2) = (2 : Int) ^ (k - 2) * (2 : Int) ^ (2 ^ (k - 1) - k) := by
        rw [← Int.pow_add]; congr 1; omega
      have h2 : (2 : Int) ^ (2 ^ (k - 1) - 1) = 2 * (2 : Int) ^ (2 ^ (k - 1) - 2) := by
        rw [show 2 ^ (k - 1) - 1 = (2 ^ (k - 1) - 2) + 1 by omega, Int.pow_succ]; grind
      grind
    refine ⟨pAdd (pConst ((2 : Int) ^ (2 ^ (k - 1) - 1)))
                 (pMul pVar (pAdd (pSub (pSub (pAdd (pConst (-((2 : Int) ^ (2 ^ (k - 1) + 2 - 2 * k)))) (pMul (pLin 1) r4)) r1) r2) r0)), fun q => ?_⟩
    simp only [doublyCyclicChromPoly, pEval_mul, pEval_var, pEval_sub, pEval_add, pEval_const, pEval_lin,
               hr4 q, hr1 q, hr2 q, hr0 q]
    grind

-- ----------------------------------------------------------------------------
-- THEOREM 5: Exact Linear `(q - 2)`-Multiplicity `2k - 4` with Constant Lead `-4` (∀ k ≥ 4)
-- ----------------------------------------------------------------------------

/-- Exact 5-state Möbius valuation & leading-term invariant at `q = 2` for all `k ≥ 4`. -/
theorem gb_mobius_lead_at_two (k : Nat) (hk : 4 ≤ k) :
    HasOrderGe (mobU0 (gbChromVec k)) 2 3 ∧
    HasLeadAt (mobU1 (gbChromVec k)) 2 (k - 1) ((-1 : Int) ^ k) ∧
    HasLeadAt (mobU2 (gbChromVec k)) 2 1 1 ∧
    HasLeadAt (mobU3 (gbChromVec k)) 2 (k - 1) ((-1 : Int) ^ (k - 1)) ∧
    HasLeadAt (mobU4 (gbChromVec k)) 2 (2 * k - 4) (-2) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk4 : k = 3
    · subst hk4
      rcases gb3_mobius_exact with ⟨h3_0, h3_1, h3_2, h3_3, h3_4⟩
      let E := pLin 2
      have hE : ∀ q, pEval E q = q - 2 := pEval_lin 2
      let A0 : Poly := pMul (pLin 1) [5, -4, 1]
      let A1 : Poly := pMul (pLin 1) [-7, 9, -5, 1]
      let A2 : Poly := pMul (pLin 1) [19, -29, 20, -7, 1]
      let A3 : Poly := pMul (pLinPow 1 2) [3, -3, 1]
      let A4 : Poly := pMul (pLinPow 1 2) [2, -2, 1]
      have hU0 : ∀ q, pEval (mobU0 (gbChromVec 3)) q = (q - 2) ^ 2 * pEval A0 q := fun q => by
        rw [h3_0 q]; simp [A0, pEval_mul, pEval_lin, pEval]; grind
      have hU1 : ∀ q, pEval (mobU1 (gbChromVec 3)) q = (q - 2) ^ 2 * pEval A1 q := fun q => by
        rw [h3_1 q]; simp [A1, pEval_mul, pEval_lin, pEval]; grind
      have hU2 : ∀ q, pEval (mobU2 (gbChromVec 3)) q = (q - 2) * pEval A2 q := fun q => by
        rw [h3_2 q]; simp [A2, pEval_mul, pEval_lin, pEval]; grind
      have hU3 : ∀ q, pEval (mobU3 (gbChromVec 3)) q = (q - 2) ^ 2 * pEval A3 q := fun q => by
        rw [h3_3 q]; simp [A3, pEval_mul, pEval_linPow, pEval]; grind
      have hU4 : ∀ q, pEval (mobU4 (gbChromVec 3)) q = (q - 2) ^ 3 * pEval A4 q := fun q => by
        rw [h3_4 q]; simp [A4, pEval_mul, pEval_linPow, pEval]; grind
      rw [gbChromVec_succ 3 (by omega)]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- u0(4): order ≥ 3 at q = 2
        let Q0 := pAdd (pMul pVar (pMul E (pMul A0 A0)))
                  (pAdd (pMul A0 (pAdd (pSub (pNeg (pMul pVar (pMul E A1))) (pScale 2 A2)) (pMul (pLinPow 2 2) A4)))
                  (pAdd (pMul A1 A2)
                  (pAdd (pNeg (pMul A2 A2))
                        (pMul (pLinPow 2 2) (pMul A2 A4)))))
        exact hasLeadAt_to_ge (hasLeadAt_two_of_unit_mul 3 _ Q0 (fun q => by
          rw [mobius_step_0, hU0 q, hU1 q, hU2 q, hU4 q]
          simp only [Q0, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_var, pEval_linPow, hE]
          grind))
      · -- u1(4): order 3, lead +1 at q = 2
        let Q1 := pAdd (pNeg (pMul pVar (pMul E (pMul A1 A1))))
                  (pAdd (pMul A0 (pSub (pMul pVar (pMul E A1)) (pMul (pLinPow 2 2) A4)))
                  (pAdd (pMul A1 (pAdd (pNeg A2) (pScale 2 (pMul (pLinPow 2 2) A4))))
                  (pAdd (pNeg (pMul (pLinPow 2 2) (pMul A2 A4)))
                        (pMul (pLinPow 2 4) (pMul A4 A4)))))
        have hlead := hasLeadAt_two_of_unit_mul 3 _ Q1 (fun q => by
          rw [mobius_step_1, hU0 q, hU1 q, hU2 q, hU4 q]
          simp only [Q1, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_var, pEval_linPow, hE]
          grind)
        have hval : pEval Q1 2 = 1 := by
          simp [Q1, A0, A1, A2, A4, E, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_var, pEval_lin, pEval_linPow, pEval]
        simpa [hval] using hlead
      · -- u2(4): order 1, lead +1 at q = 2
        let Q2 := pAdd (pMul (pMul pVar pVar) (pMul (pLinPow 2 2) (pMul A0 A0)))
                  (pAdd (pMul A0 (pAdd (pSub (pSub (pScale (-2) (pMul pVar (pMul (pLinPow 2 2) A1)))
                                                   (pScale 2 (pMul pVar (pMul E A2))))
                                             (pScale 2 (pMul pVar (pMul (pLinPow 2 2) A3))))
                                       (pScale 4 (pMul (pLinPow 2 3) A4))))
                  (pAdd (pMul (pLinPow 2 2) (pMul A1 A1))
                  (pAdd (pMul A1 (pAdd (pMul (pAdd (pNeg (pMul pVar pVar)) (pAdd (pScale 4 pVar) (pConst (-2))))
                                             (pMul (pLinPow 2 2) A3))
                                 (pAdd (pMul (pLin 4) (pMul (pLinPow 2 3) A4))
                                       (pScale 2 (pMul E A2)))))
                  (pAdd (pMul (pAdd (pNeg (pMul pVar pVar)) (pAdd (pScale 3 pVar) (pConst (-1)))) (pMul A2 A2))
                  (pAdd (pMul A2 (pAdd (pScale 2 (pMul (pLin 3) (pMul (pLinPow 2 2) A4)))
                                       (pScale 2 (pMul E A3))))
                  (pAdd (pMul (pLinPow 2 2) (pMul A3 A3))
                  (pAdd (pMul (pLin 4) (pMul (pLinPow 2 3) (pMul A3 A4)))
                        (pMul (pAdd (pMul pVar pVar) (pAdd (pScale (-5) pVar) (pConst 7)))
                              (pMul (pLinPow 2 4) (pMul A4 A4))))))))))
        have hcancel2 : ∀ q : Int,
            (q - 1) * pEval (mobU2 (stepChromPoly gbSpec (gbChromVec 3) (gbChromVec 3))) q =
            (q - 2) * pEval Q2 q := by
          have hc := pEval_cancel_lin (pMul (pLin 1) (mobU2 (stepChromPoly gbSpec (gbChromVec 3) (gbChromVec 3))))
                       (pMul E Q2) 2 (fun q => by
            simp only [pEval_mul, pEval_lin, hE]
            rw [mobius_step_2, hU0 q, hU1 q, hU2 q, hU3 q, hU4 q]
            simp only [Q2, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, pEval_linPow, hE]
            grind)
          intro q; simpa [pEval_mul, pEval_lin, hE] using hc q
        have hlead := hasLeadAt_two_of_unit_mul 1 _ Q2 (fun q => by simpa [Int.pow_one] using hcancel2 q)
        have hval : pEval Q2 2 = 1 := by
          simp [Q2, A0, A1, A2, A3, A4, E, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, pEval_linPow, pEval]
        simpa [hval] using hlead
      · -- u3(4): order 3, lead -1 at q = 2
        let Q3 := pAdd (pMul A0 (pSub (pMul pVar (pMul E A3)) (pMul (pLinPow 2 2) A4)))
                       (pMul A2 (pSub (pMul (pAdd (pMul pVar pVar) (pAdd (pScale (-3) pVar) (pConst 3)))
                                            (pMul E A4)) A3))
        have hlead := hasLeadAt_two_of_unit_mul 3 _ Q3 (fun q => by
          rw [mobius_step_3, hU0 q, hU2 q, hU3 q, hU4 q]
          simp only [Q3, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_linPow, hE]
          grind)
        have hval : pEval Q3 2 = -1 := by
          simp [Q3, A0, A2, A3, A4, E, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, pEval_linPow, pEval]
        simpa [hval] using hlead
      · -- u4(4): order 4, lead -2 at q = 2
        let Q4 := pAdd (pMul A1 (pSub (pMul pVar A3) (pMul E A4)))
                       (pMul A4 (pSub (pMul (pAdd (pMul pVar pVar) (pAdd (pScale (-3) pVar) (pConst 3)))
                                            (pMul (pLinPow 2 2) A4)) (pMul E A3)))
        have hlead := hasLeadAt_two_of_unit_mul 4 _ Q4 (fun q => by
          rw [mobius_step_4, hU1 q, hU3 q, hU4 q]
          simp only [Q4, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_linPow, hE]
          grind)
        have hval : pEval Q4 2 = -2 := by
          simp [Q4, A1, A3, A4, E, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, pEval_linPow, pEval]
        simpa [hval] using hlead
    · have hkge : 4 ≤ k := by omega
      rcases ih hkge with ⟨⟨r0, hr0⟩, ⟨r1, hr1⟩, ⟨r2, hr2⟩, ⟨r3, hr3⟩, ⟨r4, hr4⟩⟩
      let E := pLin 2
      have hE : ∀ q, pEval E q = q - 2 := pEval_lin 2
      let P1 := pAdd (pConst ((-1 : Int) ^ k)) (pMul E r1)
      let P2 := pAdd (pConst 1) (pMul E r2)
      let P3 := pAdd (pConst ((-1 : Int) ^ (k - 1))) (pMul E r3)
      let P4 := pAdd (pConst (-2)) (pMul E r4)
      have hU0 : ∀ q, pEval (mobU0 (gbChromVec k)) q = (q - 2) ^ 3 * pEval r0 q := hr0
      have hU1 : ∀ q, pEval (mobU1 (gbChromVec k)) q = (q - 2) ^ (k - 1) * pEval P1 q := fun q => by
        rw [hr1 q]; simp [P1, pEval_add, pEval_const, pEval_mul, hE, Int.pow_succ]; grind
      have hU2 : ∀ q, pEval (mobU2 (gbChromVec k)) q = (q - 2) * pEval P2 q := fun q => by
        rw [hr2 q]; simp [P2, pEval_add, pEval_const, pEval_mul, hE]; grind
      have hU3 : ∀ q, pEval (mobU3 (gbChromVec k)) q = (q - 2) ^ (k - 1) * pEval P3 q := fun q => by
        rw [hr3 q]; simp [P3, pEval_add, pEval_const, pEval_mul, hE, Int.pow_succ]; grind
      have hU4 : ∀ q, pEval (mobU4 (gbChromVec k)) q = (q - 2) ^ (2 * k - 4) * pEval P4 q := fun q => by
        rw [hr4 q]; simp [P4, pEval_add, pEval_const, pEval_mul, hE, Int.pow_succ]; grind
      let hunit_lead := hasLeadAt_two_of_unit_mul
      have hpow_ge : ∀ a b : Nat, b ≤ a → ∀ q : Int, (q - 2) ^ a = (q - 2) ^ b * (q - 2) ^ (a - b) := by
        intro a b hba q; rw [← Int.pow_add]; congr 1; omega
      rw [gbChromVec_succ k (by omega)]
      simp only [show k + 1 - 1 = k by omega, show 2 * (k + 1) - 4 = 2 * k - 2 by omega]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- u0': order ≥ 3 at q = 2!
        let Q0 := pAdd (pMul pVar (pMul (pLinPow 2 3) (pMul r0 r0)))
                  (pAdd (pMul r0 (pAdd (pSub (pNeg (pMul pVar (pMul (pLinPow 2 (k - 1)) P1)))
                                             (pScale 2 (pMul E P2)))
                                       (pMul (pLinPow 2 (2 * k - 4)) P4)))
                  (pAdd (pMul (pLinPow 2 (k - 3)) (pMul P1 P2))
                  (pAdd (pNeg (pMul P2 P2))
                        (pMul (pLinPow 2 (2 * k - 5)) (pMul P2 P4)))))
        have hlead := hunit_lead 3 (mobU0 (stepChromPoly gbSpec (gbChromVec k) (gbChromVec k))) Q0 (fun q => by
          rw [mobius_step_0, hU0 q, hU1 q, hU2 q, hU4 q]
          simp only [Q0, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_var, pEval_linPow, hE]
          have h1 : (q - 2) ^ (k - 1) = (q - 2) ^ 2 * (q - 2) ^ (k - 3) := by rw [← Int.pow_add]; congr 1; omega
          have h2 : (q - 2) ^ (2 * k - 4) = (q - 2) ^ 1 * (q - 2) ^ (2 * k - 5) := by rw [← Int.pow_add]; congr 1; omega
          rw [h1, h2]; grind)
        exact hasLeadAt_to_ge hlead
      · -- u1': order k, lead (-1)^(k+1) at q = 2!
        let Q1 := pAdd (pNeg (pMul pVar (pMul (pLinPow 2 (k - 2)) (pMul P1 P1))))
                  (pAdd (pMul r0 (pSub (pMul pVar (pMul (pLinPow 2 2) P1)) (pMul (pLinPow 2 (k - 1)) P4)))
                  (pAdd (pMul P1 (pAdd (pNeg P2) (pScale 2 (pMul (pLinPow 2 (2 * k - 5)) P4))))
                  (pAdd (pNeg (pMul (pLinPow 2 (k - 2)) (pMul P2 P4)))
                        (pMul (pLinPow 2 (3 * k - 7)) (pMul P4 P4)))))
        have hlead := hunit_lead k (mobU1 (stepChromPoly gbSpec (gbChromVec k) (gbChromVec k))) Q1 (fun q => by
          rw [mobius_step_1, hU0 q, hU1 q, hU2 q, hU4 q]
          simp only [Q1, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_var, pEval_linPow]
          have ha : (q - 2) ^ (k - 1) * (q - 2) ^ (k - 1) = (q - 2) ^ k * (q - 2) ^ (k - 2) := by
            rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          have hb : (q - 2) ^ 3 * (q - 2) ^ (k - 1) = (q - 2) ^ k * (q - 2) ^ 2 := by
            rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          have hc : (q - 2) ^ 3 * (q - 2) ^ (2 * k - 4) = (q - 2) ^ k * (q - 2) ^ (k - 1) := by
            rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          have hd : (q - 2) ^ (k - 1) * (q - 2) = (q - 2) ^ k := by
            rw [← Int.pow_succ]; congr 1; omega
          have he : (q - 2) ^ (k - 1) * (q - 2) ^ (2 * k - 4) = (q - 2) ^ k * (q - 2) ^ (2 * k - 5) := by
            rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          have hf : (q - 2) ^ 2 * (q - 2) ^ (2 * k - 4) = (q - 2) ^ k * (q - 2) ^ (k - 2) := by
            rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          have hg : (q - 2) * ((q - 2) ^ (2 * k - 4) * (q - 2) ^ (2 * k - 4)) = (q - 2) ^ k * (q - 2) ^ (3 * k - 7) := by
            rw [← Int.pow_add, show (q - 2) * (q - 2) ^ (2 * k - 4 + (2 * k - 4)) = (q - 2) ^ 1 * (q - 2) ^ (2 * k - 4 + (2 * k - 4)) by rw [Int.pow_one],
                ← Int.pow_add, ← Int.pow_add]; congr 1; omega
          grind)
        have hQ1_at2 : pEval Q1 2 = (-1 : Int) ^ (k + 1) := by
          simp only [Q1, P1, P2, P4, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_linPow, hE]
          have h0a : (2 - 2 : Int) ^ (k - 2) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have h0b : (2 - 2 : Int) ^ (k - 1) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have h0c : (2 - 2 : Int) ^ (2 * k - 5) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have h0d : (2 - 2 : Int) ^ (3 * k - 7) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          rw [h0a, h0b, h0c, h0d, Int.pow_succ]; grind
        rwa [hQ1_at2] at hlead
      · -- u2': order 1, lead 1 at q = 2! (Cancel `(q - 2)` first, then apply `hunit_lead 1`!)
        let Q2 := pAdd (pMul (pMul pVar pVar) (pMul (pLinPow 2 4) (pMul r0 r0)))
                  (pAdd (pMul r0 (pAdd (pSub (pSub (pScale (-2) (pMul pVar (pMul (pLinPow 2 k) P1)))
                                                   (pScale 2 (pMul pVar (pMul (pLinPow 2 2) P2))))
                                             (pScale 2 (pMul pVar (pMul (pLinPow 2 k) P3))))
                                       (pScale 4 (pMul (pLinPow 2 (2 * k - 3)) P4))))
                  (pAdd (pMul (pLinPow 2 (2 * k - 4)) (pMul P1 P1))
                  (pAdd (pMul P1 (pAdd (pMul (pAdd (pNeg (pMul pVar pVar)) (pAdd (pScale 4 pVar) (pConst (-2))))
                                             (pMul (pLinPow 2 (2 * k - 4)) P3))
                                 (pAdd (pMul (pLin 4) (pMul (pLinPow 2 (3 * k - 7)) P4))
                                       (pScale 2 (pMul (pLinPow 2 (k - 2)) P2)))))
                  (pAdd (pMul (pAdd (pNeg (pMul pVar pVar)) (pAdd (pScale 3 pVar) (pConst (-1)))) (pMul P2 P2))
                  (pAdd (pMul P2 (pAdd (pScale 2 (pMul (pLin 3) (pMul (pLinPow 2 (2 * k - 5)) P4)))
                                       (pScale 2 (pMul (pLinPow 2 (k - 2)) P3))))
                  (pAdd (pMul (pLinPow 2 (2 * k - 4)) (pMul P3 P3))
                  (pAdd (pMul (pLin 4) (pMul (pLinPow 2 (3 * k - 7)) (pMul P3 P4)))
                        (pMul (pAdd (pMul pVar pVar) (pAdd (pScale (-5) pVar) (pConst 7)))
                              (pMul (pLinPow 2 (4 * k - 10)) (pMul P4 P4))))))))))
        have hcancel2 : ∀ q : Int,
            (q - 1) * pEval (mobU2 (stepChromPoly gbSpec (gbChromVec k) (gbChromVec k))) q =
            (q - 2) * pEval Q2 q := by
          have hc := pEval_cancel_lin (pMul (pLin 1) (mobU2 (stepChromPoly gbSpec (gbChromVec k) (gbChromVec k))))
                       (pMul E Q2) 2 (fun q => by
            simp only [pEval_mul, pEval_lin, hE]
            rw [mobius_step_2, hU0 q, hU1 q, hU2 q, hU3 q, hU4 q]
            simp only [Q2, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, pEval_linPow]
            have h1 : (q - 2) ^ 3 * (q - 2) ^ 3 = (q - 2) ^ 2 * (q - 2) ^ 4 := by rw [← Int.pow_add, ← Int.pow_add]
            have h2 : (q - 2) ^ 3 * (q - 2) ^ (k - 1) = (q - 2) ^ 2 * (q - 2) ^ k := by rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
            have h3 : (q - 2) ^ 3 * (q - 2) = (q - 2) ^ 2 * (q - 2) ^ 2 := by rw [show (q - 2) ^ 3 * (q - 2) = (q - 2) ^ 3 * (q - 2) ^ 1 by rw [Int.pow_one], ← Int.pow_add, ← Int.pow_add]
            have h4 : (q - 2) ^ 3 * (q - 2) ^ (2 * k - 4) = (q - 2) ^ 2 * (q - 2) ^ (2 * k - 3) := by rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
            have h5 : (q - 2) ^ (k - 1) * (q - 2) ^ (k - 1) = (q - 2) ^ 2 * (q - 2) ^ (2 * k - 4) := by rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
            have h6 : (q - 2) ^ (k - 1) * (q - 2) ^ (2 * k - 4) = (q - 2) ^ 2 * (q - 2) ^ (3 * k - 7) := by rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
            have h7 : (q - 2) ^ (k - 1) * (q - 2) = (q - 2) ^ 2 * (q - 2) ^ (k - 2) := by
              rw [show (q - 2) ^ (k - 1) * (q - 2) = (q - 2) ^ (k - 1) * (q - 2) ^ 1 by rw [Int.pow_one], ← Int.pow_add, ← Int.pow_add]; congr 1; omega
            have h8 : (q - 2) * (q - 2) ^ (2 * k - 4) = (q - 2) ^ 2 * (q - 2) ^ (2 * k - 5) := by
              rw [show (q - 2) * (q - 2) ^ (2 * k - 4) = (q - 2) ^ 1 * (q - 2) ^ (2 * k - 4) by rw [Int.pow_one], ← Int.pow_add, ← Int.pow_add]; congr 1; omega
            have h9 : (q - 2) ^ (2 * k - 4) * (q - 2) ^ (2 * k - 4) = (q - 2) ^ 2 * (q - 2) ^ (4 * k - 10) := by
              rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
            grind)
          intro q; simpa [pEval_mul, pEval_lin, hE] using hc q
        have hlead := hunit_lead 1 _ Q2 (fun q => by simpa [Int.pow_one] using hcancel2 q)
        have hQ2_at2 : pEval Q2 2 = 1 := by
          simp only [Q2, P1, P2, P3, P4, pEval_add, pEval_sub, pEval_neg, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_lin, pEval_linPow, hE]
          have z1 : (2 - 2 : Int) ^ 4 = 0 := rfl
          have z2 : (2 - 2 : Int) ^ 2 = 0 := rfl
          have z3 : (2 - 2 : Int) ^ k = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have z4 : (2 - 2 : Int) ^ (2 * k - 3) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have z5 : (2 - 2 : Int) ^ (2 * k - 4) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have z6 : (2 - 2 : Int) ^ (3 * k - 7) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have z7 : (2 - 2 : Int) ^ (k - 2) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have z8 : (2 - 2 : Int) ^ (2 * k - 5) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have z9 : (2 - 2 : Int) ^ (4 * k - 10) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          rw [z1, z2, z3, z4, z5, z6, z7, z8, z9]; grind
        rwa [hQ2_at2] at hlead
      · -- u3': order k, lead (-1)^k at q = 2!
        let Q3 := pAdd (pMul r0 (pSub (pMul pVar (pMul (pLinPow 2 2) P3)) (pMul (pLinPow 2 (k - 1)) P4)))
                       (pMul P2 (pSub (pMul (pAdd (pMul pVar pVar) (pAdd (pScale (-3) pVar) (pConst 3)))
                                            (pMul (pLinPow 2 (k - 3)) P4)) P3))
        have hlead := hunit_lead k _ Q3 (fun q => by
          rw [mobius_step_3, hU0 q, hU2 q, hU3 q, hU4 q]
          simp only [Q3, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_linPow]
          have h1 : (q - 2) ^ 3 * (q - 2) ^ (k - 1) = (q - 2) ^ k * (q - 2) ^ 2 := by rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          have h2 : (q - 2) ^ 3 * (q - 2) ^ (2 * k - 4) = (q - 2) ^ k * (q - 2) ^ (k - 1) := by rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          have h3 : (q - 2) * (q - 2) ^ (2 * k - 4) = (q - 2) ^ k * (q - 2) ^ (k - 3) := by
            rw [show (q - 2) * (q - 2) ^ (2 * k - 4) = (q - 2) ^ 1 * (q - 2) ^ (2 * k - 4) by rw [Int.pow_one], ← Int.pow_add, ← Int.pow_add]; congr 1; omega
          have h4 : (q - 2) * (q - 2) ^ (k - 1) = (q - 2) ^ k := by
            rw [show (q - 2) * (q - 2) ^ (k - 1) = (q - 2) ^ 1 * (q - 2) ^ (k - 1) by rw [Int.pow_one], ← Int.pow_add]; congr 1; omega
          grind)
        have hQ3_at2 : pEval Q3 2 = (-1 : Int) ^ k := by
          simp only [Q3, P2, P3, P4, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_linPow, hE]
          have z1 : (2 - 2 : Int) ^ 2 = 0 := rfl
          have z2 : (2 - 2 : Int) ^ (k - 1) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have z3 : (2 - 2 : Int) ^ (k - 3) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have hpow1 : (-1 : Int) ^ k = -((-1 : Int) ^ (k - 1)) := by
            conv => lhs; rw [show k = (k - 1) + 1 by omega, Int.pow_succ]
            grind
          rw [z1, z2, z3, hpow1]; grind
        rwa [hQ3_at2] at hlead
      · -- u4': order 2k - 2, lead -2 at q = 2!
        let Q4 := pAdd (pMul P1 (pSub (pMul pVar P3) (pMul (pLinPow 2 (k - 3)) P4)))
                       (pMul P4 (pSub (pMul (pAdd (pMul pVar pVar) (pAdd (pScale (-3) pVar) (pConst 3)))
                                            (pMul (pLinPow 2 (2 * k - 6)) P4))
                                      (pMul (pLinPow 2 (k - 3)) P3)))
        have hlead := hunit_lead (2 * k - 2) _ Q4 (fun q => by
          rw [mobius_step_4, hU1 q, hU3 q, hU4 q]
          simp only [Q4, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_linPow]
          have h1 : (q - 2) ^ (k - 1) * (q - 2) ^ (k - 1) = (q - 2) ^ (2 * k - 2) := by rw [← Int.pow_add]; congr 1; omega
          have h2 : (q - 2) ^ (k - 1) * (q - 2) ^ (2 * k - 4) = (q - 2) ^ (2 * k - 2) * (q - 2) ^ (k - 3) := by rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          have h3 : (q - 2) ^ (2 * k - 4) * (q - 2) ^ (2 * k - 4) = (q - 2) ^ (2 * k - 2) * (q - 2) ^ (2 * k - 6) := by rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
          grind)
        have hQ4_at2 : pEval Q4 2 = -2 := by
          simp only [Q4, P1, P3, P4, pEval_add, pEval_sub, pEval_mul, pEval_scale, pEval_const, pEval_var, pEval_linPow, hE]
          have z1 : (2 - 2 : Int) ^ (k - 3) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have z2 : (2 - 2 : Int) ^ (2 * k - 6) = 0 := by rw [Int.sub_self]; exact Int.zero_pow (by omega)
          have hsign : (-1 : Int) ^ k * (-1 : Int) ^ (k - 1) = -1 := by
            rw [← Int.pow_add, show k + (k - 1) = 2 * (k - 1) + 1 by omega, Int.pow_succ, Int.pow_mul,
                show (-1 : Int) ^ 2 = 1 by decide, Int.one_pow]
            grind
          rw [z1, z2]; grind
        rwa [hQ4_at2] at hlead

/-- **THEOREM 5 (Exact Linear `(q - 2)`-Multiplicity `2k - 4` with Constant Lead `-4` ∀ `k ≥ 4`)**:
    Despite degree `2^k` growing exponentially, the chromatic polynomial `P(GB_k, q)` has root
    `q = 2` of exact linear multiplicity `2k - 4` with constant leading coefficient `-4` for ALL `k ≥ 4`:
    `P(GB_k, q) = -4 * (q - 2)^(2k - 4) + O((q - 2)^(2k - 3))`. -/
theorem gb_chrom_root_two_linear (k : Nat) (hk : 4 ≤ k) :
    HasLeadAt (gbChromPoly k) 2 (2 * k - 4) (-4) := by
  rcases (gb_mobius_lead_at_two k hk).2.2.2.2 with ⟨r4, hr4⟩
  refine ⟨pAdd (pConst (-2)) (pMul pVar r4), fun q => ?_⟩
  rw [gbChromPoly, pEval_totalChromPoly, hr4 q]
  simp only [pEval_add, pEval_const, pEval_mul, pEval_var]
  grind

/-- Sharp threshold boundary witnesses for Theorem 5: at `k = 2` multiplicity is `1` (lead `+2`),
    and at `k = 3` multiplicity is `3` (lead `+4`), showing `k ≥ 4` is exact! -/
theorem gb_chrom_root_two_sharp_k2 : HasLeadAt (gbChromPoly 2) 2 1 2 := by
  refine ⟨[1, 0, 1], fun q => ?_⟩
  rw [gbChromPoly, pEval_totalChromPoly]
  simp only [gbChromVec, mobU4, gbChromBase_0, gbChromBase_1, gbChromBase_2, gbChromBase_3, gbChromBase_4,
             pEval_add, pEval_mul, pEval_lin, pEval]
  grind

theorem gb_chrom_root_two_sharp_k3 : HasLeadAt (gbChromPoly 3) 2 3 4 := by
  have hu4 := gb3_mobius_exact.2.2.2.2
  let A : Poly := pMul pVar (pMul (pLinPow 1 2) [2, -2, 1])
  have hA : ∀ q, pEval A q = q * (q - 1) ^ 2 * (q ^ 2 - 2 * q + 2) := fun q => by
    simp only [A, pEval_mul, pEval_var, pEval_linPow, pEval]; grind
  refine ⟨pQuotLin A 2, fun q => ?_⟩
  have hq := pEval_horner A 2 q
  rw [hA 2] at hq
  rw [gbChromPoly, pEval_totalChromPoly, hu4 q]
  have := hA q; grind


-- ============================================================================
-- SECTION 6: Reusability Instantiations (`TW_k`, `SB_k`), Sharpness & Non-Vacuity
-- ============================================================================

theorem recGraph_pmVec_succ (spec : GlueSpec) (d : Nat) (s : Fin 8) :
    pmVec (recGraph spec (d + 1)) s = stepPM spec (pmVec (recGraph spec d)) (pmVec (recGraph spec d)) s := by
  simp only [recGraph, castTermGraph_pmVec, glue_pm_sound]

theorem recGraph_alphaVec_succ (spec : GlueSpec) (d : Nat) (s : Fin 8) :
    alphaVec (recGraph spec (d + 1)) s = stepAlpha spec (alphaVec (recGraph spec d)) (alphaVec (recGraph spec d)) s := by
  simp only [recGraph, castTermGraph_alphaVec, glue_alpha_sound]

theorem twPMCoef_eq_fast : ∀ sL sR s : Fin 8,
    (sL.val == 1 || sL.val == 2 || sL.val == 4 || sL.val == 7) = true →
    (sR.val == 1 || sR.val == 2 || sR.val == 4 || sR.val == 7) = true →
    bridgePMCoef twSpec sL sR s = twPMCoefFast sL sR s := by
  decide

/-- **REUSABILITY THEOREM (`TW_k` via `BitTransfer3`)**:
    For all `d ≥ 0` (`k = d + 2`), `exactPM (TW_{d+2}) = twPmSeq (d + 2)`, obeying
    `PM(TW_{k+1}) = PM(TW_k)^2 + PM(TW_{k-1})` (instead of `+ PM(TW_{k-1})^2`). -/
theorem twGraph_pmVec_eq (d : Nat) (s : Fin 8) :
    pmVec (recGraph twSpec d) s = twPmInv d s := by
  induction d generalizing s with
  | zero =>
    change pmVec (gbGraph 2 (by omega)) s = twPmInv 0 s
    rw [gbGraph2_pmVec]; revert s; decide
  | succ d ih =>
    rw [recGraph_pmVec_succ, stepPM_eq_coef]
    have hfun : pmVec (recGraph twSpec d) = twPmInv d := funext ih
    rw [hfun]
    have hcongr : ∀ sL sR : Fin 8,
        bridgePMCoef twSpec sL sR s * (twPmInv d sL * twPmInv d sR) =
        twPMCoefFast sL sR s * (twPmInv d sL * twPmInv d sR) := by
      intro sL sR
      by_cases hL : (sL.val == 1 || sL.val == 2 || sL.val == 4 || sL.val == 7) = true
      · by_cases hR : (sR.val == 1 || sR.val == 2 || sR.val == 4 || sR.val == 7) = true
        · rw [twPMCoef_eq_fast sL sR s hL hR]
        · have hz : twPmInv d sR = 0 := by
            match sR with
            | ⟨0, _⟩ | ⟨3, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl
            | ⟨1, _⟩ | ⟨2, _⟩ | ⟨4, _⟩ | ⟨7, _⟩ => simp at hR
          simp [hz]
      · have hz : twPmInv d sL = 0 := by
          match sL with
          | ⟨0, _⟩ | ⟨3, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl
          | ⟨1, _⟩ | ⟨2, _⟩ | ⟨4, _⟩ | ⟨7, _⟩ => simp at hL
        simp [hz]
    rw [sumFin8_congr (fun sL => sumFin8_congr (fun sR => hcongr sL sR))]
    match s with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ =>
      simp [sumFin8, twPMCoefFast, twPmInv, twPmSeq]; try grind

theorem tw_pm_exact (d : Nat) : exactPM (recGraph twSpec d).graph = twPmSeq (d + 2) := by
  rw [exactPM_eq_pmVec7, twGraph_pmVec_eq d 7]; rfl

theorem sbPm_step_inv : ∀ s : Fin 8, stepPM sbSpec sbPmInv sbPmInv s = sbPmInv s := by
  decide

theorem sbGraph_pmVec_eq (d : Nat) (s : Fin 8) :
    pmVec (recGraph sbSpec d) s = (if d = 0 && s == 1 then 1 else sbPmInv s) := by
  induction d generalizing s with
  | zero =>
    change pmVec (gbGraph 2 (by omega)) s = _
    rw [gbGraph2_pmVec]; revert s; decide
  | succ d ih =>
    rw [recGraph_pmVec_succ]
    have hfun : pmVec (recGraph sbSpec d) = fun t => if d = 0 && t == 1 then 1 else sbPmInv t := funext ih
    rw [hfun]
    cases d with
    | zero => revert s; decide
    | succ d' =>
      have hsimp : (fun t => if d' + 1 = 0 && t == 1 then 1 else sbPmInv t) = sbPmInv := by
        funext t; simp
      rw [hsimp, sbPm_step_inv s]; simp

theorem sb_pm_const_one (d : Nat) : exactPM (recGraph sbSpec d).graph = 1 := by
  rw [exactPM_eq_pmVec7, sbGraph_pmVec_eq d 7]; simp [sbPmInv]; rfl

-- ----------------------------------------------------------------------------
-- Kernel-Checked Sharpness Separations & Non-Vacuity Witnesses
-- ----------------------------------------------------------------------------

/-- Sharpness Witness 1: Twisting a single bridge breaks A000283 at `k = 5` (`27 ≠ 29`)! -/
theorem sharpness_twist_pm_k5 :
    exactPM (recGraph twSpec 3).graph = 27 ∧
    exactPM (gbGraph 5 (by omega)).graph = 29 ∧
    exactPM (recGraph twSpec 3).graph ≠ exactPM (gbGraph 5 (by omega)).graph := by
  rw [tw_pm_exact 3, gb_pm_exact 5 (by omega)]
  decide

/-- Sharpness Witness 2: Twisting a single bridge breaks `α = 3*2^(k-3)+1` at `k = 4` (`8 ≠ 7`)! -/
theorem sharpness_twist_alpha_k4 :
    exactAlpha (recGraph twSpec 2).graph = some 8 ∧
    exactAlpha (gbGraph 4 (by omega)).graph = some 7 ∧
    exactAlpha (recGraph twSpec 2).graph ≠ exactAlpha (gbGraph 4 (by omega)).graph := by
  have htw : exactAlpha (recGraph twSpec 2).graph = some 8 := by
    rw [exactAlpha_eq_maxFin8]
    have h0 : alphaVec (recGraph twSpec 0) = gbAlphaBase2 := funext gbGraph2_alphaVec
    have h1 : alphaVec (recGraph twSpec 1) = stepAlpha twSpec gbAlphaBase2 gbAlphaBase2 := by
      funext s; rw [recGraph_alphaVec_succ, h0]
    have h2 : alphaVec (recGraph twSpec 2) =
        stepAlpha twSpec (stepAlpha twSpec gbAlphaBase2 gbAlphaBase2) (stepAlpha twSpec gbAlphaBase2 gbAlphaBase2) := by
      funext s; rw [recGraph_alphaVec_succ, h1]
    rw [h2]; decide
  have hgb : exactAlpha (gbGraph 4 (by omega)).graph = some 7 := by
    simpa using gb_alpha_exact 4 (by omega)
  rw [htw, hgb]
  decide

/-- Sharpness Witness 3: Dropping the Gray bridge breaks A000283 immediately at `k = 3` (`1 ≠ 2`)! -/
theorem sharpness_ablation_pm_k3 :
    exactPM (recGraph sbSpec 1).graph = 1 ∧
    exactPM (gbGraph 3 (by omega)).graph = 2 ∧
    exactPM (recGraph sbSpec 1).graph ≠ exactPM (gbGraph 3 (by omega)).graph := by
  rw [sb_pm_const_one 1, gb_pm_exact 3 (by omega)]
  decide

/-- Non-Vacuity Concrete Witness: `GB_2`, `GB_3`, `GB_4` simultaneously realize all 5 theorems! -/
theorem non_vacuity_witness :
    exactPM (gbGraph 4 (by omega)).graph = 5 ∧
    exactPM (gbDoublyCyclic 4 (by omega)) = 11 ∧
    exactAlpha (gbGraph 4 (by omega)).graph = some 7 ∧
    exactAlpha (gbDoublyCyclic 4 (by omega)) = some 6 ∧
    exactChromCount (gbGraph 3 (by omega)).graph 2 = 0 ∧
    exactChromCount (gbGraph 3 (by omega)).graph 3 = 60 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gb_pm_exact 4 (by omega)]; rfl
  · rw [gb_doublyCyclic_pm 4 (by omega)]; rfl
  · exact gb_alpha_exact 4 (by omega)
  · exact gb_doublyCyclic_alpha 4 (by omega)
  · exact gb_chrom_at_two_zero 3 (by omega)
  · have h := gbGraph_exactChrom 3 (by omega) 3
    rw [gbChromPoly, pEval_totalChromPoly] at h
    have h4 := gb3_mobius_exact.2.2.2.2 3
    have h3 : ((3 : Nat) : Int) = 3 := rfl
    rw [h3, h4] at h; omega

end BitTransfer3
