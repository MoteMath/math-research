import Defs

namespace SiliconNativeCert

-- ============================================================
-- Section 1: Sound Integer Congruence Positivity
-- ============================================================

private theorem foldl_add_init {α : Type} (l : List α) (f : α → Int) (init : Int) :
    l.foldl (fun acc x => acc + f x) init = init + l.foldl (fun acc x => acc + f x) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [ih (init + f a), ih (f a), Int.add_assoc]

private theorem foldl_add_pointwise {α : Type} (l : List α) (f g : α → Int) :
    l.foldl (fun acc x => acc + (f x + g x)) 0 =
    l.foldl (fun acc x => acc + f x) 0 + l.foldl (fun acc x => acc + g x) 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [foldl_add_init t (fun x => f x + g x) (f a + g a), ih]
    rw [foldl_add_init t f (f a), foldl_add_init t g (g a)]
    omega

private theorem foldl_add_le {α : Type} (l : List α) (f g : α → Int)
    (h : ∀ x ∈ l, f x ≤ g x) :
    l.foldl (fun acc x => acc + f x) 0 ≤ l.foldl (fun acc x => acc + g x) 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [foldl_add_init t f (f a), foldl_add_init t g (g a)]
    have ha : f a ≤ g a := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

private theorem foldl_add_lt_of_mem {α : Type} (l : List α) (f g : α → Int) (a0 : α)
    (hmem : a0 ∈ l) (hle : ∀ x ∈ l, f x ≤ g x) (hlt : f a0 < g a0) :
    l.foldl (fun acc x => acc + f x) 0 < l.foldl (fun acc x => acc + g x) 0 := by
  induction l with
  | nil => cases hmem
  | cons a t ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [foldl_add_init t f (f a), foldl_add_init t g (g a)]
    cases hmem with
    | head =>
      have ht := foldl_add_le t f g (fun x hx => hle x (List.mem_cons_of_mem _ hx))
      omega
    | tail _ hmem' =>
      have ha := hle a (List.mem_cons_self ..)
      have ht := ih hmem' (fun x hx => hle x (List.mem_cons_of_mem _ hx))
      omega

private theorem foldl_add_zero {α : Type} (l : List α) :
    l.foldl (fun acc (_ : α) => acc + (0 : Int)) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.foldl_cons, Int.zero_add]; exact ih

private theorem foldl_mul_left {α : Type} (l : List α) (c : Int) (f : α → Int) :
    l.foldl (fun acc x => acc + c * f x) 0 = c * l.foldl (fun acc x => acc + f x) 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [foldl_add_init t (fun x => c * f x) (c * f a), ih]
    rw [foldl_add_init t f (f a), Int.mul_add]

private theorem foldl_mul_right {α : Type} (l : List α) (f : α → Int) (c : Int) :
    l.foldl (fun acc x => acc + f x * c) 0 = l.foldl (fun acc x => acc + f x) 0 * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [foldl_add_init t (fun x => f x * c) (f a * c), ih]
    rw [foldl_add_init t f (f a), Int.add_mul]

private theorem foldl_swap {α β : Type} (la : List α) (lb : List β) (f : α → β → Int) :
    la.foldl (fun acc a => acc + lb.foldl (fun acc2 b => acc2 + f a b) 0) 0 =
    lb.foldl (fun acc2 b => acc2 + la.foldl (fun acc a => acc + f a b) 0) 0 := by
  induction la with
  | nil => simp only [List.foldl_nil]; symm; exact foldl_add_zero lb
  | cons a t ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [foldl_add_init t (fun a' => lb.foldl (fun acc2 b => acc2 + f a' b) 0)
        (lb.foldl (fun acc2 b => acc2 + f a b) 0), ih]
    have hstep :=
      foldl_add_pointwise lb (fun b => f a b) (fun b => t.foldl (fun acc a' => acc + f a' b) 0)
    rw [← hstep]
    congr 1; funext acc2 b; rw [foldl_add_init t (fun a' => f a' b) (f a b)]

private theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFin f = sumFin g := by
  unfold sumFin; congr 1; funext acc i; rw [h i]

private theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g :=
  foldl_add_pointwise (List.finRange n) f g

private theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin (fun i => c * f i) = c * sumFin f :=
  foldl_mul_left (List.finRange n) c f

private theorem sumFin_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumFin (fun i => f i * c) = sumFin f * c :=
  foldl_mul_right (List.finRange n) f c

private theorem int_mul_self_nonneg (x : Int) : 0 ≤ x * x := by
  cases x with
  | ofNat m => exact Int.natCast_nonneg (m * m)
  | negSucc m => exact Int.natCast_nonneg ((m + 1) * (m + 1))

private theorem int_natAbs_sq (x : Int) :
    Int.ofNat x.natAbs * Int.ofNat x.natAbs = x * x := by
  cases x with | ofNat m => rfl | negSucc m => rfl

private theorem int_neg_natAbs_le (x : Int) : -Int.ofNat x.natAbs ≤ x := by
  cases x with
  | ofNat m => change -(m : Int) ≤ (m : Int); omega
  | negSucc m => change -((m + 1 : Nat) : Int) ≤ Int.negSucc m; omega

private theorem int_two_mul_le_sq_add_sq (x y : Int) : 2 * (x * y) ≤ x * x + y * y := by
  have h : 0 ≤ (x - y) * (x - y) := int_mul_self_nonneg (x - y)
  have hexp : (x - y) * (x - y) = x * x + y * y - 2 * (x * y) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; have hc : y * x = x * y := Int.mul_comm y x; omega
  omega

private theorem int_neg_abs_mul_le (c x y : Int) :
    -(Int.ofNat c.natAbs * (x * x + y * y)) ≤ 2 * (x * c * y) := by
  have hsq := int_two_mul_le_sq_add_sq (Int.ofNat x.natAbs) (Int.ofNat y.natAbs)
  rw [int_natAbs_sq x, int_natAbs_sq y] at hsq
  have hc0 : 0 ≤ Int.ofNat c.natAbs := Int.natCast_nonneg c.natAbs
  have hprod : 2 * (Int.ofNat c.natAbs * (Int.ofNat x.natAbs * Int.ofNat y.natAbs)) ≤
      Int.ofNat c.natAbs * (x * x + y * y) := by
    have hmul := Int.mul_le_mul_of_nonneg_left hsq hc0
    have hl : Int.ofNat c.natAbs * (2 * (Int.ofNat x.natAbs * Int.ofNat y.natAbs)) =
        2 * (Int.ofNat c.natAbs * (Int.ofNat x.natAbs * Int.ofNat y.natAbs)) := by
      rw [← Int.mul_assoc, Int.mul_comm (Int.ofNat c.natAbs) 2, Int.mul_assoc]
    omega
  have habs_val : -(Int.ofNat c.natAbs * (Int.ofNat x.natAbs * Int.ofNat y.natAbs)) ≤ x * c * y := by
    have h1 : (x * c * y).natAbs = x.natAbs * c.natAbs * y.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
    have h2 : Int.ofNat c.natAbs * (Int.ofNat x.natAbs * Int.ofNat y.natAbs) =
        Int.ofNat (x * c * y).natAbs := by
      rw [h1]
      have hcomm : c.natAbs * (x.natAbs * y.natAbs) = x.natAbs * c.natAbs * y.natAbs := by
        rw [← Nat.mul_assoc, Nat.mul_comm c.natAbs x.natAbs]
      change Int.ofNat (c.natAbs * (x.natAbs * y.natAbs)) = Int.ofNat (x.natAbs * c.natAbs * y.natAbs)
      rw [hcomm]
    rw [h2]; exact int_neg_natAbs_le (x * c * y)
  omega

private theorem sumFin_delta_sq {n : Nat} (S : Int) (v : Fin n → Int) (i : Fin n) :
    sumFin (fun j => v i * (if i = j then S else 0) * v j) = S * (v i * v i) := by
  unfold sumFin
  have hmem : i ∈ List.finRange n := List.mem_finRange i
  have hnodup : (List.finRange n).Nodup := List.nodup_finRange n
  suffices h : ∀ (l : List (Fin n)), l.Nodup →
      l.foldl (fun acc j => acc + v i * (if i = j then S else 0) * v j) 0 =
      if i ∈ l then S * (v i * v i) else 0 by
    rw [h (List.finRange n) hnodup]; simp [hmem]
  intro l hnd
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.nodup_cons] at hnd
    simp only [List.foldl_cons, Int.zero_add]
    rw [foldl_add_init t _ _, ih hnd.2]
    by_cases heq : i = a
    · subst heq; have hnot : i ∉ t := hnd.1; simp [hnot]; rw [Int.mul_comm (v i) S, Int.mul_assoc]
    · simp [heq]

theorem quadForm_pos_of_strictDiagDom {n : Nat}
    (G : Fin n → Fin n → Int) (S : Int)
    (hsym : ∀ i j, G i j = G j i)
    (hdom : IsStrictlyScaledDiagDom G S)
    (v : Fin n → Int) (i0 : Fin n) (hv0 : v i0 ≠ 0) :
    0 < quadForm G v := by
  rcases hdom with ⟨hS, hrow⟩
  let F : Fin n → Fin n → Int := fun i j => G i j - if i = j then S else 0
  have hFsym : ∀ i j, F i j = F j i := by
    intro i j; dsimp [F]; rw [hsym i j]
    by_cases h : i = j
    · subst h; rfl
    · have h' : j ≠ i := fun heq => h heq.symm; simp [h, h']
  have hsplit : quadForm G v =
      sumFin (fun i => S * (v i * v i)) +
      sumFin (fun i => sumFin (fun j => v i * F i j * v j)) := by
    rw [← sumFin_add]; unfold quadForm; apply sumFin_congr; intro i
    rw [← sumFin_delta_sq S v i, ← sumFin_add]; apply sumFin_congr; intro j
    dsimp [F]; rw [Int.mul_sub, Int.sub_mul]; omega
  have hterm :
      sumFin (fun i => sumFin (fun j => -(Int.ofNat (F i j).natAbs * (v i * v i + v j * v j)))) ≤
      sumFin (fun i => sumFin (fun j => 2 * (v i * F i j * v j))) := by
    unfold sumFin; apply foldl_add_le; intro i _; apply foldl_add_le; intro j _
    exact int_neg_abs_mul_le (F i j) (v i) (v j)
  have hrhs_eq :
      sumFin (fun i => sumFin (fun j => 2 * (v i * F i j * v j))) =
      2 * sumFin (fun i => sumFin (fun j => v i * F i j * v j)) := by
    rw [← sumFin_mul_left]; apply sumFin_congr; intro i; exact sumFin_mul_left 2 _
  have hlhs_eq :
      sumFin (fun i => sumFin (fun j => -(Int.ofNat (F i j).natAbs * (v i * v i + v j * v j)))) =
      -(2 * sumFin (fun i => rowAbsResidual G S i * (v i * v i))) := by
    have h1 :
        sumFin (fun i => sumFin (fun j => -(Int.ofNat (F i j).natAbs * (v i * v i + v j * v j)))) =
        (-1) * sumFin (fun i => sumFin (fun j =>
          Int.ofNat (F i j).natAbs * (v i * v i) + Int.ofNat (F i j).natAbs * (v j * v j))) := by
      rw [← sumFin_mul_left]; apply sumFin_congr; intro i
      rw [← sumFin_mul_left]; apply sumFin_congr; intro j; rw [Int.mul_add]; omega
    have h2 :
        sumFin (fun i => sumFin (fun j =>
          Int.ofNat (F i j).natAbs * (v i * v i) + Int.ofNat (F i j).natAbs * (v j * v j))) =
        sumFin (fun i => sumFin (fun j => Int.ofNat (F i j).natAbs * (v i * v i))) +
        sumFin (fun i => sumFin (fun j => Int.ofNat (F i j).natAbs * (v j * v j))) := by
      rw [← sumFin_add]; apply sumFin_congr; intro i; exact sumFin_add _ _
    have h3 :
        sumFin (fun i => sumFin (fun j => Int.ofNat (F i j).natAbs * (v i * v i))) =
        sumFin (fun i => rowAbsResidual G S i * (v i * v i)) := by
      apply sumFin_congr; intro i; rw [sumFin_mul_right]; rfl
    have h4 :
        sumFin (fun i => sumFin (fun j => Int.ofNat (F i j).natAbs * (v j * v j))) =
        sumFin (fun i => rowAbsResidual G S i * (v i * v i)) := by
      change (List.finRange n).foldl (fun acc i => acc +
          (List.finRange n).foldl (fun acc2 j => acc2 + Int.ofNat (F i j).natAbs * (v j * v j)) 0) 0 = _
      rw [foldl_swap]; apply sumFin_congr; intro j; rw [foldl_mul_right]; congr 1
      unfold rowAbsResidual; apply sumFin_congr; intro i; rw [hFsym i j]
    rw [h1, h2, h3, h4]; omega
  have hstrict :
      sumFin (fun i => rowAbsResidual G S i * (v i * v i)) <
      sumFin (fun i => S * (v i * v i)) := by
    unfold sumFin
    apply foldl_add_lt_of_mem (List.finRange n) _ _ i0 (List.mem_finRange i0)
    · intro i _; exact Int.mul_le_mul_of_nonneg_right (Int.le_of_lt (hrow i)) (int_mul_self_nonneg (v i))
    · have hvsq : 0 < v i0 * v i0 := by
        cases h : v i0 with
        | ofNat m =>
          cases m with
          | zero => exfalso; exact hv0 h
          | succ m' => change 0 < ((m' + 1) * (m' + 1) : Int); exact Int.natCast_pos.mpr (Nat.mul_pos (Nat.succ_pos m') (Nat.succ_pos m'))
        | negSucc m =>
          change 0 < ((m + 1) * (m + 1) : Int); exact Int.natCast_pos.mpr (Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos m))
      exact Int.mul_lt_mul_of_pos_right (hrow i0) hvsq
  rw [hlhs_eq, hrhs_eq] at hterm; omega

-- ============================================================
-- Section 2: Universal 4-State Carry Transducers
-- ============================================================

private theorem stepNext_lt4 (t : Transducer4) (s : Nat) (a b : Bool) :
    t.stepNext s a b < 4 := by
  unfold Transducer4.stepNext
  rw [Nat.and_two_pow_sub_one_eq_mod _ 2]
  exact Nat.mod_lt _ (by omega)

private theorem checkPsyncInv4_step {t1 t2 : Transducer4} {invMask : UInt32}
    (hchk : checkPsyncInv4 t1 t2 invMask = true)
    {s1 s2 : Nat} (hs1 : s1 < 4) (hs2 : s2 < 4)
    (hin : maskHas invMask s1 s2 = true) (a b : Bool) :
    t1.stepOut s1 a b = t2.stepOut s2 a b ∧
    maskHas invMask (t1.stepNext s1 a b) (t2.stepNext s2 a b) = true := by
  unfold checkPsyncInv4 at hchk
  simp only [Bool.and_eq_true, List.all_eq_true] at hchk
  have hpair := hchk.2 s1 (List.mem_range.mpr hs1) s2 (List.mem_range.mpr hs2)
  unfold checkPairState at hpair
  rw [hin] at hpair
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, Bool.and_eq_true] at hpair
  have ha : a ∈ [false, true] := by cases a <;> simp
  have hb : b ∈ [false, true] := by cases b <;> simp
  have hab := hpair a ha b hb
  exact ⟨beq_iff_eq.mp hab.1, hab.2⟩

private theorem evalFrom_eq_of_inv {t1 t2 : Transducer4} {invMask : UInt32}
    (hchk : checkPsyncInv4 t1 t2 invMask = true) (inp : List (Bool × Bool)) :
    ∀ s1 s2, s1 < 4 → s2 < 4 → maskHas invMask s1 s2 = true →
      t1.evalFrom s1 inp = t2.evalFrom s2 inp := by
  induction inp with
  | nil => intro _ _ _ _ _; rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    intro s1 s2 hs1 hs2 hin
    have ⟨hout, hnext⟩ := checkPsyncInv4_step hchk hs1 hs2 hin a b
    simp only [Transducer4.evalFrom, hout]
    congr 1
    exact ih (t1.stepNext s1 a b) (t2.stepNext s2 a b)
      (stepNext_lt4 t1 s1 a b) (stepNext_lt4 t2 s2 a b) hnext

theorem psync4_sound (t1 t2 : Transducer4) (invMask : UInt32)
    (hchk : checkPsyncInv4 t1 t2 invMask = true) :
    ∀ inp : List (Bool × Bool), t1.eval inp = t2.eval inp := by
  intro inp
  have h0 : maskHas invMask 0 0 = true := by
    unfold checkPsyncInv4 at hchk; simp only [Bool.and_eq_true] at hchk; exact hchk.1
  exact evalFrom_eq_of_inv hchk inp 0 0 (by omega) (by omega) h0

theorem universal_carry_decomp :
    ∀ inp : List (Bool × Bool), tAdd.eval inp = tXorPlusTwiceAnd.eval inp :=
  psync4_sound tAdd tXorPlusTwiceAnd 0x61 (by decide)

-- ============================================================
-- Section 3: Universal Step-to-Target & Formal Obstructions
-- ============================================================

private theorem sqrtBit_sq_le (w : Nat) : (sqrtBit w) ^ 2 ≤ 2 * (2 ^ w) := by
  unfold sqrtBit
  rw [← Nat.pow_mul]
  have hexp : ((w + 1) / 2) * 2 ≤ w + 1 := by omega
  have h1 : 2 ^ (((w + 1) / 2) * 2) ≤ 2 ^ (w + 1) := Nat.pow_le_pow_right (by omega) hexp
  have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  exact h2 ▸ h1

theorem universal_step_envelope_implies_target
    (f E : Nat → Nat) (C B : Nat)
    (hbound : ∀ w : Nat, 1 ≤ w → f w ≤ E w)
    (henv : ∀ w : Nat, 1 ≤ w → E w ≤ C * sqrtBit w + B) :
    SqrtScaleTarget f := by
  intro k hk
  refine ⟨(2 * (C + B) ^ 2) ^ k, ?_⟩
  intro w hw
  have h1 : f w ≤ (C + B) * sqrtBit w := by
    have hfw := hbound w hw; have hew := henv w hw
    have hsb : 1 ≤ sqrtBit w := Nat.one_le_pow _ _ (by omega)
    have hB : B ≤ B * sqrtBit w := Nat.le_mul_of_pos_right B (by omega)
    rw [Nat.add_mul]; omega
  have hsq : (f w) ^ 2 ≤ (2 * (C + B) ^ 2) * (2 ^ w) := by
    have hp : (f w) ^ 2 ≤ ((C + B) * sqrtBit w) ^ 2 := Nat.pow_le_pow_left h1 2
    rw [Nat.mul_pow] at hp
    have hstep := Nat.mul_le_mul_left ((C + B) ^ 2) (sqrtBit_sq_le w)
    have hcomm : (C + B) ^ 2 * (2 * 2 ^ w) = (2 * (C + B) ^ 2) * (2 ^ w) := by
      rw [← Nat.mul_assoc, Nat.mul_comm ((C + B) ^ 2) 2]
    exact Nat.le_trans hp (hcomm ▸ hstep)
  have hpow := Nat.pow_le_pow_left hsq k
  rw [← Nat.pow_mul, Nat.mul_pow] at hpow
  have hgrow : (2 ^ w) ^ k ≤ (2 ^ w) ^ (k + 1) :=
    Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) (by omega)
  exact Nat.le_trans hpow (Nat.mul_le_mul_left _ hgrow)

private theorem two_pow_gt_nat (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem finite_window_blindness (f : Nat → Nat) (W0 : Nat) :
    ∃ g : Nat → Nat,
      (∀ w : Nat, w ≤ W0 → g w = f w) ∧ ¬ SqrtScaleTarget g := by
  let g : Nat → Nat := fun w => if w ≤ W0 then f w else 2 ^ w
  refine ⟨g, fun w hw => by dsimp [g]; simp [hw], ?_⟩
  intro htarget
  rcases htarget 2 (by omega) with ⟨C, hC⟩
  let w := W0 + C + 2
  have hle := hC w (by omega)
  have hg : g w = 2 ^ w := by
    dsimp [g]
    have hgt : ¬ (w ≤ W0) := by omega
    simp [hgt]
  rw [hg] at hle
  have hpow4 : (2 ^ w) ^ (2 * 2) = 2 ^ w * (2 ^ w) ^ (2 + 1) := by
    rw [show 2 * 2 = 3 + 1 by omega, show 2 + 1 = 3 by omega, Nat.pow_succ, Nat.mul_comm]
  rw [hpow4] at hle
  have h2le : 2 ^ w ≤ C := Nat.le_of_mul_le_mul_right hle (Nat.pow_pos (Nat.pow_pos (by omega)))
  have hlt := two_pow_gt_nat w
  omega

theorem bounded_envelope_obstruction (f E : Nat → Nat) (B : Nat)
    (hunb : ∀ M : Nat, ∃ w : Nat, 1 ≤ w ∧ M < f w)
    (hbnd : ∀ w : Nat, 1 ≤ w → E w ≤ B) :
    ¬ (∀ w : Nat, 1 ≤ w → f w ≤ E w) := by
  intro hall; rcases hunb B with ⟨w, hw1, hgt⟩
  have h1 := hall w hw1; have h2 := hbnd w hw1; omega

-- ============================================================
-- Section 4: BIN-4 Carry-Split Factorization Graph
-- ============================================================

private theorem listProd_append (xs ys : List Nat) :
    listProd (xs ++ ys) = listProd xs * listProd ys := by
  induction xs with
  | nil => simp [listProd]
  | cons x xs ih => simp [listProd, ih, Nat.mul_assoc]

private theorem isSplitPair_mul_le {a b d : Nat} (h : isSplitPair a b d = true) :
    a * b ≤ d := by
  unfold isSplitPair at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨_, _⟩, hmul | ⟨⟨⟨hodd, h7⟩, ha⟩, hb⟩⟩
  · omega
  · subst ha; subst hb; omega

private theorem oneStepSplit_flips_parity {xs ys : List Nat} (h : isOneStepSplit xs ys) :
    listParity ys = !listParity xs := by
  rcases h with ⟨pre, suf, d, a, b, rfl, rfl, _⟩
  unfold listParity
  simp only [List.length_append, List.length_cons]
  have hlen : (pre.length + (suf.length + 1 + 1)) % 2 = (pre.length + (suf.length + 1) + 1) % 2 := by omega
  rw [hlen]
  cases hmod : (pre.length + (suf.length + 1)) % 2 with
  | zero =>
    have h1 : (pre.length + (suf.length + 1) + 1) % 2 = 1 := by omega
    simp [h1]
  | succ k =>
    have hk : k = 0 := by omega
    subst hk
    have h0 : (pre.length + (suf.length + 1) + 1) % 2 = 0 := by omega
    simp [h0]

theorem carryMove_flips_parity {xs ys : List Nat} (h : isCarryMove xs ys) :
    listParity ys = !listParity xs := by
  rcases h with h1 | h2
  · exact oneStepSplit_flips_parity h1
  · have := oneStepSplit_flips_parity h2; cases hx : listParity xs <;> cases hy : listParity ys <;> simp_all

theorem oneStepSplit_preserves_valid {N : Nat} {xs ys : List Nat}
    (hvalid : validFactorList N xs = true) (hsplit : isOneStepSplit xs ys) :
    validFactorList N ys = true := by
  rcases hsplit with ⟨pre, suf, d, a, b, rfl, rfl, hpair⟩
  have hge : 2 ≤ a ∧ 2 ≤ b := by
    unfold isSplitPair at hpair
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hpair; exact hpair.1
  have hmul := isSplitPair_mul_le hpair
  unfold validFactorList at hvalid ⊢
  simp only [Bool.and_eq_true, List.all_append, List.all_cons, decide_eq_true_eq] at hvalid ⊢
  rcases hvalid with ⟨⟨hpre, ⟨_, hsuf⟩⟩, hprod⟩
  refine ⟨⟨hpre, ⟨hge.1, ⟨hge.2, hsuf⟩⟩⟩, ?_⟩
  rw [listProd_append] at hprod ⊢; simp only [listProd] at hprod ⊢
  have hstep : a * (b * listProd suf) ≤ d * listProd suf := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right (listProd suf) hmul
  exact Nat.le_trans (Nat.mul_le_mul_left (listProd pre) hstep) hprod

end SiliconNativeCert
