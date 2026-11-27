/-!
# Dyadic Skew-Congruence & Schur-Elimination Pfaffian Engine (`specmat-3`)

A standalone Lean 4.36.0 (zero Mathlib) pure-silicon infinite proof mechanism for
exact signed Pfaffians of bit-indexed skew-symmetric integer matrices.
-/

namespace SiliconPfaffian

-- ============================================================================
-- Section 1: Basic Combinatorics (`altSign`, `sumFin`, `prodFin`, `skip`)
-- ============================================================================

theorem fin_ne_of_val {n : Nat} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b :=
  fun heq => h (congrArg Fin.val heq)

def altSign (k : Nat) : Int :=
  if k % 2 = 0 then 1 else -1

@[simp] theorem altSign_zero : altSign 0 = 1 := rfl
@[simp] theorem altSign_one : altSign 1 = -1 := rfl

theorem altSign_succ (k : Nat) : altSign (k + 1) = -altSign k := by
  unfold altSign
  split <;> split <;> omega

theorem altSign_add (a b : Nat) : altSign (a + b) = altSign a * altSign b := by
  unfold altSign
  split <;> split <;> split <;> omega

theorem altSign_mul_self (k : Nat) : altSign k * altSign k = 1 := by
  unfold altSign
  split <;> decide

theorem altSign_two_mul (k : Nat) : altSign (2 * k) = 1 := by
  unfold altSign
  have : (2 * k) % 2 = 0 := by omega
  simp [this]

def sumFin : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | _ + 1, f => f ⟨0, Nat.zero_lt_succ _⟩ + sumFin (fun i => f i.succ)

def prodFin : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 1
  | _ + 1, f => f ⟨0, Nat.zero_lt_succ _⟩ * prodFin (fun i => f i.succ)

@[simp] theorem sumFin_zero (f : Fin 0 → Int) : sumFin f = 0 := rfl
@[simp] theorem prodFin_zero (f : Fin 0 → Int) : prodFin f = 1 := rfl

theorem sumFin_succ {n : Nat} (f : Fin (n + 1) → Int) :
    sumFin f = f ⟨0, Nat.zero_lt_succ n⟩ + sumFin (fun i => f i.succ) := rfl

theorem prodFin_succ {n : Nat} (f : Fin (n + 1) → Int) :
    prodFin f = f ⟨0, Nat.zero_lt_succ n⟩ * prodFin (fun i => f i.succ) := rfl

theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFin f = sumFin g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin_succ]
    rw [h ⟨0, Nat.zero_lt_succ n⟩, ih (fun i => h i.succ)]

theorem prodFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    prodFin f = prodFin g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prodFin_succ]
    rw [h ⟨0, Nat.zero_lt_succ n⟩, ih (fun i => h i.succ)]

theorem sumFin_eq_zero {n : Nat} {f : Fin n → Int} (h : ∀ i, f i = 0) :
    sumFin f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumFin_succ, h ⟨0, Nat.zero_lt_succ n⟩, ih (fun i => h i.succ)]
    rfl

theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin_succ, ih]
    omega

theorem sumFin_neg {n : Nat} (f : Fin n → Int) :
    sumFin (fun i => -f i) = -sumFin f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin_succ, ih]
    omega

theorem sumFin_sub {n : Nat} (f g : Fin n → Int) :
    sumFin (fun i => f i - g i) = sumFin f - sumFin g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin_succ, ih]
    omega

theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin (fun i => c * f i) = c * sumFin f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin_succ, ih, Int.mul_add]

theorem sumFin_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumFin (fun i => f i * c) = sumFin f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin_succ, ih, Int.add_mul]

theorem sumFin_comm {m n : Nat} (f : Fin m → Fin n → Int) :
    sumFin (fun i => sumFin (fun j => f i j)) = sumFin (fun j => sumFin (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumFin_zero]
    symm
    exact sumFin_eq_zero (fun _ => rfl)
  | succ m ih =>
    simp only [sumFin_succ, ih]
    rw [← sumFin_add]

theorem sumFin_single {n : Nat} (k : Fin n) (f : Fin n → Int)
    (h : ∀ i, i ≠ k → f i = 0) : sumFin f = f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    cases k using Fin.cases with
    | zero =>
      rw [sumFin_succ]
      have hz : sumFin (fun i : Fin n => f i.succ) = 0 :=
        sumFin_eq_zero (fun i => h i.succ (Fin.succ_ne_zero i))
      rw [hz, Int.add_zero]
      rfl
    | succ k' =>
      rw [sumFin_succ]
      have h0 : f ⟨0, Nat.zero_lt_succ n⟩ = 0 :=
        h ⟨0, Nat.zero_lt_succ n⟩ (Ne.symm (Fin.succ_ne_zero k'))
      rw [h0, Int.zero_add]
      exact ih k' (fun i => f i.succ) (fun i hi => h i.succ (fun heq => hi (Fin.succ_inj.mp heq)))

theorem prodFin_mul {n : Nat} (f g : Fin n → Int) :
    prodFin (fun i => f i * g i) = prodFin f * prodFin g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prodFin_succ, ih]
    ac_rfl

theorem prodFin_const {n : Nat} (c : Int) :
    prodFin (fun _ : Fin n => c) = c ^ n := by
  induction n with
  | zero => simp [prodFin]
  | succ n ih =>
    simp only [prodFin_succ, ih, Int.pow_succ, Int.mul_comm]

theorem sumFin_cast {n m : Nat} (h : n = m) (g : Fin m → Int) :
    sumFin (fun i : Fin n => g ⟨i.val, by omega⟩) = sumFin g := by
  subst h; exact sumFin_congr (fun _ => rfl)

theorem prodFin_cast {n m : Nat} (h : n = m) (g : Fin m → Int) :
    prodFin (fun i : Fin n => g ⟨i.val, by omega⟩) = prodFin g := by
  subst h; exact prodFin_congr (fun _ => rfl)

theorem sumFin_split {p q : Nat} (f : Fin (p + q) → Int) :
    sumFin f = sumFin (fun i : Fin p => f ⟨i.val, by omega⟩) +
               sumFin (fun j : Fin q => f ⟨p + j.val, by omega⟩) := by
  induction p with
  | zero =>
    simp only [sumFin_zero, Int.zero_add]
    rw [← sumFin_cast (Nat.zero_add q).symm f]
    exact sumFin_congr (fun j => congrArg f (Fin.ext (Nat.zero_add j.val).symm))
  | succ p ih =>
    rw [← sumFin_cast (show (p + q) + 1 = (p + 1) + q by omega) f]
    rw [sumFin_succ]
    have h1 := ih (fun x : Fin (p + q) => f ⟨x.val + 1, by omega⟩)
    have hstep : sumFin (fun x : Fin (p + q) => f ⟨x.succ.val, by omega⟩) =
                 sumFin (fun x : Fin (p + q) => f ⟨x.val + 1, by omega⟩) :=
      sumFin_congr (fun _ => rfl)
    rw [hstep, h1, sumFin_succ]
    have hL : sumFin (fun i : Fin p => f ⟨i.val + 1, by omega⟩) =
              sumFin (fun i : Fin p => f ⟨i.succ.val, by omega⟩) :=
      sumFin_congr (fun _ => rfl)
    have hR : sumFin (fun j : Fin q => f ⟨p + j.val + 1, by omega⟩) =
              sumFin (fun j : Fin q => f ⟨p + 1 + j.val, by omega⟩) :=
      sumFin_congr (fun j => by congr 1; apply Fin.ext; dsimp; omega)
    rw [hL, hR]
    omega

theorem prodFin_split {p q : Nat} (f : Fin (p + q) → Int) :
    prodFin f = prodFin (fun i : Fin p => f ⟨i.val, by omega⟩) *
                prodFin (fun j : Fin q => f ⟨p + j.val, by omega⟩) := by
  induction p with
  | zero =>
    simp only [prodFin_zero, Int.one_mul]
    rw [← prodFin_cast (Nat.zero_add q).symm f]
    exact prodFin_congr (fun j => congrArg f (Fin.ext (Nat.zero_add j.val).symm))
  | succ p ih =>
    rw [← prodFin_cast (show (p + q) + 1 = (p + 1) + q by omega) f]
    rw [prodFin_succ]
    have h1 := ih (fun x : Fin (p + q) => f ⟨x.val + 1, by omega⟩)
    have hstep : prodFin (fun x : Fin (p + q) => f ⟨x.succ.val, by omega⟩) =
                 prodFin (fun x : Fin (p + q) => f ⟨x.val + 1, by omega⟩) :=
      prodFin_congr (fun _ => rfl)
    rw [hstep, h1, prodFin_succ]
    have hL : prodFin (fun i : Fin p => f ⟨i.val + 1, by omega⟩) =
              prodFin (fun i : Fin p => f ⟨i.succ.val, by omega⟩) :=
      prodFin_congr (fun _ => rfl)
    have hR : prodFin (fun j : Fin q => f ⟨p + j.val + 1, by omega⟩) =
              prodFin (fun j : Fin q => f ⟨p + 1 + j.val, by omega⟩) :=
      prodFin_congr (fun j => by congr 1; apply Fin.ext; dsimp; omega)
    rw [hL, hR, Int.mul_assoc]

/-- Swap two indices `a` and `b` in `Fin n`. -/
def swapIdx {n : Nat} (a b : Fin n) (i : Fin n) : Fin n :=
  if i = a then b else if i = b then a else i

theorem swapIdx_self {n : Nat} (a i : Fin n) : swapIdx a a i = i := by
  unfold swapIdx; split <;> simp_all

theorem swapIdx_comm {n : Nat} (a b i : Fin n) : swapIdx a b i = swapIdx b a i := by
  unfold swapIdx
  by_cases h1 : i = a <;> by_cases h2 : i = b <;> simp_all

theorem swapIdx_invol {n : Nat} (a b i : Fin n) : swapIdx a b (swapIdx a b i) = i := by
  unfold swapIdx
  by_cases h1 : i = a
  · subst h1; simp
  · by_cases h2 : i = b
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swapIdx_left {n : Nat} (a b : Fin n) : swapIdx a b a = b := by
  unfold swapIdx; simp

theorem swapIdx_right {n : Nat} (a b : Fin n) : swapIdx a b b = a := by
  unfold swapIdx; by_cases h : b = a <;> simp [h]

theorem swapIdx_other {n : Nat} {a b i : Fin n} (h1 : i ≠ a) (h2 : i ≠ b) :
    swapIdx a b i = i := by
  unfold swapIdx; simp [h1, h2]

theorem sumFin_swapAdj {n : Nat} (k : Nat) (hk : k + 1 < n) (f : Fin n → Int) :
    sumFin (fun i => f (swapIdx ⟨k, by omega⟩ ⟨k + 1, hk⟩ i)) = sumFin f := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      cases n with
      | zero => omega
      | succ n' =>
        rw [sumFin_succ, sumFin_succ, sumFin_succ, sumFin_succ]
        have h0 : swapIdx (⟨0, by omega⟩ : Fin (n' + 2)) ⟨1, hk⟩ ⟨0, by omega⟩ = ⟨1, hk⟩ :=
          swapIdx_left _ _
        have h1 : swapIdx (⟨0, by omega⟩ : Fin (n' + 2)) ⟨1, hk⟩
                  (⟨0, Nat.zero_lt_succ n'⟩ : Fin (n' + 1)).succ = ⟨0, by omega⟩ := by
          have heq : (⟨0, Nat.zero_lt_succ n'⟩ : Fin (n' + 1)).succ = ⟨1, hk⟩ := Fin.ext rfl
          rw [heq]; exact swapIdx_right _ _
        have hrest : ∀ i : Fin n',
            swapIdx (⟨0, by omega⟩ : Fin (n' + 2)) ⟨1, hk⟩ i.succ.succ = i.succ.succ := by
          intro i
          exact swapIdx_other
            (fin_ne_of_val (by simp [Fin.succ]))
            (fin_ne_of_val (by simp [Fin.succ]))
        have heq1 : (⟨0, Nat.zero_lt_succ n'⟩ : Fin (n' + 1)).succ = ⟨1, hk⟩ := Fin.ext rfl
        rw [h0, h1, heq1]
        have hc : sumFin (fun i : Fin n' => f (swapIdx ⟨0, by omega⟩ ⟨1, hk⟩ i.succ.succ)) =
                  sumFin (fun i : Fin n' => f i.succ.succ) :=
          sumFin_congr (fun i => by rw [hrest i])
        rw [hc]
        omega
    | succ k' =>
      rw [sumFin_succ, sumFin_succ]
      have h0 : swapIdx (⟨k' + 1, by omega⟩ : Fin (n + 1)) ⟨k' + 2, hk⟩ ⟨0, Nat.zero_lt_succ n⟩ =
                ⟨0, Nat.zero_lt_succ n⟩ :=
        swapIdx_other (fin_ne_of_val (by dsimp; omega)) (fin_ne_of_val (by dsimp; omega))
      rw [h0]
      have hstep : ∀ i : Fin n,
          swapIdx ⟨k' + 1, by omega⟩ ⟨k' + 2, hk⟩ i.succ =
          (swapIdx ⟨k', by omega⟩ ⟨k' + 1, by omega⟩ i).succ := by
        intro i
        apply Fin.ext
        unfold swapIdx
        by_cases h1 : i.val = k'
        · simp [Fin.succ, Fin.ext_iff, h1]
        · by_cases h2 : i.val = k' + 1
          · simp [Fin.succ, Fin.ext_iff, h2]
          · simp [Fin.succ, Fin.ext_iff, h1, h2]
      have hc : sumFin (fun i : Fin n => f (swapIdx ⟨k' + 1, by omega⟩ ⟨k' + 2, hk⟩ i.succ)) =
                sumFin (fun i : Fin n => f (swapIdx ⟨k', by omega⟩ ⟨k' + 1, by omega⟩ i).succ) :=
        sumFin_congr (fun i => by rw [hstep i])
      rw [hc, ih k' (by omega) (fun i => f i.succ)]

/-- Embed `Fin n` into `Fin (n + 1)` skipping index `k`. -/
def skip {n : Nat} (k : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if h : i.val < k.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

theorem skip_val_lt {n : Nat} {k : Fin (n + 1)} {i : Fin n} (h : i.val < k.val) :
    (skip k i).val = i.val := by
  unfold skip; simp [h]

theorem skip_val_ge {n : Nat} {k : Fin (n + 1)} {i : Fin n} (h : ¬ i.val < k.val) :
    (skip k i).val = i.val + 1 := by
  unfold skip; simp [h]

theorem skip_ne {n : Nat} (k : Fin (n + 1)) (i : Fin n) : skip k i ≠ k := by
  unfold skip; intro h; split at h <;> (have := congrArg Fin.val h; dsimp at this; omega)

theorem skip_inj {n : Nat} {k : Fin (n + 1)} {i j : Fin n} (h : skip k i = skip k j) : i = j := by
  unfold skip at h
  apply Fin.ext
  split at h <;> split at h <;> (have := congrArg Fin.val h; dsimp at this; omega)

theorem skip_zero {n : Nat} (i : Fin n) : skip ⟨0, Nat.zero_lt_succ n⟩ i = i.succ := by
  unfold skip; apply Fin.ext; simp [Fin.succ]

/-- Embed `Fin n` into `Fin (n + 2)` skipping `0` and `j.succ`. -/
def skip0And {n : Nat} (j : Fin (n + 1)) (i : Fin n) : Fin (n + 2) :=
  (skip j i).succ

theorem skip0And_ne_zero {n : Nat} (j : Fin (n + 1)) (i : Fin n) :
    skip0And j i ≠ ⟨0, Nat.zero_lt_succ (n + 1)⟩ :=
  Fin.succ_ne_zero _

theorem skip0And_ne_succ {n : Nat} (j : Fin (n + 1)) (i : Fin n) :
    skip0And j i ≠ j.succ := by
  intro h
  exact skip_ne j i (Fin.succ_inj.mp h)

theorem skip0And_zero {n : Nat} (i : Fin n) :
    skip0And ⟨0, Nat.zero_lt_succ n⟩ i = i.succ.succ := by
  unfold skip0And; rw [skip_zero]

theorem skip_skip_comm_lt {n : Nat} (a : Fin (n + 2)) (b : Fin (n + 1))
    (h : b.val < a.val) (i : Fin n) :
    skip a (skip ⟨b.val, by omega⟩ i) = skip ⟨b.val, by omega⟩ (skip ⟨a.val - 1, by omega⟩ i) := by
  apply Fin.ext
  unfold skip
  by_cases h1 : i.val < b.val
  · have h2 : i.val < a.val - 1 := by omega
    have h3 : i.val < a.val := by omega
    simp [h1, h2, h3]
  · by_cases h2 : i.val < a.val - 1
    · have h3 : i.val + 1 < a.val := by omega
      simp [h1, h2, h3]
    · have h3 : ¬ (i.val + 1 < a.val) := by omega
      have h4 : ¬ (i.val + 1 < b.val) := by omega
      simp [h1, h2, h3, h4]

/-- Extract the unique preimage of `x ≠ k` under `skip k`. -/
def unskip {n : Nat} (k x : Fin (n + 1)) (h : x ≠ k) : Fin n :=
  if hlt : x.val < k.val then ⟨x.val, by omega⟩ else ⟨x.val - 1, by
    have : x.val ≠ k.val := fun heq => h (Fin.ext heq)
    omega⟩

theorem skip_unskip {n : Nat} (k x : Fin (n + 1)) (h : x ≠ k) :
    skip k (unskip k x h) = x := by
  apply Fin.ext
  unfold skip unskip
  have hne : x.val ≠ k.val := fun heq => h (Fin.ext heq)
  by_cases hlt : x.val < k.val
  · simp [hlt]
  · have hge : ¬ (x.val - 1 < k.val) := by omega
    simp [hlt, hge]
    omega

theorem sumFin_skip {k : Nat} (u : Fin (k + 1)) (h : Fin (k + 1) → Int) :
    sumFin h = h u + sumFin (fun b : Fin k => h (skip u b)) := by
  induction k with
  | zero =>
    have hu : u = ⟨0, Nat.zero_lt_succ 0⟩ := Fin.ext (by omega)
    rw [hu]; simp [sumFin]
  | succ k ih =>
    cases u using Fin.cases with
    | zero =>
      rw [sumFin_succ]
      exact congrArg (h ⟨0, Nat.zero_lt_succ (k + 1)⟩ + ·)
        (sumFin_congr (fun b => congrArg h (skip_zero b).symm))
    | succ u' =>
      rw [sumFin_succ, ih u' (fun x => h x.succ)]
      have h0 : skip u'.succ ⟨0, Nat.zero_lt_succ k⟩ = ⟨0, Nat.zero_lt_succ (k + 1)⟩ := by
        unfold skip; apply Fin.ext; simp [Fin.succ]
      have hsucc : ∀ b : Fin k, skip u'.succ b.succ = (skip u' b).succ := by
        intro b; unfold skip; apply Fin.ext
        by_cases hlt : b.val < u'.val
        · have hlt' : b.val + 1 < u'.val + 1 := by omega
          simp [hlt, hlt', Fin.succ]
        · have hlt' : ¬ (b.val + 1 < u'.val + 1) := by omega
          simp [hlt, hlt', Fin.succ]
      rw [sumFin_succ, h0]
      have hc : sumFin (fun b : Fin k => h (skip u'.succ b.succ)) =
                sumFin (fun b : Fin k => h (skip u' b).succ) :=
        sumFin_congr (fun b => by rw [hsucc b])
      rw [hc]
      omega

-- ============================================================================
-- Section 2: Matrices, Skew-Symmetry, Combinatorial Pfaffian & Determinant
-- ============================================================================

abbrev Mat (n : Nat) := Fin n → Fin n → Int

def IsSkew {n : Nat} (A : Mat n) : Prop :=
  (∀ i, A i i = 0) ∧ (∀ i j, A i j = -A j i)

def matMul {m p n : Nat} (A : Fin m → Fin p → Int) (B : Fin p → Fin n → Int) :
    Fin m → Fin n → Int :=
  fun i j => sumFin (fun k => A i k * B k j)

def matTrans {m n : Nat} (A : Fin m → Fin n → Int) : Fin n → Fin m → Int :=
  fun i j => A j i

def matId (n : Nat) : Mat n :=
  fun i j => if i = j then 1 else 0

def congruence {n : Nat} (P A : Mat n) : Mat n :=
  matMul (matTrans P) (matMul A P)

theorem matMul_assoc {a b c d : Nat}
    (A : Fin a → Fin b → Int) (B : Fin b → Fin c → Int) (C : Fin c → Fin d → Int) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i l
  unfold matMul
  simp only [← sumFin_mul_right, ← sumFin_mul_left]
  rw [sumFin_comm]
  exact sumFin_congr (fun j => sumFin_congr (fun k => Int.mul_assoc _ _ _))

theorem matTrans_mul {a b c : Nat}
    (A : Fin a → Fin b → Int) (B : Fin b → Fin c → Int) :
    matTrans (matMul A B) = matMul (matTrans B) (matTrans A) := by
  funext i j
  unfold matTrans matMul
  exact sumFin_congr (fun k => Int.mul_comm _ _)

theorem congruence_comp {n : Nat} (P Q A : Mat n) :
    congruence (matMul P Q) A = congruence Q (congruence P A) := by
  unfold congruence
  rw [matTrans_mul, matMul_assoc, matMul_assoc, matMul_assoc]

theorem congruence_id {n : Nat} (A : Mat n) : congruence (matId n) A = A := by
  funext i j
  unfold congruence matMul matTrans matId
  have h1 : ∀ k : Fin n, sumFin (fun l => A k l * (if l = j then 1 else 0)) = A k j := by
    intro k
    rw [sumFin_single j _ (fun l hl => by simp [hl])]
    simp
  simp only [h1]
  rw [sumFin_single i _ (fun k hk => by simp [hk])]
  simp

theorem isSkew_congruence {n : Nat} (P A : Mat n) (hA : IsSkew A) :
    IsSkew (congruence P A) := by
  constructor
  · intro i
    unfold congruence matMul matTrans
    simp only [← sumFin_mul_left]
    have hneg : sumFin (fun k => sumFin (fun l => P k i * (A k l * P l i))) =
                -sumFin (fun k => sumFin (fun l => P k i * (A k l * P l i))) := by
      calc sumFin (fun k => sumFin (fun l => P k i * (A k l * P l i)))
          = sumFin (fun l => sumFin (fun k => P k i * (A k l * P l i))) := sumFin_comm _
        _ = -sumFin (fun l => sumFin (fun k => P l i * (A l k * P k i))) := by
            rw [← sumFin_neg]
            apply sumFin_congr; intro l
            rw [← sumFin_neg]
            apply sumFin_congr; intro k
            rw [hA.2 k l, Int.neg_mul, Int.mul_neg]
            congr 1; ac_rfl
    omega
  · intro i j
    unfold congruence matMul matTrans
    simp only [← sumFin_mul_left]
    rw [sumFin_comm, ← sumFin_neg]
    apply sumFin_congr; intro l
    rw [← sumFin_neg]
    apply sumFin_congr; intro k
    rw [hA.2 k l, Int.neg_mul, Int.mul_neg]
    congr 1; ac_rfl

/-- Exact combinatorial Pfaffian defined by recursive row-0 Laplace expansion. -/
def pfaffian : (m : Nat) → Mat (2 * m) → Int
  | 0, _ => 1
  | m + 1, A =>
    sumFin (fun j : Fin (2 * m + 1) =>
      altSign j.val * A ⟨0, Nat.zero_lt_succ (2 * m + 1)⟩ j.succ *
      pfaffian m (fun r c => A (skip0And j r) (skip0And j c)))

theorem pfaffian_congr {m : Nat} {A B : Mat (2 * m)} (h : ∀ i j, A i j = B i j) :
    pfaffian m A = pfaffian m B := by
  have : A = B := funext (fun i => funext (fun j => h i j))
  rw [this]

/-- Cast a `Mat n` along `n = m`. -/
def castMat {n m : Nat} (h : n = m) (A : Mat n) : Mat m :=
  fun i j => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

theorem pfaffian_castMat {m1 m2 : Nat} (h : m1 = m2) (A : Mat (2 * m1)) :
    pfaffian m2 (castMat (by omega) A) = pfaffian m1 A := by
  subst h
  exact pfaffian_congr (fun _ _ => rfl)

-- ============================================================================
-- Section 3: Elementary Congruence Operations & Pfaffian Invariance
-- ============================================================================

def scaleRC {n : Nat} (a : Fin n) (c : Int) (A : Mat n) : Mat n :=
  fun i j => (if i = a then c else 1) * A i j * (if j = a then c else 1)

def swapRC {n : Nat} (a b : Fin n) (A : Mat n) : Mat n :=
  fun i j => A (swapIdx a b i) (swapIdx a b j)

def shearRC {n : Nat} (a b : Fin n) (c : Int) (A : Mat n) : Mat n :=
  fun i j =>
    A i j + (if i = a then c * A b j else 0) + (if j = a then c * A i b else 0) +
    (if i = a ∧ j = a then c * c * A b b else 0)

def elemScale {n : Nat} (a : Fin n) (c : Int) : Mat n :=
  fun i j => if i = j then (if i = a then c else 1) else 0

def elemSwap {n : Nat} (a b : Fin n) : Mat n :=
  fun i j => if i = swapIdx a b j then 1 else 0

def elemShear {n : Nat} (a b : Fin n) (c : Int) : Mat n :=
  fun i j => (if i = j then 1 else 0) + (if i = b ∧ j = a then c else 0)

theorem congruence_elemScale {n : Nat} (a : Fin n) (c : Int) (A : Mat n) :
    congruence (elemScale a c) A = scaleRC a c A := by
  funext i j
  unfold congruence matMul matTrans elemScale scaleRC
  have h1 : ∀ k : Fin n,
      sumFin (fun l => A k l * (if l = j then (if l = a then c else 1) else 0)) =
      A k j * (if j = a then c else 1) := by
    intro k
    rw [sumFin_single j _ (fun l hl => by simp [hl])]
    simp
  simp only [h1]
  rw [sumFin_single i _ (fun k hk => by simp [hk])]
  simp [Int.mul_assoc]

theorem congruence_elemSwap {n : Nat} (a b : Fin n) (A : Mat n) :
    congruence (elemSwap a b) A = swapRC a b A := by
  funext i j
  unfold congruence matMul matTrans elemSwap swapRC
  have h1 : ∀ k : Fin n,
      sumFin (fun l => A k l * (if l = swapIdx a b j then 1 else 0)) =
      A k (swapIdx a b j) := by
    intro k
    rw [sumFin_single (swapIdx a b j) _ (fun l hl => by simp [hl])]
    simp
  simp only [h1]
  rw [sumFin_single (swapIdx a b i) _ (fun k hk => by simp [hk])]
  simp

theorem congruence_elemShear {n : Nat} (a b : Fin n) (c : Int) (A : Mat n) :
    congruence (elemShear a b c) A = shearRC a b c A := by
  funext i j
  unfold congruence matMul matTrans elemShear shearRC
  have h1 : ∀ k : Fin n,
      sumFin (fun l => A k l * ((if l = j then 1 else 0) + (if l = b ∧ j = a then c else 0))) =
      A k j + (if j = a then c * A k b else 0) := by
    intro k
    have hsplit : ∀ l : Fin n,
        A k l * ((if l = j then 1 else 0) + (if l = b ∧ j = a then c else 0)) =
        A k l * (if l = j then 1 else 0) + A k l * (if l = b ∧ j = a then c else 0) :=
      fun l => Int.mul_add _ _ _
    rw [sumFin_congr hsplit, sumFin_add]
    rw [sumFin_single j _ (fun l hl => by simp [hl])]
    rw [sumFin_single b _ (fun l hl => by simp [hl])]
    by_cases hja : j = a <;> simp [hja, Int.mul_comm]
  simp only [h1]
  have hsplit2 : ∀ k : Fin n,
      ((if k = i then 1 else 0) + (if k = b ∧ i = a then c else 0)) *
        (A k j + (if j = a then c * A k b else 0)) =
      (if k = i then 1 else 0) * (A k j + (if j = a then c * A k b else 0)) +
      (if k = b ∧ i = a then c else 0) * (A k j + (if j = a then c * A k b else 0)) :=
    fun k => Int.add_mul _ _ _
  rw [sumFin_congr hsplit2, sumFin_add]
  rw [sumFin_single i _ (fun k hk => by simp [hk])]
  rw [sumFin_single b _ (fun k hk => by simp [hk])]
  by_cases hia : i = a <;> by_cases hja : j = a
  · simp [hia, hja, Int.mul_add, Int.mul_assoc]; omega
  · simp [hia, hja]
  · simp [hia, hja]
  · simp [hia, hja]

theorem isSkew_scaleRC {n : Nat} (a : Fin n) (c : Int) {A : Mat n} (hA : IsSkew A) :
    IsSkew (scaleRC a c A) := by
  rw [← congruence_elemScale]; exact isSkew_congruence _ _ hA

theorem isSkew_swapRC {n : Nat} (a b : Fin n) {A : Mat n} (hA : IsSkew A) :
    IsSkew (swapRC a b A) := by
  rw [← congruence_elemSwap]; exact isSkew_congruence _ _ hA

theorem isSkew_shearRC {n : Nat} (a b : Fin n) (c : Int) {A : Mat n} (hA : IsSkew A) :
    IsSkew (shearRC a b c A) := by
  rw [← congruence_elemShear]; exact isSkew_congruence _ _ hA

-- 3.1 Scaling lemma for `pfaffian`
theorem pfaffian_scaleRC {m : Nat} (a : Fin (2 * m)) (c : Int) (A : Mat (2 * m)) :
    pfaffian m (scaleRC a c A) = c * pfaffian m A := by
  induction m with
  | zero => exact Fin.elim0 a
  | succ m ih =>
    simp only [pfaffian]
    cases a using Fin.cases with
    | zero =>
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro j
      have hz0 : (0 : Fin (2 * m + 2)) = ⟨0, Nat.zero_lt_succ (2 * m + 1)⟩ := rfl
      rw [hz0]
      have hne : j.succ ≠ ⟨0, Nat.zero_lt_succ (2 * m + 1)⟩ := Fin.succ_ne_zero j
      have hsub : pfaffian m (fun r c' => scaleRC ⟨0, Nat.zero_lt_succ (2 * m + 1)⟩ c A (skip0And j r) (skip0And j c')) =
                  pfaffian m (fun r c' => A (skip0And j r) (skip0And j c')) :=
        pfaffian_congr (fun r c' => by
          unfold scaleRC
          simp only [skip0And_ne_zero, ↓reduceIte, Int.one_mul, Int.mul_one])
      rw [hsub]
      unfold scaleRC
      simp only [hne, ↓reduceIte, Int.mul_one]
      ac_rfl
    | succ a' =>
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro j
      have h0ne : (⟨0, Nat.zero_lt_succ (2 * m + 1)⟩ : Fin (2 * m + 2)) ≠ a'.succ :=
        Ne.symm (Fin.succ_ne_zero a')
      by_cases hj : j = a'
      · rw [hj]
        have hsub : pfaffian m (fun r c' => scaleRC a'.succ c A (skip0And a' r) (skip0And a' c')) =
                    pfaffian m (fun r c' => A (skip0And a' r) (skip0And a' c')) :=
          pfaffian_congr (fun r c' => by
            unfold scaleRC
            simp only [skip0And_ne_succ, ↓reduceIte, Int.one_mul, Int.mul_one])
        rw [hsub]
        unfold scaleRC
        simp only [h0ne, ↓reduceIte, Int.one_mul]
        ac_rfl
      · have hjsne : j.succ ≠ a'.succ := fun h => hj (Fin.succ_inj.mp h)
        let b : Fin (2 * m) := unskip j a' (Ne.symm hj)
        have hb : skip0And j b = a'.succ := by
          unfold skip0And b; rw [skip_unskip]
        have hsub : pfaffian m (fun r c' => scaleRC a'.succ c A (skip0And j r) (skip0And j c')) =
                    pfaffian m (scaleRC b c (fun r c' => A (skip0And j r) (skip0And j c'))) :=
          pfaffian_congr (fun r c' => by
            unfold scaleRC
            have hr : (skip0And j r = a'.succ) ↔ (r = b) := by
              rw [← hb]
              constructor
              · intro heq; exact skip_inj (Fin.succ_inj.mp heq)
              · intro heq; rw [heq]
            have hc' : (skip0And j c' = a'.succ) ↔ (c' = b) := by
              rw [← hb]
              constructor
              · intro heq; exact skip_inj (Fin.succ_inj.mp heq)
              · intro heq; rw [heq]
            simp only [hr, hc'])
        rw [hsub, ih b]
        unfold scaleRC
        simp only [h0ne, hjsne, ↓reduceIte, Int.one_mul, Int.mul_one]
        ac_rfl

-- 3.2 Two-level expansion of `pfaffian (m + 2)`
def skip01Pair {n : Nat} (a : Fin (n + 2)) (b : Fin (n + 1)) (i : Fin n) : Fin (n + 4) :=
  (skip a (skip b i)).succ.succ

theorem skip0And_skip0And {n : Nat} (a : Fin (n + 2)) (b : Fin (n + 1)) (i : Fin n) :
    skip0And a.succ (skip0And b i) = skip01Pair a b i := by
  unfold skip0And skip01Pair skip
  apply Fin.ext
  by_cases h1 : i.val < b.val
  · by_cases h2 : i.val < a.val
    · have h3 : i.val + 1 < a.val + 1 := by omega
      simp [h1, h2, h3, Fin.succ]
    · have h3 : ¬ (i.val + 1 < a.val + 1) := by omega
      simp [h1, h2, h3, Fin.succ]
  · by_cases h2 : i.val + 1 < a.val
    · have h3 : i.val + 2 < a.val + 1 := by omega
      simp [h1, h2, h3, Fin.succ]
    · have h3 : ¬ (i.val + 2 < a.val + 1) := by omega
      simp [h1, h2, h3, Fin.succ]

theorem skip0And_succ_zero {n : Nat} (a : Fin (n + 2)) :
    skip0And a.succ ⟨0, Nat.zero_lt_succ (n + 1)⟩ = ⟨1, by omega⟩ := by
  unfold skip0And skip
  apply Fin.ext
  simp [Fin.succ]

theorem skip0And_succ_succ {n : Nat} (a : Fin (n + 2)) (b : Fin (n + 1)) :
    skip0And a.succ b.succ = (skip a b).succ.succ := by
  unfold skip0And skip
  apply Fin.ext
  by_cases h : b.val < a.val
  · have h' : b.val + 1 < a.val + 1 := by omega
    simp [h, h', Fin.succ]
  · have h' : ¬ (b.val + 1 < a.val + 1) := by omega
    simp [h, h', Fin.succ]

theorem pfaffian_expand2 {m : Nat} (A : Mat (2 * (m + 2))) :
    pfaffian (m + 2) A =
      A ⟨0, by omega⟩ ⟨1, by omega⟩ *
        pfaffian (m + 1) (fun r c => A r.succ.succ c.succ.succ) -
      sumFin (fun a : Fin (2 * m + 2) =>
        sumFin (fun b : Fin (2 * m + 1) =>
          altSign a.val * altSign b.val *
          A ⟨0, by omega⟩ a.succ.succ *
          A ⟨1, by omega⟩ (skip a b).succ.succ *
          pfaffian m (fun r c => A (skip01Pair a b r) (skip01Pair a b c)))) := by
  change sumFin (fun j : Fin (2 * m + 3) =>
      altSign j.val * A ⟨0, by omega⟩ j.succ *
      pfaffian (m + 1) (fun r c => A (skip0And j r) (skip0And j c))) = _
  rw [sumFin_succ]
  have h0 : altSign 0 * A ⟨0, by omega⟩ (⟨0, Nat.zero_lt_succ (2 * m + 2)⟩ : Fin (2 * m + 3)).succ *
      pfaffian (m + 1) (fun r c => A (skip0And ⟨0, Nat.zero_lt_succ (2 * m + 2)⟩ r)
                                     (skip0And ⟨0, Nat.zero_lt_succ (2 * m + 2)⟩ c)) =
      A ⟨0, by omega⟩ ⟨1, by omega⟩ *
      pfaffian (m + 1) (fun r c => A r.succ.succ c.succ.succ) := by
    simp only [altSign_zero, Int.one_mul]
    exact congrArg (A ⟨0, by omega⟩ ⟨1, by omega⟩ * ·)
      (pfaffian_congr (fun r c => by rw [skip0And_zero, skip0And_zero]))
  rw [h0]
  have hrest :
      sumFin (fun a : Fin (2 * m + 2) =>
        altSign a.succ.val * A ⟨0, by omega⟩ a.succ.succ *
        pfaffian (m + 1) (fun r c => A (skip0And a.succ r) (skip0And a.succ c))) =
      -sumFin (fun a : Fin (2 * m + 2) =>
        sumFin (fun b : Fin (2 * m + 1) =>
          altSign a.val * altSign b.val *
          A ⟨0, by omega⟩ a.succ.succ *
          A ⟨1, by omega⟩ (skip a b).succ.succ *
          pfaffian m (fun r c => A (skip01Pair a b r) (skip01Pair a b c)))) := by
    rw [← sumFin_neg]
    apply sumFin_congr; intro a
    change altSign (a.val + 1) * A ⟨0, by omega⟩ a.succ.succ *
      sumFin (fun b : Fin (2 * m + 1) =>
        altSign b.val *
        A (skip0And a.succ ⟨0, Nat.zero_lt_succ (2 * m + 1)⟩) (skip0And a.succ b.succ) *
        pfaffian m (fun r c => A (skip0And a.succ (skip0And b r)) (skip0And a.succ (skip0And b c)))) = _
    rw [altSign_succ, Int.neg_mul, Int.neg_mul]
    congr 1
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro b
    rw [skip0And_succ_zero, skip0And_succ_succ]
    have hsub : pfaffian m (fun r c => A (skip0And a.succ (skip0And b r)) (skip0And a.succ (skip0And b c))) =
                pfaffian m (fun r c => A (skip01Pair a b r) (skip01Pair a b c)) :=
      pfaffian_congr (fun r c => by rw [skip0And_skip0And, skip0And_skip0And])
    rw [hsub]
    simp only [Int.mul_assoc]
    rw [Int.mul_left_comm (A ⟨0, by omega⟩ a.succ.succ) (altSign b.val)]
  rw [hrest, Int.sub_eq_add_neg]

theorem sumFin_double_swap_pair {n : Nat}
    (g : Fin (n + 2) → Fin (n + 2) → (Fin n → Fin (n + 4)) → Int)
    (hg_sub : ∀ (a : Fin (n + 2)) (b : Fin (n + 1)) (h : a ≠ skip a b),
      g (skip a b) a (skip01Pair (skip a b) (unskip (skip a b) a h)) =
      g (skip a b) a (skip01Pair a b)) :
    sumFin (fun a : Fin (n + 2) =>
      sumFin (fun b : Fin (n + 1) =>
        altSign a.val * altSign b.val * g a (skip a b) (skip01Pair a b))) =
    -sumFin (fun a : Fin (n + 2) =>
      sumFin (fun b : Fin (n + 1) =>
        altSign a.val * altSign b.val * g (skip a b) a (skip01Pair a b))) := by
  let F : Fin (n + 2) → Fin (n + 2) → Int := fun u v =>
    if h : u = v then 0
    else if hlt : u.val < v.val then
      -altSign u.val * altSign v.val * g u v (skip01Pair u ⟨v.val - 1, by omega⟩)
    else
      altSign u.val * altSign v.val * g u v (skip01Pair u ⟨v.val, by
        have : u.val ≠ v.val := fun heq => h (Fin.ext heq); omega⟩)
  have hLHS : ∀ u : Fin (n + 2),
      sumFin (fun b : Fin (n + 1) => altSign u.val * altSign b.val * g u (skip u b) (skip01Pair u b)) =
      sumFin (fun v : Fin (n + 2) => F u v) := by
    intro u
    rw [sumFin_skip u (F u)]
    have hdiag : F u u = 0 := by simp [F]
    rw [hdiag, Int.zero_add]
    apply sumFin_congr; intro b
    dsimp only [F]
    have hne : u ≠ skip u b := Ne.symm (skip_ne u b)
    simp only [hne, ↓reduceDIte]
    by_cases hlt : b.val < u.val
    · have hv : (skip u b).val = b.val := skip_val_lt hlt
      have hnlt : ¬ (u.val < (skip u b).val) := by omega
      simp only [hnlt, ↓reduceDIte]
      have hbf : (⟨(skip u b).val, by omega⟩ : Fin (n + 1)) = b := Fin.ext hv
      rw [hbf, hv]
    · have hv : (skip u b).val = b.val + 1 := skip_val_ge hlt
      have hlt2 : u.val < (skip u b).val := by omega
      simp only [hlt2, ↓reduceDIte]
      have hbf : (⟨(skip u b).val - 1, by omega⟩ : Fin (n + 1)) = b := Fin.ext (by dsimp; omega)
      rw [hbf, hv, altSign_succ]
      have : -altSign u.val * -altSign b.val = altSign u.val * altSign b.val := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [this]
  have hRHS : ∀ u : Fin (n + 2),
      sumFin (fun b : Fin (n + 1) => altSign u.val * altSign b.val * g (skip u b) u (skip01Pair u b)) =
      sumFin (fun v : Fin (n + 2) => -F v u) := by
    intro u
    rw [sumFin_skip u (fun v => -F v u)]
    have hdiag : -F u u = 0 := by simp [F]
    rw [hdiag, Int.zero_add]
    apply sumFin_congr; intro b
    dsimp only [F]
    have hne : skip u b ≠ u := skip_ne u b
    have hne' : u ≠ skip u b := Ne.symm hne
    simp only [hne, ↓reduceDIte]
    have hsub_eq := hg_sub u b hne'
    by_cases hlt : b.val < u.val
    · have hv : (skip u b).val = b.val := skip_val_lt hlt
      have hlt2 : (skip u b).val < u.val := by omega
      simp only [hlt2, ↓reduceDIte]
      have hun : unskip (skip u b) u hne' = ⟨u.val - 1, by omega⟩ := by
        unfold unskip; apply Fin.ext
        have hnot : ¬ (u.val < (skip u b).val) := by omega
        simp only [hnot, ↓reduceDIte]
      rw [← hun, hsub_eq, hv]
      rw [Int.neg_mul, Int.neg_mul, Int.neg_neg]
      ac_rfl
    · have hv : (skip u b).val = b.val + 1 := skip_val_ge hlt
      have hnlt : ¬ ((skip u b).val < u.val) := by omega
      simp only [hnlt, ↓reduceDIte]
      have hun : unskip (skip u b) u hne' = ⟨u.val, by omega⟩ := by
        unfold unskip; apply Fin.ext
        have hlt3 : u.val < (skip u b).val := by omega
        simp only [hlt3, ↓reduceDIte]
      rw [← hun, hsub_eq, hv, altSign_succ]
      rw [Int.neg_mul, Int.neg_mul, Int.neg_neg]
      ac_rfl
  rw [sumFin_congr hLHS, sumFin_congr hRHS, sumFin_comm, ← sumFin_neg]
  apply sumFin_congr; intro u
  rw [← sumFin_neg]
  apply sumFin_congr; intro v
  rw [Int.neg_neg]

theorem skip01Pair_comm {n : Nat} (a : Fin (n + 2)) (b : Fin (n + 1)) (h : a ≠ skip a b) :
    skip01Pair (skip a b) (unskip (skip a b) a h) = skip01Pair a b := by
  funext i
  unfold skip01Pair unskip
  apply congrArg Fin.succ
  apply congrArg Fin.succ
  by_cases hlt : b.val < a.val
  · have hv : (skip a b).val = b.val := skip_val_lt hlt
    have hnlt : ¬ (a.val < (skip a b).val) := by omega
    simp only [hnlt, ↓reduceDIte]
    have hcomm := skip_skip_comm_lt a b hlt i
    have h1 : (⟨b.val, by omega⟩ : Fin (n + 1)) = b := Fin.ext rfl
    have h2 : (⟨b.val, by omega⟩ : Fin (n + 2)) = skip a b := Fin.ext hv.symm
    rw [h1, h2] at hcomm
    exact hcomm.symm
  · have hv : (skip a b).val = b.val + 1 := skip_val_ge hlt
    have hlt2 : a.val < (skip a b).val := by omega
    simp only [hlt2, ↓reduceDIte]
    have hcomm := skip_skip_comm_lt (skip a b) ⟨a.val, by omega⟩ (by omega) i
    have h1 : (⟨(skip a b).val - 1, by omega⟩ : Fin (n + 1)) = b := Fin.ext (by dsimp; omega)
    have h2 : (⟨a.val, by omega⟩ : Fin (n + 2)) = a := Fin.ext rfl
    have h3 : (⟨(⟨a.val, by omega⟩ : Fin (n + 1)).val, by omega⟩ : Fin (n + 1)) = ⟨a.val, by omega⟩ := Fin.ext rfl
    rw [h1, h2, h3] at hcomm
    exact hcomm

-- 3.3 Swap 0 and 1, adjacent swap, and arbitrary swap!
theorem pfaffian_swap01 {m : Nat} {A : Mat (2 * (m + 1))} (hA : IsSkew A) :
    pfaffian (m + 1) (swapRC ⟨0, by omega⟩ ⟨1, by omega⟩ A) = -pfaffian (m + 1) A := by
  cases m with
  | zero =>
    change altSign 0 * swapRC ⟨0, by omega⟩ ⟨1, by omega⟩ A ⟨0, by omega⟩ ⟨1, by omega⟩ * 1 + 0 =
           -(altSign 0 * A ⟨0, by omega⟩ ⟨1, by omega⟩ * 1 + 0)
    unfold swapRC
    have h0 : swapIdx (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩ ⟨0, by omega⟩ = ⟨1, by omega⟩ :=
      swapIdx_left _ _
    have h1 : swapIdx (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩ ⟨1, by omega⟩ = ⟨0, by omega⟩ :=
      swapIdx_right _ _
    rw [h0, h1, hA.2 ⟨1, by omega⟩ ⟨0, by omega⟩]
    simp
  | succ m' =>
    rw [pfaffian_expand2, pfaffian_expand2]
    have hs0 : swapIdx (⟨0, by omega⟩ : Fin (2 * (m' + 2))) ⟨1, by omega⟩ ⟨0, by omega⟩ = ⟨1, by omega⟩ :=
      swapIdx_left _ _
    have hs1 : swapIdx (⟨0, by omega⟩ : Fin (2 * (m' + 2))) ⟨1, by omega⟩ ⟨1, by omega⟩ = ⟨0, by omega⟩ :=
      swapIdx_right _ _
    have hss : ∀ x : Fin (2 * (m' + 1)),
        swapIdx (⟨0, by omega⟩ : Fin (2 * (m' + 2))) ⟨1, by omega⟩ x.succ.succ = x.succ.succ := by
      intro x
      exact swapIdx_other (fin_ne_of_val (by simp [Fin.succ])) (fin_ne_of_val (by simp [Fin.succ]))
    have hterm1 :
        swapRC ⟨0, by omega⟩ ⟨1, by omega⟩ A ⟨0, by omega⟩ ⟨1, by omega⟩ *
        pfaffian (m' + 1) (fun (r c : Fin (2 * (m' + 1))) =>
          swapRC ⟨0, by omega⟩ ⟨1, by omega⟩ A r.succ.succ c.succ.succ) =
        -(A ⟨0, by omega⟩ ⟨1, by omega⟩ *
          pfaffian (m' + 1) (fun (r c : Fin (2 * (m' + 1))) => A r.succ.succ c.succ.succ)) := by
      unfold swapRC
      rw [hs0, hs1, hA.2 ⟨1, by omega⟩ ⟨0, by omega⟩]
      have hsub : (fun (r c : Fin (2 * (m' + 1))) =>
                    A (swapIdx ⟨0, by omega⟩ ⟨1, by omega⟩ r.succ.succ)
                      (swapIdx ⟨0, by omega⟩ ⟨1, by omega⟩ c.succ.succ)) =
                  (fun (r c : Fin (2 * (m' + 1))) => A r.succ.succ c.succ.succ) := by
        funext r c; rw [hss r, hss c]
      rw [hsub, Int.neg_mul]
    rw [hterm1]
    have hsum_simp :
        sumFin (fun a : Fin (2 * m' + 2) =>
          sumFin (fun b : Fin (2 * m' + 1) =>
            altSign a.val * altSign b.val *
            swapRC ⟨0, by omega⟩ ⟨1, by omega⟩ A ⟨0, by omega⟩ a.succ.succ *
            swapRC ⟨0, by omega⟩ ⟨1, by omega⟩ A ⟨1, by omega⟩ (skip a b).succ.succ *
            pfaffian m' (fun r c => swapRC ⟨0, by omega⟩ ⟨1, by omega⟩ A (skip01Pair a b r) (skip01Pair a b c)))) =
        sumFin (fun a : Fin (2 * m' + 2) =>
          sumFin (fun b : Fin (2 * m' + 1) =>
            altSign a.val * altSign b.val *
            A ⟨1, by omega⟩ a.succ.succ *
            A ⟨0, by omega⟩ (skip a b).succ.succ *
            pfaffian m' (fun r c => A (skip01Pair a b r) (skip01Pair a b c)))) := by
      apply sumFin_congr; intro a
      apply sumFin_congr; intro b
      unfold swapRC
      rw [hs0, hs1, hss a, hss (skip a b)]
      have hsub : (fun (r c : Fin (2 * m')) =>
                    A (swapIdx ⟨0, by omega⟩ ⟨1, by omega⟩ (skip01Pair a b r))
                      (swapIdx ⟨0, by omega⟩ ⟨1, by omega⟩ (skip01Pair a b c))) =
                  (fun (r c : Fin (2 * m')) => A (skip01Pair a b r) (skip01Pair a b c)) := by
        funext r c; unfold skip01Pair; rw [hss, hss]
      rw [hsub]
    rw [hsum_simp]
    let g : Fin (2 * m' + 2) → Fin (2 * m' + 2) → (Fin (2 * m') → Fin (2 * m' + 4)) → Int :=
      fun u v f => A ⟨0, by omega⟩ u.succ.succ * A ⟨1, by omega⟩ v.succ.succ *
                   pfaffian m' (fun r c => A (f r) (f c))
    have hswap := sumFin_double_swap_pair g (fun a b h => by
      dsimp only [g]; rw [skip01Pair_comm a b h])
    have hL : sumFin (fun a : Fin (2 * m' + 2) =>
        sumFin (fun b : Fin (2 * m' + 1) =>
          altSign a.val * altSign b.val *
          A ⟨1, by omega⟩ a.succ.succ *
          A ⟨0, by omega⟩ (skip a b).succ.succ *
          pfaffian m' (fun r c => A (skip01Pair a b r) (skip01Pair a b c)))) =
        sumFin (fun a : Fin (2 * m' + 2) =>
          sumFin (fun b : Fin (2 * m' + 1) =>
            altSign a.val * altSign b.val * g (skip a b) a (skip01Pair a b))) := by
      apply sumFin_congr; intro a; apply sumFin_congr; intro b; dsimp only [g]; ac_rfl
    have hR : sumFin (fun a : Fin (2 * m' + 2) =>
        sumFin (fun b : Fin (2 * m' + 1) =>
          altSign a.val * altSign b.val *
          A ⟨0, by omega⟩ a.succ.succ *
          A ⟨1, by omega⟩ (skip a b).succ.succ *
          pfaffian m' (fun r c => A (skip01Pair a b r) (skip01Pair a b c)))) =
        sumFin (fun a : Fin (2 * m' + 2) =>
          sumFin (fun b : Fin (2 * m' + 1) =>
            altSign a.val * altSign b.val * g a (skip a b) (skip01Pair a b))) := by
      apply sumFin_congr; intro a; apply sumFin_congr; intro b; dsimp only [g]; ac_rfl
    rw [hL, hR, hswap]
    omega

theorem pfaffian_swapAdj {m : Nat} (k : Nat) (hk : k + 1 < 2 * m)
    {A : Mat (2 * m)} (hA : IsSkew A) :
    pfaffian m (swapRC ⟨k, by omega⟩ ⟨k + 1, hk⟩ A) = -pfaffian m A := by
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
    cases k with
    | zero => exact pfaffian_swap01 hA
    | succ p =>
      change sumFin (fun j : Fin (2 * m + 1) =>
        altSign j.val * swapRC ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ A ⟨0, by omega⟩ j.succ *
        pfaffian m (fun r c => swapRC ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ A (skip0And j r) (skip0And j c))) =
        -sumFin (fun j : Fin (2 * m + 1) =>
        altSign j.val * A ⟨0, by omega⟩ j.succ *
        pfaffian m (fun r c => A (skip0And j r) (skip0And j c)))
      let sp : Fin (2 * m + 1) → Fin (2 * m + 1) :=
        swapIdx ⟨p, by omega⟩ ⟨p + 1, by omega⟩
      rw [← sumFin_swapAdj p (by omega)]
      rw [← sumFin_neg]
      apply sumFin_congr; intro j
      have h0 : swapIdx (⟨p + 1, by omega⟩ : Fin (2 * m + 2)) ⟨p + 2, hk⟩ ⟨0, by omega⟩ = ⟨0, by omega⟩ :=
        swapIdx_other (fin_ne_of_val (by dsimp; omega)) (fin_ne_of_val (by dsimp; omega))
      have hsucc : ∀ x : Fin (2 * m + 1),
          swapIdx (⟨p + 1, by omega⟩ : Fin (2 * m + 2)) ⟨p + 2, hk⟩ x.succ = (sp x).succ := by
        intro x; apply Fin.ext; unfold sp swapIdx
        by_cases h1 : x.val = p
        · simp [Fin.succ, Fin.ext_iff, h1]
        · by_cases h2 : x.val = p + 1
          · simp [Fin.succ, Fin.ext_iff, h2]
          · simp [Fin.succ, Fin.ext_iff, h1, h2]
      unfold swapRC
      change altSign (sp j).val *
        A (swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ ⟨0, by omega⟩)
          (swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (sp j).succ) *
        pfaffian m (fun r c => A (swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And (sp j) r))
                                 (swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And (sp j) c))) = _
      have hsp_invol : sp (sp j) = j := swapIdx_invol _ _ j
      rw [h0, hsucc (sp j), hsp_invol]
      by_cases hjp : j.val = p
      · have hsp : sp j = ⟨p + 1, by omega⟩ := by
          apply Fin.ext; unfold sp swapIdx; simp [Fin.ext_iff, hjp]
        have hsub : ∀ r : Fin (2 * m),
            swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And (sp j) r) = skip0And j r := by
          intro r; unfold skip0And; rw [hsucc]; congr 1
          rw [hsp]; apply Fin.ext
          by_cases hr : r.val < p
          · have hr1 : r.val < p + 1 := by omega
            have hsk : skip ⟨p + 1, by omega⟩ r = ⟨r.val, by omega⟩ := by unfold skip; simp [hr1]
            rw [hsk]; unfold sp
            rw [swapIdx_other (fin_ne_of_val (by dsimp; omega)) (fin_ne_of_val (by dsimp; omega))]
            rw [skip_val_lt (by omega)]
          · by_cases hr0 : r.val = p
            · have hsk : skip ⟨p + 1, by omega⟩ r = ⟨p, by omega⟩ := by
                unfold skip; apply Fin.ext; simp [hr0]
              rw [hsk]; unfold sp; rw [swapIdx_left, skip_val_ge (by omega)]; dsimp; omega
            · have hr1 : ¬ (r.val < p + 1) := by omega
              have hsk : skip ⟨p + 1, by omega⟩ r = ⟨r.val + 1, by omega⟩ := by unfold skip; simp [hr1]
              rw [hsk]; unfold sp
              rw [swapIdx_other (fin_ne_of_val (by dsimp; omega)) (fin_ne_of_val (by dsimp; omega))]
              rw [skip_val_ge (by omega)]
        have hsubM : pfaffian m (fun r c => A (swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And (sp j) r))
                                              (swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And (sp j) c))) =
                     pfaffian m (fun r c => A (skip0And j r) (skip0And j c)) :=
          pfaffian_congr (fun r c => by rw [hsub r, hsub c])
        rw [hsubM, hsp, hjp]
        simp only [altSign_succ, Int.neg_mul]
      · by_cases hjp1 : j.val = p + 1
        · have hsp : sp j = ⟨p, by omega⟩ := by
            apply Fin.ext; unfold sp swapIdx; simp [Fin.ext_iff, hjp1]
          have hsub : ∀ r : Fin (2 * m),
              swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And (sp j) r) = skip0And j r := by
            intro r; unfold skip0And; rw [hsucc]; congr 1
            rw [hsp]; apply Fin.ext
            by_cases hr : r.val < p
            · have hsk : skip ⟨p, by omega⟩ r = ⟨r.val, by omega⟩ := by unfold skip; simp [hr]
              rw [hsk]; unfold sp
              rw [swapIdx_other (fin_ne_of_val (by dsimp; omega)) (fin_ne_of_val (by dsimp; omega))]
              rw [skip_val_lt (by omega)]
            · by_cases hr0 : r.val = p
              · have hsk : skip ⟨p, by omega⟩ r = ⟨p + 1, by omega⟩ := by
                  unfold skip; apply Fin.ext; simp [hr0]
                rw [hsk]; unfold sp; rw [swapIdx_right, skip_val_lt (by omega)]; dsimp; omega
              · have hsk : skip ⟨p, by omega⟩ r = ⟨r.val + 1, by omega⟩ := by unfold skip; simp [hr]
                rw [hsk]; unfold sp
                rw [swapIdx_other (fin_ne_of_val (by dsimp; omega)) (fin_ne_of_val (by dsimp; omega))]
                rw [skip_val_ge (by omega)]
          have hsubM : pfaffian m (fun r c => A (swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And (sp j) r))
                                                (swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And (sp j) c))) =
                       pfaffian m (fun r c => A (skip0And j r) (skip0And j c)) :=
            pfaffian_congr (fun r c => by rw [hsub r, hsub c])
          rw [hsubM, hsp, hjp1]
          simp only [altSign_succ, Int.neg_mul, Int.neg_neg]
        · have hsp : sp j = j := by
            unfold sp; exact swapIdx_other (fin_ne_of_val (by dsimp; omega)) (fin_ne_of_val (by dsimp; omega))
          rw [hsp]
          let q : Nat := if j.val < p then p - 1 else p
          have hq : q + 1 < 2 * m := by dsimp [q]; split <;> omega
          have hsub : ∀ r : Fin (2 * m),
              swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And j r) =
              skip0And j (swapIdx ⟨q, by omega⟩ ⟨q + 1, hq⟩ r) := by
            intro r; unfold skip0And; rw [hsucc]; congr 1
            apply Fin.ext
            by_cases hjp_lt : j.val < p
            · have hqv : q = p - 1 := by simp [q, hjp_lt]
              by_cases hr1 : r.val = q
              · have hrf : r = ⟨q, by omega⟩ := Fin.ext hr1
                rw [hrf, swapIdx_left]
                have h1 : ¬ (q < j.val) := by omega
                have h2 : ¬ (q + 1 < j.val) := by omega
                have hsk : skip j ⟨q, by omega⟩ = ⟨p, by omega⟩ := by
                  unfold skip; apply Fin.ext; simp [h1]; omega
                rw [hsk]; unfold sp; rw [swapIdx_left, skip_val_ge h2]; dsimp; omega
              · by_cases hr2 : r.val = q + 1
                · have hrf : r = ⟨q + 1, hq⟩ := Fin.ext hr2
                  rw [hrf, swapIdx_right]
                  have h1 : ¬ (q < j.val) := by omega
                  have h2 : ¬ (q + 1 < j.val) := by omega
                  have hsk : skip j ⟨q + 1, hq⟩ = ⟨p + 1, by omega⟩ := by
                    unfold skip; apply Fin.ext; simp [h2]; omega
                  rw [hsk]; unfold sp; rw [swapIdx_right, skip_val_ge h1]; dsimp; omega
                · rw [swapIdx_other (fin_ne_of_val (by dsimp; omega)) (fin_ne_of_val (by dsimp; omega))]
                  unfold sp
                  by_cases hrj : r.val < j.val
                  · rw [swapIdx_other (fin_ne_of_val (by rw [skip_val_lt hrj]; dsimp; omega))
                                      (fin_ne_of_val (by rw [skip_val_lt hrj]; dsimp; omega))]
                  · rw [swapIdx_other (fin_ne_of_val (by rw [skip_val_ge hrj]; dsimp; omega))
                                      (fin_ne_of_val (by rw [skip_val_ge hrj]; dsimp; omega))]
            · have hqv : q = p := by simp [q, hjp_lt]
              by_cases hr1 : r.val = q
              · have hrf : r = ⟨q, by omega⟩ := Fin.ext hr1
                rw [hrf, swapIdx_left]
                have h1 : q < j.val := by omega
                have h2 : q + 1 < j.val := by omega
                have hsk : skip j ⟨q, by omega⟩ = ⟨p, by omega⟩ := by
                  unfold skip; apply Fin.ext; simp [h1]; omega
                rw [hsk]; unfold sp; rw [swapIdx_left, skip_val_lt h2]; dsimp; omega
              · by_cases hr2 : r.val = q + 1
                · have hrf : r = ⟨q + 1, hq⟩ := Fin.ext hr2
                  rw [hrf, swapIdx_right]
                  have h1 : q < j.val := by omega
                  have h2 : q + 1 < j.val := by omega
                  have hsk : skip j ⟨q + 1, hq⟩ = ⟨p + 1, by omega⟩ := by
                    unfold skip; apply Fin.ext; simp [h2]; omega
                  rw [hsk]; unfold sp; rw [swapIdx_right, skip_val_lt h1]; dsimp; omega
                · rw [swapIdx_other (fin_ne_of_val (by dsimp; omega)) (fin_ne_of_val (by dsimp; omega))]
                  unfold sp
                  by_cases hrj : r.val < j.val
                  · rw [swapIdx_other (fin_ne_of_val (by rw [skip_val_lt hrj]; dsimp; omega))
                                      (fin_ne_of_val (by rw [skip_val_lt hrj]; dsimp; omega))]
                  · rw [swapIdx_other (fin_ne_of_val (by rw [skip_val_ge hrj]; dsimp; omega))
                                      (fin_ne_of_val (by rw [skip_val_ge hrj]; dsimp; omega))]
          have hsubM : pfaffian m (fun r c => A (swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And j r))
                                                (swapIdx ⟨p + 1, by omega⟩ ⟨p + 2, hk⟩ (skip0And j c))) =
                       pfaffian m (swapRC ⟨q, by omega⟩ ⟨q + 1, hq⟩ (fun r c => A (skip0And j r) (skip0And j c))) :=
            pfaffian_congr (fun r c => by unfold swapRC; rw [hsub r, hsub c])
          have hsubSkew : IsSkew (fun r c : Fin (2 * m) => A (skip0And j r) (skip0And j c)) :=
            ⟨fun r => hA.1 _, fun r c => hA.2 _ _⟩
          rw [hsubM, ih q hq hsubSkew, Int.mul_neg]

theorem pfaffian_swapRC {m : Nat} (a b : Fin (2 * m)) (hab : a ≠ b)
    {A : Mat (2 * m)} (hA : IsSkew A) :
    pfaffian m (swapRC a b A) = -pfaffian m A := by
  suffices ∀ d (a b : Fin (2 * m)), a.val < b.val → b.val - a.val = d →
      ∀ (A : Mat (2 * m)), IsSkew A → pfaffian m (swapRC a b A) = -pfaffian m A by
    by_cases hlt : a.val < b.val
    · exact this (b.val - a.val) a b hlt rfl A hA
    · have hgt : b.val < a.val := by
        have : a.val ≠ b.val := fun heq => hab (Fin.ext heq); omega
      have hcomm : swapRC a b A = swapRC b a A := by
        funext i j; unfold swapRC; rw [swapIdx_comm a b i, swapIdx_comm a b j]
      rw [hcomm]
      exact this (a.val - b.val) b a hgt rfl A hA
  intro d
  induction d with
  | zero => intro a' b' hlt hdiff; omega
  | succ d ih =>
    intro a' b' hlt hdiff A' hA'
    cases d with
    | zero =>
      have ha_lt : a'.val + 1 < 2 * m := by omega
      have hb : b' = ⟨a'.val + 1, ha_lt⟩ := Fin.ext (by dsimp; omega)
      have h := pfaffian_swapAdj a'.val ha_lt hA'
      have ha1 : (⟨a'.val, by omega⟩ : Fin (2 * m)) = a' := Fin.ext rfl
      rw [ha1, ← hb] at h
      exact h
    | succ d' =>
      let c : Fin (2 * m) := ⟨b'.val - 1, by omega⟩
      have hdecomp : swapRC a' b' A' = swapRC c b' (swapRC a' c (swapRC c b' A')) := by
        funext i j; unfold swapRC
        have hac : a' ≠ c := fin_ne_of_val (by dsimp [c]; omega)
        have hab' : a' ≠ b' := fin_ne_of_val (by omega)
        have hcb : c ≠ b' := fin_ne_of_val (by dsimp [c]; omega)
        have hd : ∀ x : Fin (2 * m), swapIdx a' b' x = swapIdx c b' (swapIdx a' c (swapIdx c b' x)) := by
          intro x
          by_cases h1 : x = a'
          · rw [h1, swapIdx_left, swapIdx_other hac hab', swapIdx_left, swapIdx_left]
          · by_cases h2 : x = b'
            · rw [h2, swapIdx_right, swapIdx_right, swapIdx_right, swapIdx_other hac hab']
            · by_cases h3 : x = c
              · rw [h3, swapIdx_other (Ne.symm hac) hcb, swapIdx_left, swapIdx_other (Ne.symm hab') (Ne.symm hcb), swapIdx_right]
              · rw [swapIdx_other h1 h2, swapIdx_other h3 h2, swapIdx_other h1 h3, swapIdx_other h3 h2]
        rw [hd i, hd j]
      rw [hdecomp]
      have hA1 : IsSkew (swapRC c b' A') := isSkew_swapRC c b' hA'
      have hA2 : IsSkew (swapRC a' c (swapRC c b' A')) := isSkew_swapRC a' c hA1
      have hc1 : (⟨c.val, by omega⟩ : Fin (2 * m)) = c := Fin.ext rfl
      have hb1 : (⟨c.val + 1, by dsimp [c]; omega⟩ : Fin (2 * m)) = b' := Fin.ext (by dsimp [c]; omega)
      have hstep1 := pfaffian_swapAdj c.val (by dsimp [c]; omega) hA2
      rw [hc1, hb1] at hstep1
      rw [hstep1]
      rw [ih a' c (by dsimp [c]; omega) (by dsimp [c]; omega) (swapRC c b' A') hA1]
      have hstep3 := pfaffian_swapAdj c.val (by dsimp [c]; omega) hA'
      rw [hc1, hb1] at hstep3
      rw [hstep3]
      omega

-- 3.4 Elementary shear `shearRC 0 1 c` and arbitrary `shearRC a b c`!
theorem pfaffian_shear01 {m : Nat} (c : Int) {A : Mat (2 * (m + 1))} (hA : IsSkew A) :
    pfaffian (m + 1) (shearRC ⟨0, by omega⟩ ⟨1, by omega⟩ c A) = pfaffian (m + 1) A := by
  cases m with
  | zero =>
    change altSign 0 * shearRC ⟨0, by omega⟩ ⟨1, by omega⟩ c A ⟨0, by omega⟩ ⟨1, by omega⟩ * 1 + 0 =
           altSign 0 * A ⟨0, by omega⟩ ⟨1, by omega⟩ * 1 + 0
    unfold shearRC
    have h01 : (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, by omega⟩ := fin_ne_of_val (by decide)
    simp [hA.1]
  | succ m' =>
    rw [pfaffian_expand2, pfaffian_expand2]
    have h01 : (⟨0, by omega⟩ : Fin (2 * (m' + 2))) ≠ ⟨1, by omega⟩ := fin_ne_of_val (by simp)
    have hne0 : ∀ x : Fin (2 * (m' + 1)), x.succ.succ ≠ ⟨0, by omega⟩ :=
      fun x => fin_ne_of_val (by simp [Fin.succ])
    have h1 : shearRC ⟨0, by omega⟩ ⟨1, by omega⟩ c A ⟨0, by omega⟩ ⟨1, by omega⟩ =
              A ⟨0, by omega⟩ ⟨1, by omega⟩ := by
      unfold shearRC; simp only [Ne.symm h01, ↓reduceIte, hA.1, Int.mul_zero, Int.add_zero, and_false]
    have hsub1 : (fun (r c' : Fin (2 * (m' + 1))) =>
                    shearRC ⟨0, by omega⟩ ⟨1, by omega⟩ c A r.succ.succ c'.succ.succ) =
                 (fun (r c' : Fin (2 * (m' + 1))) => A r.succ.succ c'.succ.succ) := by
      funext r c'; unfold shearRC; simp only [hne0, ↓reduceIte, Int.add_zero, false_and]
    rw [h1, hsub1]
    congr 1
    have hsimp :
        sumFin (fun a : Fin (2 * m' + 2) =>
          sumFin (fun b : Fin (2 * m' + 1) =>
            altSign a.val * altSign b.val *
            shearRC ⟨0, by omega⟩ ⟨1, by omega⟩ c A ⟨0, by omega⟩ a.succ.succ *
            shearRC ⟨0, by omega⟩ ⟨1, by omega⟩ c A ⟨1, by omega⟩ (skip a b).succ.succ *
            pfaffian m' (fun r c' => shearRC ⟨0, by omega⟩ ⟨1, by omega⟩ c A
                                       (skip01Pair a b r) (skip01Pair a b c')))) =
        sumFin (fun a : Fin (2 * m' + 2) =>
          sumFin (fun b : Fin (2 * m' + 1) =>
            altSign a.val * altSign b.val *
            A ⟨0, by omega⟩ a.succ.succ *
            A ⟨1, by omega⟩ (skip a b).succ.succ *
            pfaffian m' (fun r c' => A (skip01Pair a b r) (skip01Pair a b c')))) +
        c * sumFin (fun a : Fin (2 * m' + 2) =>
          sumFin (fun b : Fin (2 * m' + 1) =>
            altSign a.val * altSign b.val *
            A ⟨1, by omega⟩ a.succ.succ *
            A ⟨1, by omega⟩ (skip a b).succ.succ *
            pfaffian m' (fun r c' => A (skip01Pair a b r) (skip01Pair a b c')))) := by
      rw [← sumFin_mul_left, ← sumFin_add]
      apply sumFin_congr; intro a
      rw [← sumFin_mul_left, ← sumFin_add]
      apply sumFin_congr; intro b
      have hsub2 : (fun (r c' : Fin (2 * m')) =>
                      shearRC ⟨0, by omega⟩ ⟨1, by omega⟩ c A
                        (skip01Pair a b r) (skip01Pair a b c')) =
                   (fun (r c' : Fin (2 * m')) => A (skip01Pair a b r) (skip01Pair a b c')) := by
        funext r c'; unfold shearRC skip01Pair; simp only [hne0, ↓reduceIte, Int.add_zero, false_and]
      rw [hsub2]
      unfold shearRC
      simp only [hne0, Ne.symm h01, ↓reduceIte, Int.add_zero, and_false]
      have hd : ∀ (s x y z p : Int), s * (x + c * y) * z * p = s * x * z * p + c * (s * y * z * p) := by
        intro s x y z p
        rw [Int.mul_add, Int.add_mul, Int.add_mul]
        congr 1; ac_rfl
      exact hd _ _ _ _ _
    rw [hsimp]
    let g : Fin (2 * m' + 2) → Fin (2 * m' + 2) → (Fin (2 * m') → Fin (2 * m' + 4)) → Int :=
      fun u v f => A ⟨1, by omega⟩ u.succ.succ * A ⟨1, by omega⟩ v.succ.succ *
                   pfaffian m' (fun r c' => A (f r) (f c'))
    have hanti := sumFin_double_swap_pair g (fun a b h => by
      dsimp only [g]; rw [skip01Pair_comm a b h])
    have hsym : ∀ (a : Fin (2 * m' + 2)) (b : Fin (2 * m' + 1)),
        g (skip a b) a (skip01Pair a b) = g a (skip a b) (skip01Pair a b) := by
      intro a b; dsimp only [g]
      rw [Int.mul_comm (A ⟨1, by omega⟩ (skip a b).succ.succ) (A ⟨1, by omega⟩ a.succ.succ)]
    have hzero : sumFin (fun a : Fin (2 * m' + 2) =>
        sumFin (fun b : Fin (2 * m' + 1) =>
          altSign a.val * altSign b.val *
          A ⟨1, by omega⟩ a.succ.succ *
          A ⟨1, by omega⟩ (skip a b).succ.succ *
          pfaffian m' (fun r c' => A (skip01Pair a b r) (skip01Pair a b c')))) = 0 := by
      have heq1 : sumFin (fun a : Fin (2 * m' + 2) =>
          sumFin (fun b : Fin (2 * m' + 1) =>
            altSign a.val * altSign b.val *
            A ⟨1, by omega⟩ a.succ.succ *
            A ⟨1, by omega⟩ (skip a b).succ.succ *
            pfaffian m' (fun r c' => A (skip01Pair a b r) (skip01Pair a b c')))) =
          sumFin (fun a : Fin (2 * m' + 2) =>
            sumFin (fun b : Fin (2 * m' + 1) =>
              altSign a.val * altSign b.val * g a (skip a b) (skip01Pair a b))) := by
        apply sumFin_congr; intro a; apply sumFin_congr; intro b
        dsimp only [g]; simp only [Int.mul_assoc]
      rw [heq1]
      have hswap_eq : sumFin (fun a : Fin (2 * m' + 2) =>
          sumFin (fun b : Fin (2 * m' + 1) =>
            altSign a.val * altSign b.val * g (skip a b) a (skip01Pair a b))) =
          sumFin (fun a : Fin (2 * m' + 2) =>
            sumFin (fun b : Fin (2 * m' + 1) =>
              altSign a.val * altSign b.val * g a (skip a b) (skip01Pair a b))) := by
        apply sumFin_congr; intro a; apply sumFin_congr; intro b
        exact congrArg (altSign a.val * altSign b.val * ·) (hsym a b)
      rw [hswap_eq] at hanti
      omega
    rw [hzero, Int.mul_zero, Int.add_zero]

theorem pfaffian_shearRC {m : Nat} (a b : Fin (2 * m)) (hab : a ≠ b) (c : Int)
    {A : Mat (2 * m)} (hA : IsSkew A) :
    pfaffian m (shearRC a b c A) = pfaffian m A := by
  cases m with
  | zero => exact Fin.elim0 a
  | succ m' =>
    let i0 : Fin (2 * (m' + 1)) := ⟨0, by omega⟩
    let i1 : Fin (2 * (m' + 1)) := ⟨1, by omega⟩
    have hconj_swap : ∀ (u v x y : Fin (2 * (m' + 1))) (M : Mat (2 * (m' + 1))),
        swapRC u v (shearRC x y c M) = shearRC (swapIdx u v x) (swapIdx u v y) c (swapRC u v M) := by
      intro u v x y M; funext r s; unfold swapRC shearRC
      have hiff : ∀ z w : Fin (2 * (m' + 1)), (swapIdx u v z = w) ↔ (z = swapIdx u v w) := by
        intro z w; constructor
        · intro h; rw [← h, swapIdx_invol]
        · intro h; rw [h, swapIdx_invol]
      simp only [hiff, swapIdx_invol]
    have hstep : ∀ (b' : Fin (2 * (m' + 1))), i0 ≠ b' →
        ∀ (M : Mat (2 * (m' + 1))), IsSkew M →
        pfaffian (m' + 1) (shearRC i0 b' c M) = pfaffian (m' + 1) M := by
      intro b' hb' M hM
      by_cases hb1 : b' = i1
      · rw [hb1]; exact pfaffian_shear01 c hM
      · have h1 := pfaffian_swapRC i1 b' (Ne.symm hb1) (isSkew_shearRC i0 b' c hM)
        rw [hconj_swap] at h1
        have hsi0 : swapIdx i1 b' i0 = i0 :=
          swapIdx_other (fin_ne_of_val (by dsimp [i0, i1]; omega)) hb'
        have hsb' : swapIdx i1 b' b' = i1 := swapIdx_right i1 b'
        rw [hsi0, hsb', pfaffian_shear01 c (isSkew_swapRC i1 b' hM),
            pfaffian_swapRC i1 b' (Ne.symm hb1) hM] at h1
        omega
    by_cases ha0 : a = i0
    · rw [ha0]; exact hstep b (by rw [← ha0]; exact hab) A hA
    · have h1 := pfaffian_swapRC i0 a (Ne.symm ha0) (isSkew_shearRC a b c hA)
      rw [hconj_swap] at h1
      have hsa : swapIdx i0 a a = i0 := swapIdx_right i0 a
      have hsb_ne : i0 ≠ swapIdx i0 a b := by
        intro h; have := congrArg (swapIdx i0 a) h
        rw [swapIdx_left, swapIdx_invol] at this; exact hab this
      rw [hsa, hstep (swapIdx i0 a b) hsb_ne (swapRC i0 a A) (isSkew_swapRC i0 a hA),
          pfaffian_swapRC i0 a (Ne.symm ha0) hA] at h1
      omega

theorem pfaffian_zero_row0 {m : Nat} {A : Mat (2 * (m + 1))}
    (h0 : ∀ j, A ⟨0, by omega⟩ j = 0) : pfaffian (m + 1) A = 0 := by
  change sumFin (fun j : Fin (2 * m + 1) => _) = 0
  exact sumFin_eq_zero (fun j => by rw [h0 j.succ]; simp)

theorem pfaffian_zero_row {m : Nat} (a : Fin (2 * m)) {A : Mat (2 * m)}
    (hA : IsSkew A) (ha : ∀ j, A a j = 0) : pfaffian m A = 0 := by
  cases m with
  | zero => exact Fin.elim0 a
  | succ m' =>
    let i0 : Fin (2 * (m' + 1)) := ⟨0, by omega⟩
    by_cases h : a = i0
    · rw [h] at ha; exact pfaffian_zero_row0 ha
    · have h1 := pfaffian_swapRC i0 a (Ne.symm h) hA
      have h2 : pfaffian (m' + 1) (swapRC i0 a A) = 0 := by
        apply pfaffian_zero_row0
        intro j; unfold swapRC; rw [swapIdx_left]; exact ha _
      rw [h2] at h1; omega

-- 3.5 Block direct sum, global scaling, and diagonal congruence for `pfaffian`
def blockDiag {p q : Nat} (A : Mat p) (B : Mat q) : Mat (p + q) :=
  fun i j =>
    if hi : i.val < p then
      if hj : j.val < p then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else
      if hj : j.val < p then 0 else B ⟨i.val - p, by omega⟩ ⟨j.val - p, by omega⟩

theorem pfaffian_blockDiag {m n : Nat} (A : Mat (2 * m)) (B : Mat (2 * n)) :
    pfaffian (m + n) (castMat (by omega) (blockDiag A B)) = pfaffian m A * pfaffian n B := by
  induction m with
  | zero =>
    simp only [pfaffian, Int.one_mul]
    have h0 : 0 + n = n := Nat.zero_add n
    rw [← pfaffian_castMat h0.symm]
    exact pfaffian_congr (fun i j => by unfold castMat blockDiag; simp)
  | succ m ih =>
    have hmn : m + 1 + n = (m + n) + 1 := by omega
    rw [← pfaffian_castMat hmn]
    let M : Mat (2 * ((m + n) + 1)) :=
      castMat (show 2 * (m + 1 + n) = 2 * ((m + n) + 1) by omega)
        (castMat (show 2 * (m + 1) + 2 * n = 2 * (m + 1 + n) by omega) (blockDiag A B))
    change sumFin (fun j : Fin (2 * (m + n) + 1) =>
      altSign j.val * M ⟨0, by omega⟩ j.succ *
      pfaffian (m + n) (fun r c => M (skip0And j r) (skip0And j c))) =
      sumFin (fun j : Fin (2 * m + 1) =>
        altSign j.val * A ⟨0, by omega⟩ j.succ *
        pfaffian m (fun r c => A (skip0And j r) (skip0And j c))) * pfaffian n B
    rw [← sumFin_mul_right]
    rw [← sumFin_cast (show (2 * m + 1) + 2 * n = 2 * (m + n) + 1 by omega)]
    rw [sumFin_split]
    have hzero2 : sumFin (fun j : Fin (2 * n) =>
        altSign ((2 * m + 1) + j.val) *
        M ⟨0, by omega⟩ (⟨(2 * m + 1) + j.val, by omega⟩ : Fin (2 * (m + n) + 1)).succ *
        pfaffian (m + n) (fun r c =>
          M (skip0And (⟨(2 * m + 1) + j.val, by omega⟩ : Fin (2 * (m + n) + 1)) r)
            (skip0And (⟨(2 * m + 1) + j.val, by omega⟩ : Fin (2 * (m + n) + 1)) c))) = 0 := by
      apply sumFin_eq_zero; intro j
      dsimp only [M]; unfold castMat blockDiag
      have h0 : 0 < 2 * (m + 1) := by omega
      have hj : ¬ ((2 * m + 1) + j.val + 1 < 2 * (m + 1)) := by omega
      simp [Fin.succ, h0, hj]
    rw [hzero2, Int.add_zero]
    apply sumFin_congr; intro j
    have h0j : M ⟨0, by omega⟩ (⟨j.val, by omega⟩ : Fin (2 * (m + n) + 1)).succ =
               A ⟨0, by omega⟩ j.succ := by
      dsimp only [M]; unfold castMat blockDiag
      have h0 : 0 < 2 * (m + 1) := by omega
      have hj : j.val + 1 < 2 * (m + 1) := by omega
      simp [Fin.succ, h0, hj]
    rw [h0j]
    have hsub : (fun r c : Fin (2 * (m + n)) =>
        M (skip0And (⟨j.val, by omega⟩ : Fin (2 * (m + n) + 1)) r)
          (skip0And (⟨j.val, by omega⟩ : Fin (2 * (m + n) + 1)) c)) =
        castMat (by omega) (blockDiag (fun r c : Fin (2 * m) => A (skip0And j r) (skip0And j c)) B) := by
      funext r c
      dsimp only [M]; unfold castMat blockDiag skip0And skip
      by_cases hr : r.val < 2 * m <;> by_cases hc : c.val < 2 * m
      · by_cases h1 : r.val < j.val <;> by_cases h2 : c.val < j.val
        · have hr1 : r.val + 1 < 2 * (m + 1) := by omega
          have hc1 : c.val + 1 < 2 * (m + 1) := by omega
          simp [Fin.succ, hr, hc, h1, h2, hr1, hc1]
        · have hr1 : r.val + 1 < 2 * (m + 1) := by omega
          have hc1 : c.val + 1 + 1 < 2 * (m + 1) := by omega
          simp [Fin.succ, hr, hc, h1, h2, hr1, hc1]
        · have hr1 : r.val + 1 + 1 < 2 * (m + 1) := by omega
          have hc1 : c.val + 1 < 2 * (m + 1) := by omega
          simp [Fin.succ, hr, hc, h1, h2, hr1, hc1]
        · have hr1 : r.val + 1 + 1 < 2 * (m + 1) := by omega
          have hc1 : c.val + 1 + 1 < 2 * (m + 1) := by omega
          simp [Fin.succ, hr, hc, h1, h2, hr1, hc1]
      · have hc0 : ¬ (c.val < j.val) := by omega
        have hc1 : ¬ (c.val + 1 + 1 < 2 * (m + 1)) := by omega
        by_cases h1 : r.val < j.val
        · have hr1 : r.val + 1 < 2 * (m + 1) := by omega
          simp [Fin.succ, hr, hc, h1, hc0, hr1, hc1]
        · have hr1 : r.val + 1 + 1 < 2 * (m + 1) := by omega
          simp [Fin.succ, hr, hc, h1, hc0, hr1, hc1]
      · have hr0 : ¬ (r.val < j.val) := by omega
        have hr1 : ¬ (r.val + 1 + 1 < 2 * (m + 1)) := by omega
        by_cases h2 : c.val < j.val
        · have hc1 : c.val + 1 < 2 * (m + 1) := by omega
          simp [Fin.succ, hr, hc, hr0, h2, hr1, hc1]
        · have hc1 : c.val + 1 + 1 < 2 * (m + 1) := by omega
          simp [Fin.succ, hr, hc, hr0, h2, hr1, hc1]
      · have hr0 : ¬ (r.val < j.val) := by omega
        have hc0 : ¬ (c.val < j.val) := by omega
        have hr1 : ¬ (r.val + 1 + 1 < 2 * (m + 1)) := by omega
        have hc1 : ¬ (c.val + 1 + 1 < 2 * (m + 1)) := by omega
        simp only [Fin.succ, hr, hc, hr0, hc0, hr1, hc1, ↓reduceDIte]
        congr 1 <;> (apply Fin.ext; dsimp; omega)
    rw [hsub, ih]
    ac_rfl

def scaleMat {n : Nat} (c : Int) (A : Mat n) : Mat n :=
  fun i j => c * A i j

theorem pfaffian_scaleMat {m : Nat} (c : Int) (A : Mat (2 * m)) :
    pfaffian m (scaleMat c A) = c ^ m * pfaffian m A := by
  induction m with
  | zero => simp [pfaffian]
  | succ m ih =>
    change sumFin (fun j : Fin (2 * m + 1) =>
      altSign j.val * (c * A ⟨0, by omega⟩ j.succ) *
      pfaffian m (scaleMat c (fun r c' => A (skip0And j r) (skip0And j c')))) = _
    simp only [ih]
    change _ = c ^ (m + 1) * sumFin (fun j : Fin (2 * m + 1) => _)
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro j
    rw [Int.pow_succ]
    ac_rfl

def diagCong {n : Nat} (d : Fin n → Int) (A : Mat n) : Mat n :=
  fun i j => d i * A i j * d j

theorem pfaffian_diagCong {m : Nat} (d : Fin (2 * m) → Int) (A : Mat (2 * m)) :
    pfaffian m (diagCong d A) = prodFin d * pfaffian m A := by
  suffices ∀ (k : Nat) (hk : k ≤ 2 * m),
      pfaffian m (fun i j => (if i.val < k then d i else 1) * A i j * (if j.val < k then d j else 1)) =
      prodFin (fun i : Fin k => d ⟨i.val, by omega⟩) * pfaffian m A by
    have h := this (2 * m) (Nat.le_refl _)
    have hL : (fun i j : Fin (2 * m) =>
        (if i.val < 2 * m then d i else 1) * A i j * (if j.val < 2 * m then d j else 1)) =
        diagCong d A := by
      funext i j; unfold diagCong; simp [i.isLt, j.isLt]
    have hR : prodFin (fun i : Fin (2 * m) => d ⟨i.val, by omega⟩) = prodFin d :=
      prodFin_congr (fun _ => rfl)
    rw [hL, hR] at h
    exact h
  intro k
  induction k with
  | zero =>
    intro _; simp only [prodFin_zero, Int.one_mul]
    exact pfaffian_congr (fun _ _ => by simp)
  | succ k ih =>
    intro hk
    let ak : Fin (2 * m) := ⟨k, by omega⟩
    let Mprev : Mat (2 * m) := fun i j =>
      (if i.val < k then d i else 1) * A i j * (if j.val < k then d j else 1)
    have heq : (fun i j : Fin (2 * m) =>
        (if i.val < k + 1 then d i else 1) * A i j * (if j.val < k + 1 then d j else 1)) =
        scaleRC ak (d ak) Mprev := by
      funext i j; unfold scaleRC Mprev
      have hfactor : ∀ x : Fin (2 * m),
          (if x.val < k + 1 then d x else 1) =
          (if x = ak then d ak else 1) * (if x.val < k then d x else 1) := by
        intro x
        by_cases hlt : x.val < k
        · have hlt1 : x.val < k + 1 := by omega
          have hne : x ≠ ak := fin_ne_of_val (by dsimp [ak]; omega)
          simp [hlt, hlt1, hne]
        · by_cases heq : x.val = k
          · have hxf : x = ak := Fin.ext heq
            rw [hxf]; simp [ak]
          · have hlt1 : ¬ (x.val < k + 1) := by omega
            have hne : x ≠ ak := fin_ne_of_val (by dsimp [ak]; omega)
            simp [hlt, hlt1, hne]
      rw [hfactor i, hfactor j]
      ac_rfl
    rw [heq, pfaffian_scaleRC, ih (by omega)]
    have hprod : prodFin (fun i : Fin (k + 1) => d ⟨i.val, by omega⟩) =
                 prodFin (fun i : Fin k => d ⟨i.val, by omega⟩) * d ak := by
      have hsp := prodFin_split (p := k) (q := 1) (fun i : Fin (k + 1) => d ⟨i.val, by omega⟩)
      rw [hsp]
      congr 1
      change d ⟨k + 0, by omega⟩ * 1 = d ak
      simp [ak]
    rw [hprod]
    ac_rfl

-- ============================================================================
-- Section 4: Reusable Infinite Proof Mechanisms
--   Mechanism 1: Integral Block-Schur Elimination (Top-Left & Bottom-Right)
--   Mechanism 2: Zero-Corner Upper-Triangular Congruence Law
--   Mechanism 3: Order-Reversal, Self-Congruence & Skew-Conference Reflection
-- ============================================================================

theorem int_add_congr {a b c d : Int} (h1 : a = c) (h2 : b = d) : a + b = c + d := by
  rw [h1, h2]

def blockMat {p q : Nat}
    (A00 : Mat p) (A01 : Fin p → Fin q → Int)
    (A10 : Fin q → Fin p → Int) (A11 : Mat q) : Mat (p + q) :=
  fun i j =>
    if hi : i.val < p then
      if hj : j.val < p then A00 ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else A01 ⟨i.val, hi⟩ ⟨j.val - p, by omega⟩
    else
      if hj : j.val < p then A10 ⟨i.val - p, by omega⟩ ⟨j.val, hj⟩
      else A11 ⟨i.val - p, by omega⟩ ⟨j.val - p, by omega⟩

def blockUpperId {p q : Nat} (X : Fin p → Fin q → Int) : Mat (p + q) :=
  fun i j =>
    (if i = j then 1 else 0) +
    if hi : i.val < p then
      if hj : j.val < p then 0 else X ⟨i.val, hi⟩ ⟨j.val - p, by omega⟩
    else 0

def blockLowerId {p q : Nat} (Y : Fin q → Fin p → Int) : Mat (p + q) :=
  fun i j =>
    (if i = j then 1 else 0) +
    if hi : i.val < p then 0
    else if hj : j.val < p then Y ⟨i.val - p, by omega⟩ ⟨j.val, hj⟩ else 0

theorem pfaffian_elemShear_congruence {m : Nat} (a b : Fin (2 * m)) (hab : a ≠ b) (c : Int)
    {A : Mat (2 * m)} (hA : IsSkew A) :
    pfaffian m (congruence (elemShear a b c) A) = pfaffian m A := by
  rw [congruence_elemShear]
  exact pfaffian_shearRC a b hab c hA

theorem pfaffian_elemSwap_congruence {m : Nat} (a b : Fin (2 * m)) (hab : a ≠ b)
    {A : Mat (2 * m)} (hA : IsSkew A) :
    pfaffian m (congruence (elemSwap a b) A) = -pfaffian m A := by
  rw [congruence_elemSwap]
  exact pfaffian_swapRC a b hab hA

theorem pfaffian_elemScale_congruence {m : Nat} (a : Fin (2 * m)) (c : Int) (A : Mat (2 * m)) :
    pfaffian m (congruence (elemScale a c) A) = c * pfaffian m A := by
  rw [congruence_elemScale]
  exact pfaffian_scaleRC a c A

theorem matMul_elemShear_right {n : Nat} (P : Mat n) (a b : Fin n) (c : Int) (i j : Fin n) :
    matMul P (elemShear a b c) i j = P i j + (if j = a then c * P i b else 0) := by
  unfold matMul elemShear
  have hsp : ∀ k : Fin n,
      P i k * ((if k = j then 1 else 0) + (if k = b ∧ j = a then c else 0)) =
      P i k * (if k = j then 1 else 0) + P i k * (if k = b ∧ j = a then c else 0) :=
    fun k => Int.mul_add _ _ _
  rw [sumFin_congr hsp, sumFin_add]
  rw [sumFin_single j _ (fun k hk => by simp [hk])]
  rw [sumFin_single b _ (fun k hk => by simp [hk])]
  by_cases hja : j = a <;> simp [hja, Int.mul_comm]

theorem pfaffian_blockLowerId {p q r : Nat} (hpq : p + q = 2 * r)
    (Y : Fin q → Fin p → Int) {A : Mat (2 * r)} (hA : IsSkew A) :
    pfaffian r (congruence (castMat hpq (blockLowerId Y)) A) = pfaffian r A := by
  by_cases hq0 : q = 0
  · have hid : castMat hpq (blockLowerId Y) = matId (2 * r) := by
      funext i j; unfold castMat blockLowerId matId
      have : i.val < p := by omega
      simp [this, Fin.ext_iff]
    rw [hid, congruence_id]
  · let pref (k : Nat) : Mat (2 * r) := fun i j =>
      (if i = j then 1 else 0) +
      if hi : i.val < p then 0
      else if hj : j.val < p then
        if j.val * q + (i.val - p) < k then Y ⟨i.val - p, by omega⟩ ⟨j.val, hj⟩ else 0
      else 0
    have hstep : ∀ k, k ≤ p * q → pfaffian r (congruence (pref k) A) = pfaffian r A := by
      intro k
      induction k with
      | zero =>
        intro _
        have h0 : pref 0 = matId (2 * r) := by
          funext i j; dsimp only [pref]; unfold matId
          by_cases hi : i.val < p <;> by_cases hj : j.val < p <;> simp [hi, hj]
        rw [h0, congruence_id]
      | succ k ih =>
        intro hk
        have hq_pos : 0 < q := by omega
        let ii : Nat := k / q
        let jj : Nat := k % q
        have hjj : jj < q := Nat.mod_lt k hq_pos
        have hii : ii < p := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
        have hdecomp : ii * q + jj = k := by
          dsimp [ii, jj]; have := Nat.div_add_mod k q; rw [Nat.mul_comm] at this; exact this
        let a : Fin (2 * r) := ⟨ii, by omega⟩
        let b : Fin (2 * r) := ⟨p + jj, by omega⟩
        have hab : a ≠ b := fin_ne_of_val (by dsimp [a, b]; omega)
        have hmul : pref (k + 1) = matMul (pref k) (elemShear a b (Y ⟨jj, hjj⟩ ⟨ii, hii⟩)) := by
          funext row col
          rw [matMul_elemShear_right]
          have hcolb : pref k row b = if row = b then 1 else 0 := by
            dsimp only [pref, b]
            have hnb : ¬ (p + jj < p) := by omega
            by_cases hr : row.val < p <;> simp [hr, hnb]
          rw [hcolb]
          dsimp only [pref, a, b]
          by_cases hr : row.val < p <;> by_cases hc : col.val < p
          · have hne : row ≠ ⟨p + jj, by omega⟩ := fin_ne_of_val (by dsimp; omega)
            simp [hr, hne]
          · have hne : row ≠ ⟨p + jj, by omega⟩ := fin_ne_of_val (by dsimp; omega)
            simp [hr, hne]
          · by_cases hca : col = ⟨ii, by omega⟩
            · have hcv : col.val = ii := congrArg Fin.val hca
              by_cases hrb : row = ⟨p + jj, by omega⟩
              · have hrv : row.val = p + jj := congrArg Fin.val hrb
                have hrsub : row.val - p = jj := by omega
                have hidx : col.val * q + (row.val - p) = k := by rw [hcv, hrsub, hdecomp]
                have hlt1 : col.val * q + (row.val - p) < k + 1 := by omega
                have hlt0 : ¬ (col.val * q + (row.val - p) < k) := by omega
                have hY : Y ⟨row.val - p, by omega⟩ ⟨col.val, hc⟩ = Y ⟨jj, hjj⟩ ⟨ii, hii⟩ := by
                  congr 1 <;> (apply Fin.ext; dsimp; omega)
                simp only [hr, hc, ↓reduceDIte, hlt1, hlt0, ↓reduceIte, hY]
                simp only [hca, hrb, ↓reduceIte, Int.mul_one, Int.add_zero]
              · have hrv : row.val ≠ p + jj := fun h => hrb (Fin.ext h)
                have hneq : col.val * q + (row.val - p) ≠ k := by rw [hcv]; omega
                have hiff : (col.val * q + (row.val - p) < k + 1) ↔ (col.val * q + (row.val - p) < k) := by omega
                simp only [hr, hc, ↓reduceDIte, hiff]
                simp only [hca, hrb, ↓reduceIte, Int.mul_zero, Int.add_zero]
            · have hcv : col.val ≠ ii := fun h => hca (Fin.ext h)
              have hneq : col.val * q + (row.val - p) ≠ k := by
                intro heq
                have h1 : col.val * q + (row.val - p) = ii * q + jj := by omega
                by_cases hlt : col.val < ii
                · have hle : (col.val + 1) * q ≤ ii * q := Nat.mul_le_mul_right q (by omega)
                  rw [Nat.add_mul, Nat.one_mul] at hle; omega
                · have hle : (ii + 1) * q ≤ col.val * q := Nat.mul_le_mul_right q (by omega)
                  rw [Nat.add_mul, Nat.one_mul] at hle; omega
              have hiff : (col.val * q + (row.val - p) < k + 1) ↔ (col.val * q + (row.val - p) < k) := by omega
              simp only [hr, hc, ↓reduceDIte, hiff]
              simp only [hca, ↓reduceIte, Int.add_zero]
          · have hne1 : col ≠ ⟨ii, by omega⟩ := fin_ne_of_val (by dsimp; omega)
            simp [hr, hc, hne1]
        rw [hmul, congruence_comp, pfaffian_elemShear_congruence a b hab _ (isSkew_congruence _ _ hA)]
        exact ih (by omega)
    have hfull : pref (p * q) = castMat hpq (blockLowerId Y) := by
      funext i j; dsimp only [pref]; unfold castMat blockLowerId
      by_cases hi : i.val < p <;> by_cases hj : j.val < p
      · simp [hi, Fin.ext_iff]
      · simp [hi, Fin.ext_iff]
      · have hlt : j.val * q + (i.val - p) < p * q := by
          have hjp : j.val + 1 ≤ p := by omega
          have h1 : j.val * q + q = (j.val + 1) * q := by rw [Nat.add_mul, Nat.one_mul]
          have h2 : (j.val + 1) * q ≤ p * q := Nat.mul_le_mul_right q hjp
          omega
        simp [hi, hj, hlt, Fin.ext_iff]
      · simp [hi, hj, Fin.ext_iff]
    rw [← hfull]
    exact hstep (p * q) (Nat.le_refl _)

-- ----------------------------------------------------------------------------
-- Mechanism 1A: General Integral Block-Schur Elimination (Top-Left Pivot)
-- ----------------------------------------------------------------------------
/-- Move index `k` down to index `0` via `k` adjacent swaps (`0..k-1` shift up by 1). -/
def moveToZeroIdx {n : Nat} (k : Fin n) (i : Fin n) : Fin n :=
  if i.val = 0 then k
  else if h : i.val ≤ k.val then ⟨i.val - 1, by omega⟩
  else i

theorem pfaffian_moveToZero {m : Nat} (k : Fin (2 * m)) {A : Mat (2 * m)} (hA : IsSkew A) :
    pfaffian m (fun i j => A (moveToZeroIdx k i) (moveToZeroIdx k j)) =
    altSign k.val * pfaffian m A := by
  suffices ∀ (t : Nat) (ht : t < 2 * m) (M : Mat (2 * m)), IsSkew M →
      pfaffian m (fun i j => M (moveToZeroIdx ⟨t, ht⟩ i) (moveToZeroIdx ⟨t, ht⟩ j)) =
      altSign t * pfaffian m M from this k.val k.isLt A hA
  intro t
  induction t with
  | zero =>
    intro ht M _
    simp only [altSign_zero, Int.one_mul]
    exact pfaffian_congr (fun i j => by
      have hm : ∀ x : Fin (2 * m), moveToZeroIdx ⟨0, ht⟩ x = x := by
        intro x; unfold moveToZeroIdx; apply Fin.ext
        by_cases h0 : x.val = 0 <;> simp [h0]
      rw [hm i, hm j])
  | succ t ih =>
    intro ht M hM
    -- First swap t and t+1 in M, then apply moveToZeroIdx t!
    let M1 : Mat (2 * m) := swapRC ⟨t, by omega⟩ ⟨t + 1, ht⟩ M
    have hM1 : IsSkew M1 := isSkew_swapRC _ _ hM
    have hcomp : ∀ x : Fin (2 * m),
        swapIdx ⟨t, by omega⟩ ⟨t + 1, ht⟩ (moveToZeroIdx ⟨t, by omega⟩ x) =
        moveToZeroIdx ⟨t + 1, ht⟩ x := by
      intro x; apply Fin.ext; unfold moveToZeroIdx swapIdx
      by_cases h0 : x.val = 0
      · simp [h0]
      · by_cases hle : x.val ≤ t
        · have hle1 : x.val ≤ t + 1 := by omega
          have hne1 : (⟨x.val - 1, by omega⟩ : Fin (2 * m)) ≠ ⟨t, by omega⟩ := fin_ne_of_val (by dsimp; omega)
          have hne2 : (⟨x.val - 1, by omega⟩ : Fin (2 * m)) ≠ ⟨t + 1, ht⟩ := fin_ne_of_val (by dsimp; omega)
          simp [h0, hle, hle1, hne1, hne2]
        · by_cases heq : x.val = t + 1
          · have hle1 : x.val ≤ t + 1 := by omega
            have hne1 : x ≠ ⟨t, by omega⟩ := fin_ne_of_val (by dsimp; omega)
            have heq2 : x = ⟨t + 1, ht⟩ := Fin.ext heq
            simp [heq2]
          · have hle1 : ¬ (x.val ≤ t + 1) := by omega
            have hne1 : x ≠ ⟨t, by omega⟩ := fin_ne_of_val (by dsimp; omega)
            have hne2 : x ≠ ⟨t + 1, ht⟩ := fin_ne_of_val (by dsimp; omega)
            simp [h0, hle, hle1, hne1, hne2]
    have hMeq : (fun i j => M (moveToZeroIdx ⟨t + 1, ht⟩ i) (moveToZeroIdx ⟨t + 1, ht⟩ j)) =
                (fun i j => M1 (moveToZeroIdx ⟨t, by omega⟩ i) (moveToZeroIdx ⟨t, by omega⟩ j)) := by
      funext i j; dsimp only [M1]; unfold swapRC; rw [hcomp i, hcomp j]
    rw [hMeq, ih (by omega) M1 hM1, pfaffian_swapAdj t ht hM, altSign_succ]
    rw [Int.mul_neg, Int.neg_mul]

/-- If a `2n × 2n` skew matrix has zero bottom-right `n × n` block and upper-triangular
    top-right `n × n` block, its Pfaffian is `altSign (n*(n-1)/2) * ∏ U_{i,i}`! -/
theorem pfaffian_zeroCorner_upperTri : ∀ (n : Nat) (M : Mat (2 * n)),
    IsSkew M →
    (∀ (i j : Fin n), M ⟨n + i.val, by omega⟩ ⟨n + j.val, by omega⟩ = 0) →
    (∀ (i j : Fin n), j.val < i.val → M ⟨i.val, by omega⟩ ⟨n + j.val, by omega⟩ = 0) →
    pfaffian n M = altSign (n * (n - 1) / 2) * prodFin (fun i : Fin n => M ⟨i.val, by omega⟩ ⟨n + i.val, by omega⟩)
  | 0, _, _, _, _ => by simp [pfaffian, prodFin, altSign]
  | n + 1, M, hM, hbot, htri => by
    -- Move index (n + 1) to index 0!
    let k : Fin (2 * (n + 1)) := ⟨n + 1, by omega⟩
    let M' : Mat (2 * (n + 1)) := fun i j => M (moveToZeroIdx k i) (moveToZeroIdx k j)
    have hmove := pfaffian_moveToZero k hM
    -- In M', row 0 is old row (n + 1): ONLY col 1 (old col 0) can be nonzero!
    have hrow0 : ∀ j : Fin (2 * n + 1), j ≠ ⟨0, Nat.zero_lt_succ (2 * n)⟩ →
        M' ⟨0, by omega⟩ j.succ = 0 := by
      intro j hj
      dsimp only [M', k]
      have hm0 : moveToZeroIdx (⟨n + 1, by omega⟩ : Fin (2 * (n + 1))) ⟨0, by omega⟩ = ⟨n + 1, by omega⟩ := rfl
      rw [hm0]
      have hjv : 0 < j.val := by
        have : j.val ≠ 0 := fun h => hj (Fin.ext h); omega
      by_cases hjlt : j.val ≤ n
      · have hm1 : moveToZeroIdx (⟨n + 1, by omega⟩ : Fin (2 * (n + 1))) j.succ = ⟨j.val, by omega⟩ := by
          unfold moveToZeroIdx; apply Fin.ext
          have h1 : j.succ.val ≠ 0 := by simp [Fin.succ]
          have h2 : j.succ.val ≤ n + 1 := by simp [Fin.succ]; omega
          simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
          change j.val + 1 - 1 = j.val; omega
        rw [hm1, hM.2]
        have hz := htri ⟨j.val, by omega⟩ ⟨0, by omega⟩ (by dsimp; omega)
        have heq : (⟨n + 1 + 0, by omega⟩ : Fin (2 * (n + 1))) = ⟨n + 1, by omega⟩ := Fin.ext (by simp)
        rw [heq] at hz
        rw [hz]; rfl
      · have hm1 : moveToZeroIdx (⟨n + 1, by omega⟩ : Fin (2 * (n + 1))) j.succ = ⟨n + 1 + (j.val - n), by omega⟩ := by
          unfold moveToZeroIdx; apply Fin.ext
          have h1 : j.succ.val ≠ 0 := by simp [Fin.succ]
          have h2 : ¬ (j.succ.val ≤ n + 1) := by simp [Fin.succ]; omega
          simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
          change j.val + 1 = n + 1 + (j.val - n); omega
        rw [hm1]
        have hz := hbot ⟨0, by omega⟩ ⟨j.val - n, by omega⟩
        have heq : (⟨n + 1 + 0, by omega⟩ : Fin (2 * (n + 1))) = ⟨n + 1, by omega⟩ := Fin.ext (by simp)
        rw [heq] at hz
        exact hz
    have hpf' : pfaffian (n + 1) M' =
        (-M ⟨0, by omega⟩ ⟨n + 1, by omega⟩) *
        pfaffian n (fun r c => M' r.succ.succ c.succ.succ) := by
      change sumFin (fun j : Fin (2 * n + 1) =>
        altSign j.val * M' ⟨0, by omega⟩ j.succ *
        pfaffian n (fun r c => M' (skip0And j r) (skip0And j c))) = _
      rw [sumFin_single ⟨0, Nat.zero_lt_succ (2 * n)⟩ _ (fun j hj => by rw [hrow0 j hj]; simp)]
      simp only [altSign_zero, Int.one_mul]
      have h01 : M' ⟨0, by omega⟩ (⟨0, Nat.zero_lt_succ (2 * n)⟩ : Fin (2 * n + 1)).succ =
                 -M ⟨0, by omega⟩ ⟨n + 1, by omega⟩ := by
        dsimp only [M', k]; unfold moveToZeroIdx
        have h1 : (⟨0, Nat.zero_lt_succ (2 * n)⟩ : Fin (2 * n + 1)).succ.val = 1 := rfl
        have h1ne : (1 : Nat) ≠ 0 := by omega
        have h1le : (1 : Nat) ≤ n + 1 := by omega
        simp only [↓reduceIte, h1, h1ne, h1le, ↓reduceDIte]
        exact hM.2 ⟨n + 1, by omega⟩ ⟨0, by omega⟩
      rw [h01]
      exact congrArg ((-M ⟨0, by omega⟩ ⟨n + 1, by omega⟩) * ·)
        (pfaffian_congr (fun r c => by rw [skip0And_zero, skip0And_zero]))
    let Msub : Mat (2 * n) := fun r c => M' r.succ.succ c.succ.succ
    have hsub_idx : ∀ x : Fin (2 * n),
        moveToZeroIdx k x.succ.succ =
        if hx : x.val < n then ⟨x.val + 1, by omega⟩ else ⟨n + 1 + (x.val - n + 1), by omega⟩ := by
      intro x; apply Fin.ext; dsimp only [k]; unfold moveToZeroIdx
      by_cases hx : x.val < n
      · have h1 : x.succ.succ.val ≠ 0 := by simp [Fin.succ]
        have h2 : x.succ.succ.val ≤ n + 1 := by simp [Fin.succ]; omega
        simp only [hx, h1, h2, ↓reduceIte, ↓reduceDIte]
        change x.val + 2 - 1 = x.val + 1; omega
      · have h1 : x.succ.succ.val ≠ 0 := by simp [Fin.succ]
        have h2 : ¬ (x.succ.succ.val ≤ n + 1) := by simp [Fin.succ]; omega
        simp only [hx, h1, h2, ↓reduceIte, ↓reduceDIte]
        change x.val + 2 = n + 1 + (x.val - n + 1); omega
    have hsub_skew : IsSkew Msub := ⟨fun r => hM.1 _, fun r c => hM.2 _ _⟩
    have hsub_bot : ∀ i j : Fin n, Msub ⟨n + i.val, by omega⟩ ⟨n + j.val, by omega⟩ = 0 := by
      intro i j; dsimp only [Msub, M']
      rw [hsub_idx, hsub_idx]
      have hni : ¬ (n + i.val < n) := by omega
      have hnj : ¬ (n + j.val < n) := by omega
      simp only [hni, hnj, ↓reduceDIte]
      have hi' : (⟨n + 1 + (n + i.val - n + 1), by omega⟩ : Fin (2 * (n + 1))) = ⟨n + 1 + i.succ.val, by omega⟩ :=
        Fin.ext (by simp only [Fin.succ]; omega)
      have hj' : (⟨n + 1 + (n + j.val - n + 1), by omega⟩ : Fin (2 * (n + 1))) = ⟨n + 1 + j.succ.val, by omega⟩ :=
        Fin.ext (by simp only [Fin.succ]; omega)
      rw [hi', hj']; exact hbot i.succ j.succ
    have hsub_tri : ∀ i j : Fin n, j.val < i.val → Msub ⟨i.val, by omega⟩ ⟨n + j.val, by omega⟩ = 0 := by
      intro i j hji; dsimp only [Msub, M']
      rw [hsub_idx, hsub_idx]
      have hnj : ¬ (n + j.val < n) := by omega
      simp only [i.isLt, hnj, ↓reduceDIte]
      have hi' : (⟨i.val + 1, by omega⟩ : Fin (2 * (n + 1))) = ⟨i.succ.val, by omega⟩ := Fin.ext rfl
      have hj' : (⟨n + 1 + (n + j.val - n + 1), by omega⟩ : Fin (2 * (n + 1))) = ⟨n + 1 + j.succ.val, by omega⟩ :=
        Fin.ext (by simp only [Fin.succ]; omega)
      rw [hi', hj']; exact htri i.succ j.succ (by simp only [Fin.succ]; omega)
    have hih := pfaffian_zeroCorner_upperTri n Msub hsub_skew hsub_bot hsub_tri
    have hdiag_sub : prodFin (fun i : Fin n => Msub ⟨i.val, by omega⟩ ⟨n + i.val, by omega⟩) =
                     prodFin (fun i : Fin n => M ⟨i.succ.val, by omega⟩ ⟨n + 1 + i.succ.val, by omega⟩) := by
      apply prodFin_congr; intro i
      dsimp only [Msub, M']; rw [hsub_idx, hsub_idx]
      have hni : ¬ (n + i.val < n) := by omega
      simp only [i.isLt, hni, ↓reduceDIte]
      congr 1 <;> (apply Fin.ext; simp only [Fin.succ]; omega)
    rw [hdiag_sub] at hih
    have hmul_alt : pfaffian (n + 1) M = altSign (n + 1) * pfaffian (n + 1) M' := by
      have h1 : altSign (n + 1) * (altSign (n + 1) * pfaffian (n + 1) M) = altSign (n + 1) * pfaffian (n + 1) M' :=
        congrArg (altSign (n + 1) * ·) hmove.symm
      rw [← Int.mul_assoc, altSign_mul_self, Int.one_mul] at h1
      exact h1
    rw [hmul_alt, hpf', hih]
    rw [prodFin_succ]
    have h0eq : M ⟨(⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)).val, by omega⟩
                  ⟨n + 1 + (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)).val, by omega⟩ =
                M ⟨0, by omega⟩ ⟨n + 1, by omega⟩ := by
      congr 1 <;> (apply Fin.ext; dsimp; omega)
    rw [h0eq]
    have hsign : altSign (n + 1) * (-M ⟨0, by omega⟩ ⟨n + 1, by omega⟩) * altSign (n * (n - 1) / 2) =
                 altSign ((n + 1) * (n + 1 - 1) / 2) * M ⟨0, by omega⟩ ⟨n + 1, by omega⟩ := by
      have htri_arith : (n + 1) * (n + 1 - 1) / 2 = n + n * (n - 1) / 2 := by
        cases n with
        | zero => rfl
        | succ n' =>
          have h1 : (n' + 1 + 1) * (n' + 1) = 2 * (n' + 1) + (n' + 1) * n' := by
            rw [Nat.mul_comm (n' + 1) n', ← Nat.add_mul]; congr 1; omega
          have h2 : (n' + 1 + 1) * (n' + 1 + 1 - 1) = 2 * (n' + 1) + (n' + 1) * (n' + 1 - 1) := by
            simpa using h1
          rw [h2, Nat.mul_add_div (show 0 < 2 by decide)]
      rw [htri_arith, altSign_add n (n * (n - 1) / 2), altSign_succ]
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      ac_rfl
    calc altSign (n + 1) * (-M ⟨0, by omega⟩ ⟨n + 1, by omega⟩ *
          (altSign (n * (n - 1) / 2) * prodFin (fun i : Fin n => M ⟨i.succ.val, by omega⟩ ⟨n + 1 + i.succ.val, by omega⟩)))
        = (altSign (n + 1) * (-M ⟨0, by omega⟩ ⟨n + 1, by omega⟩) * altSign (n * (n - 1) / 2)) *
          prodFin (fun i : Fin n => M ⟨i.succ.val, by omega⟩ ⟨n + 1 + i.succ.val, by omega⟩) := by
          simp only [Int.mul_assoc]
      _ = (altSign ((n + 1) * (n + 1 - 1) / 2) * M ⟨0, by omega⟩ ⟨n + 1, by omega⟩) *
          prodFin (fun i : Fin n => M ⟨i.succ.val, by omega⟩ ⟨n + 1 + i.succ.val, by omega⟩) := by rw [hsign]
      _ = altSign ((n + 1) * (n + 1 - 1) / 2) *
          (M ⟨0, by omega⟩ ⟨n + 1, by omega⟩ *
            prodFin (fun i : Fin n => M ⟨i.succ.val, by omega⟩ ⟨n + 1 + i.succ.val, by omega⟩)) := Int.mul_assoc _ _ _

-- ----------------------------------------------------------------------------
-- Mechanism 3: Order-Reversal, Pure-Pfaffian Self-Congruence &
--              Skew-Conference Complementary-Minor Reflection
-- ----------------------------------------------------------------------------
def revIdx {n : Nat} (i : Fin n) : Fin n :=
  ⟨n - 1 - i.val, by omega⟩

theorem pfaffian_rev {m : Nat} {A : Mat (2 * m)} (hA : IsSkew A) :
    pfaffian m (fun i j => A (revIdx i) (revIdx j)) = altSign m * pfaffian m A := by
  -- Reverse 2m indices via m disjoint transpositions (k ↔ 2m - 1 - k) for k = 0 .. m - 1!
  let pref (k : Nat) (x : Fin (2 * m)) : Fin (2 * m) :=
    if x.val < k ∨ 2 * m - k ≤ x.val then revIdx x else x
  have hstep : ∀ k, k ≤ m →
      pfaffian m (fun i j => A (pref k i) (pref k j)) = altSign k * pfaffian m A := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [altSign_zero, Int.one_mul]
      exact pfaffian_congr (fun i j => by
        have hp0 : ∀ x : Fin (2 * m), pref 0 x = x := by
          intro x; dsimp only [pref]
          have hno : ¬ (x.val < 0 ∨ 2 * m - 0 ≤ x.val) := by omega
          simp only [hno, ↓reduceIte]
        rw [hp0 i, hp0 j])
    | succ k ih =>
      intro hk
      let a : Fin (2 * m) := ⟨k, by omega⟩
      let b : Fin (2 * m) := ⟨2 * m - 1 - k, by omega⟩
      have hab : a ≠ b := fin_ne_of_val (by dsimp [a, b]; omega)
      have hcomp : ∀ x : Fin (2 * m), pref k (swapIdx a b x) = pref (k + 1) x := by
        intro x; apply Fin.ext
        by_cases h1 : x = a
        · rw [h1, swapIdx_left]; dsimp only [pref, a, b, revIdx]
          have hna : ¬ ((⟨2 * m - 1 - k, by omega⟩ : Fin (2 * m)).val < k ∨ 2 * m - k ≤ (⟨2 * m - 1 - k, by omega⟩ : Fin (2 * m)).val) := by dsimp; omega
          have hya : (⟨k, by omega⟩ : Fin (2 * m)).val < k + 1 ∨ 2 * m - (k + 1) ≤ (⟨k, by omega⟩ : Fin (2 * m)).val := by dsimp; omega
          simp only [hna, hya, ↓reduceIte]
        · by_cases h2 : x = b
          · rw [h2, swapIdx_right]; dsimp only [pref, a, b, revIdx]
            have hnb : ¬ ((⟨k, by omega⟩ : Fin (2 * m)).val < k ∨ 2 * m - k ≤ (⟨k, by omega⟩ : Fin (2 * m)).val) := by dsimp; omega
            have hyb : (⟨2 * m - 1 - k, by omega⟩ : Fin (2 * m)).val < k + 1 ∨ 2 * m - (k + 1) ≤ (⟨2 * m - 1 - k, by omega⟩ : Fin (2 * m)).val := by dsimp; omega
            simp only [hnb, hyb, ↓reduceIte]; omega
          · rw [swapIdx_other h1 h2]; dsimp only [pref]
            have hxv1 : x.val ≠ k := fun h => h1 (Fin.ext h)
            have hxv2 : x.val ≠ 2 * m - 1 - k := fun h => h2 (Fin.ext h)
            have hiff : (x.val < k ∨ 2 * m - k ≤ x.val) ↔ (x.val < k + 1 ∨ 2 * m - (k + 1) ≤ x.val) := by omega
            simp only [hiff]
      have hM : (fun i j => A (pref (k + 1) i) (pref (k + 1) j)) =
                swapRC a b (fun i j => A (pref k i) (pref k j)) := by
        funext i j; unfold swapRC; dsimp only; rw [hcomp i, hcomp j]
      have hSkewPrev : IsSkew (fun i j => A (pref k i) (pref k j)) :=
        ⟨fun i => hA.1 _, fun i j => hA.2 _ _⟩
      rw [hM, pfaffian_swapRC a b hab hSkewPrev, ih (by omega), altSign_succ, Int.neg_mul]
  have hfull : (fun i j => A (pref m i) (pref m j)) = (fun i j => A (revIdx i) (revIdx j)) := by
    funext i j
    have hpm : ∀ x : Fin (2 * m), pref m x = revIdx x := by
      intro x; dsimp only [pref]
      have hy : x.val < m ∨ 2 * m - m ≤ x.val := by omega
      simp only [hy, ↓reduceIte]
    rw [hpm i, hpm j]
  rw [← hfull]
  exact hstep m (Nat.le_refl m)

-- Helper: elementary matrices embedded into the bottom-right block `(I_{2m} ⊕ E)`
theorem matMul_blockDiag {p q : Nat} (A1 A2 : Mat p) (B1 B2 : Mat q) :
    matMul (blockDiag A1 B1) (blockDiag A2 B2) = blockDiag (matMul A1 A2) (matMul B1 B2) := by
  funext i j; unfold matMul blockDiag
  rw [sumFin_split]
  by_cases hi : i.val < p <;> by_cases hj : j.val < p
  · simp only [hi, hj, ↓reduceDIte]
    have hz2 : sumFin (fun k : Fin q =>
        (if hk : (⟨p + k.val, by omega⟩ : Fin (p + q)).val < p then
          A1 ⟨i.val, hi⟩ ⟨p + k.val, hk⟩ else 0) *
        (if hk : (⟨p + k.val, by omega⟩ : Fin (p + q)).val < p then
          A2 ⟨p + k.val, hk⟩ ⟨j.val, hj⟩ else 0)) = 0 :=
      sumFin_eq_zero (fun k => by
        have hnk : ¬ ((⟨p + k.val, by omega⟩ : Fin (p + q)).val < p) := by dsimp; omega
        simp only [hnk, ↓reduceDIte, Int.zero_mul])
    rw [hz2, Int.add_zero]
    exact sumFin_congr (fun k => by simp [k.isLt])
  · simp only [hi, hj, ↓reduceDIte]
    have hz1 : sumFin (fun k : Fin p =>
        (if hk : (⟨k.val, by omega⟩ : Fin (p + q)).val < p then A1 ⟨i.val, hi⟩ ⟨k.val, hk⟩ else 0) *
        (if hk : (⟨k.val, by omega⟩ : Fin (p + q)).val < p then 0 else B2 ⟨k.val - p, by omega⟩ ⟨j.val - p, by omega⟩)) = 0 :=
      sumFin_eq_zero (fun k => by simp [k.isLt])
    have hz2 : sumFin (fun k : Fin q =>
        (if hk : (⟨p + k.val, by omega⟩ : Fin (p + q)).val < p then A1 ⟨i.val, hi⟩ ⟨p + k.val, hk⟩ else 0) *
        (if hk : (⟨p + k.val, by omega⟩ : Fin (p + q)).val < p then 0 else B2 ⟨p + k.val - p, by omega⟩ ⟨j.val - p, by omega⟩)) = 0 :=
      sumFin_eq_zero (fun k => by
        have hnk : ¬ ((⟨p + k.val, by omega⟩ : Fin (p + q)).val < p) := by dsimp; omega
        simp only [hnk, ↓reduceDIte, Int.zero_mul])
    rw [hz1, hz2]; rfl
  · simp only [hi, hj, ↓reduceDIte]
    have hz1 : sumFin (fun k : Fin p =>
        (if hk : (⟨k.val, by omega⟩ : Fin (p + q)).val < p then 0 else B1 ⟨i.val - p, by omega⟩ ⟨k.val - p, by omega⟩) *
        (if hk : (⟨k.val, by omega⟩ : Fin (p + q)).val < p then A2 ⟨k.val, hk⟩ ⟨j.val, hj⟩ else 0)) = 0 :=
      sumFin_eq_zero (fun k => by simp [k.isLt])
    have hz2 : sumFin (fun k : Fin q =>
        (if hk : (⟨p + k.val, by omega⟩ : Fin (p + q)).val < p then 0 else B1 ⟨i.val - p, by omega⟩ ⟨p + k.val - p, by omega⟩) *
        (if hk : (⟨p + k.val, by omega⟩ : Fin (p + q)).val < p then A2 ⟨p + k.val, hk⟩ ⟨j.val, hj⟩ else 0)) = 0 :=
      sumFin_eq_zero (fun k => by
        have hnk : ¬ ((⟨p + k.val, by omega⟩ : Fin (p + q)).val < p) := by dsimp; omega
        simp only [hnk, ↓reduceDIte, Int.mul_zero])
    rw [hz1, hz2]; rfl
  · simp only [hi, hj, ↓reduceDIte]
    have hz1 : sumFin (fun k : Fin p =>
        (if hk : (⟨k.val, by omega⟩ : Fin (p + q)).val < p then 0 else B1 ⟨i.val - p, by omega⟩ ⟨k.val - p, by omega⟩) *
        (if hk : (⟨k.val, by omega⟩ : Fin (p + q)).val < p then 0 else B2 ⟨k.val - p, by omega⟩ ⟨j.val - p, by omega⟩)) = 0 :=
      sumFin_eq_zero (fun k => by simp [k.isLt])
    rw [hz1, Int.zero_add]
    apply sumFin_congr; intro k
    have hnk : ¬ ((⟨p + k.val, by omega⟩ : Fin (p + q)).val < p) := by dsimp; omega
    simp only [hnk, ↓reduceDIte]
    have hk' : (⟨p + k.val - p, by omega⟩ : Fin q) = k := Fin.ext (by dsimp; omega)
    rw [hk']

theorem matMul_castMat {n m : Nat} (h : n = m) (A B : Mat n) :
    matMul (castMat h A) (castMat h B) = castMat h (matMul A B) := by
  subst h; funext i j; unfold castMat matMul; exact sumFin_congr (fun _ => rfl)

theorem matTrans_castMat {n m : Nat} (h : n = m) (A : Mat n) :
    matTrans (castMat h A) = castMat h (matTrans A) := by
  subst h; funext i j; rfl

theorem matTrans_blockDiag {p q : Nat} (A : Mat p) (B : Mat q) :
    matTrans (blockDiag A B) = blockDiag (matTrans A) (matTrans B) := by
  funext i j; unfold matTrans blockDiag
  by_cases hi : i.val < p <;> by_cases hj : j.val < p <;> simp [hi, hj]

theorem matTrans_matId (n : Nat) : matTrans (matId n) = matId n := by
  funext i j; unfold matTrans matId; simp [eq_comm]

theorem matMul_matId_left {n : Nat} (A : Mat n) : matMul (matId n) A = A := by
  funext i j; unfold matMul matId
  rw [sumFin_single i _ (fun k hk => by simp [Ne.symm hk])]; simp

theorem matMul_matId_right {n : Nat} (A : Mat n) : matMul A (matId n) = A := by
  funext i j; unfold matMul matId
  rw [sumFin_single j _ (fun k hk => by simp [hk])]; simp

theorem elemScale_blockDiag {m n : Nat} (a : Fin (2 * n)) (c : Int) :
    castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockDiag (matId (2 * m)) (elemScale a c)) =
    elemScale ⟨2 * m + a.val, by omega⟩ c := by
  funext i j; unfold castMat blockDiag matId elemScale
  by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
  · have hne : i ≠ ⟨2 * m + a.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
    simp [hi, hj, hne, Fin.ext_iff]
  · have hne : i ≠ j := fin_ne_of_val (by omega)
    simp [hi, hj, hne]
  · have hne : i ≠ j := fin_ne_of_val (by omega)
    simp [hi, hj, hne]
  · have hiff1 : (⟨i.val - 2 * m, by omega⟩ : Fin (2 * n)) = ⟨j.val - 2 * m, by omega⟩ ↔ i = j := by
      simp only [Fin.ext_iff]; omega
    have hiff2 : (⟨i.val - 2 * m, by omega⟩ : Fin (2 * n)) = a ↔ i = ⟨2 * m + a.val, by omega⟩ := by
      simp only [Fin.ext_iff]; omega
    simp [hi, hj, hiff1, hiff2]

theorem elemSwap_blockDiag {m n : Nat} (a b : Fin (2 * n)) :
    castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockDiag (matId (2 * m)) (elemSwap a b)) =
    elemSwap ⟨2 * m + a.val, by omega⟩ ⟨2 * m + b.val, by omega⟩ := by
  funext i j; unfold castMat blockDiag matId elemSwap
  by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
  · have hne1 : j ≠ ⟨2 * m + a.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
    have hne2 : j ≠ ⟨2 * m + b.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
    rw [swapIdx_other hne1 hne2]; simp [hi, hj, Fin.ext_iff]
  · have hne : i ≠ swapIdx ⟨2 * m + a.val, by omega⟩ ⟨2 * m + b.val, by omega⟩ j := by
      unfold swapIdx; by_cases h1 : j = ⟨2 * m + a.val, by omega⟩
      · simp only [h1, ↓reduceIte]; exact fin_ne_of_val (by dsimp; omega)
      · by_cases h2 : j = ⟨2 * m + b.val, by omega⟩
        · simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte]; exact fin_ne_of_val (by dsimp; omega)
        · simp only [h1, h2, ↓reduceIte]; exact fin_ne_of_val (by omega)
    simp [hi, hj, hne]
  · have hne1 : j ≠ ⟨2 * m + a.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
    have hne2 : j ≠ ⟨2 * m + b.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
    rw [swapIdx_other hne1 hne2]
    have hne : i ≠ j := fin_ne_of_val (by omega)
    simp [hi, hj, hne]
  · simp only [hi, hj, ↓reduceDIte]
    have hiff : (⟨i.val - 2 * m, by omega⟩ : Fin (2 * n)) = swapIdx a b ⟨j.val - 2 * m, by omega⟩ ↔
                i = swapIdx ⟨2 * m + a.val, by omega⟩ ⟨2 * m + b.val, by omega⟩ j := by
      unfold swapIdx
      by_cases h1 : j.val = 2 * m + a.val
      · have e1 : (⟨j.val - 2 * m, by omega⟩ : Fin (2 * n)) = a := Fin.ext (by dsimp; omega)
        have e2 : j = ⟨2 * m + a.val, by omega⟩ := Fin.ext h1
        rw [e1, e2]; simp only [↓reduceIte, Fin.ext_iff]; omega
      · have ne1 : (⟨j.val - 2 * m, by omega⟩ : Fin (2 * n)) ≠ a := fin_ne_of_val (by dsimp; omega)
        have ne2 : j ≠ ⟨2 * m + a.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
        by_cases h2 : j.val = 2 * m + b.val
        · have e1 : (⟨j.val - 2 * m, by omega⟩ : Fin (2 * n)) = b := Fin.ext (by dsimp; omega)
          have e2 : j = ⟨2 * m + b.val, by omega⟩ := Fin.ext h2
          simp only [ne1, ne2, ↓reduceIte]; rw [e1, e2]; simp only [↓reduceIte, Fin.ext_iff]; omega
        · have ne3 : (⟨j.val - 2 * m, by omega⟩ : Fin (2 * n)) ≠ b := fin_ne_of_val (by dsimp; omega)
          have ne4 : j ≠ ⟨2 * m + b.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
          simp only [ne1, ne2, ne3, ne4, ↓reduceIte, Fin.ext_iff]; omega
    simp [hiff]

theorem elemShear_blockDiag {m n : Nat} (a b : Fin (2 * n)) (c : Int) :
    castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockDiag (matId (2 * m)) (elemShear a b c)) =
    elemShear ⟨2 * m + a.val, by omega⟩ ⟨2 * m + b.val, by omega⟩ c := by
  funext i j; unfold castMat blockDiag matId elemShear
  by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
  · have hne : i ≠ ⟨2 * m + b.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
    simp [hi, hj, hne, Fin.ext_iff]
  · have hne1 : i ≠ j := fin_ne_of_val (by omega)
    have hne2 : i ≠ ⟨2 * m + b.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
    simp [hi, hj, hne1, hne2]
  · have hne1 : i ≠ j := fin_ne_of_val (by omega)
    have hne2 : j ≠ ⟨2 * m + a.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
    simp [hi, hj, hne1, hne2]
  · have hiff1 : (⟨i.val - 2 * m, by omega⟩ : Fin (2 * n)) = ⟨j.val - 2 * m, by omega⟩ ↔ i = j := by
      simp only [Fin.ext_iff]; omega
    have hiff2 : ((⟨i.val - 2 * m, by omega⟩ : Fin (2 * n)) = b ∧ (⟨j.val - 2 * m, by omega⟩ : Fin (2 * n)) = a) ↔
                 (i = ⟨2 * m + b.val, by omega⟩ ∧ j = ⟨2 * m + a.val, by omega⟩) := by
      simp only [Fin.ext_iff]; omega
    simp [hi, hj, hiff1, hiff2]

theorem matTrans_elemScale {n : Nat} (a : Fin n) (c : Int) :
    matTrans (elemScale a c) = elemScale a c := by
  funext i j; unfold matTrans elemScale; by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem matTrans_elemSwap {n : Nat} (a b : Fin n) :
    matTrans (elemSwap a b) = elemSwap a b := by
  funext i j; unfold matTrans elemSwap
  have hiff : (j = swapIdx a b i) ↔ (i = swapIdx a b j) := by
    constructor
    · intro h; rw [h, swapIdx_invol]
    · intro h; rw [h, swapIdx_invol]
  simp [hiff]

theorem matTrans_elemShear {n : Nat} (a b : Fin n) (c : Int) :
    matTrans (elemShear a b c) = elemShear b a c := by
  funext i j; unfold matTrans elemShear
  simp [eq_comm, and_comm]

def popcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else n % 2 + popcountAux fuel (n / 2)

def popcount (n : Nat) : Nat :=
  popcountAux n n

def paritySign (x : Nat) : Int :=
  if popcount x % 2 = 0 then 1 else -1

def gray (x : Nat) : Nat :=
  x ^^^ (x >>> 1)

def invGrayAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else n ^^^ invGrayAux fuel (n / 2)

def invGray (n : Nat) : Nat :=
  invGrayAux n n

def carries (x y : Nat) : Int :=
  (popcount x : Int) + (popcount y : Int) - (popcount (x + y) : Int)

def msbAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n / 2 = 0 then 0 else 1 + msbAux fuel (n / 2)

def msb (n : Nat) : Nat :=
  msbAux n n

def sgnInt (i j : Nat) : Int :=
  if i < j then 1 else if j < i then -1 else 0

theorem popcountAux_eq : ∀ (f1 f2 n : Nat), n ≤ f1 → n ≤ f2 → popcountAux f1 n = popcountAux f2 n
  | 0, f2, n, h1, _ => by
    have hn : n = 0 := by omega
    subst hn; cases f2 <;> rfl
  | f1 + 1, 0, n, _, h2 => by
    have hn : n = 0 := by omega
    subst hn; rfl
  | f1 + 1, f2 + 1, n, h1, h2 => by
    unfold popcountAux
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      rw [popcountAux_eq f1 f2 (n / 2) (by omega) (by omega)]

theorem popcount_succ (n : Nat) : popcount (n + 1) = (n + 1) % 2 + popcount ((n + 1) / 2) := by
  change (if n + 1 = 0 then 0 else (n + 1) % 2 + popcountAux n ((n + 1) / 2)) =
         (n + 1) % 2 + popcountAux ((n + 1) / 2) ((n + 1) / 2)
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  congr 1
  exact popcountAux_eq n ((n + 1) / 2) ((n + 1) / 2) (by omega) (Nat.le_refl _)

theorem msbAux_eq : ∀ (f1 f2 n : Nat), n ≤ f1 → n ≤ f2 → msbAux f1 n = msbAux f2 n
  | 0, f2, n, h1, _ => by
    have hn : n = 0 := by omega
    subst hn; cases f2 <;> rfl
  | f1 + 1, 0, n, _, h2 => by
    have hn : n = 0 := by omega
    subst hn; rfl
  | f1 + 1, f2 + 1, n, h1, h2 => by
    unfold msbAux
    by_cases hd : n / 2 = 0
    · simp [hd]
    · simp only [hd, ↓reduceIte]
      rw [msbAux_eq f1 f2 (n / 2) (by omega) (by omega)]

theorem msb_succ (n : Nat) : msb (n + 1) = if (n + 1) / 2 = 0 then 0 else 1 + msb ((n + 1) / 2) := by
  change (if (n + 1) / 2 = 0 then 0 else 1 + msbAux n ((n + 1) / 2)) =
         if (n + 1) / 2 = 0 then 0 else 1 + msbAux ((n + 1) / 2) ((n + 1) / 2)
  by_cases hd : (n + 1) / 2 = 0
  · simp [hd]
  · simp only [hd, ↓reduceIte]
    congr 1
    exact msbAux_eq n ((n + 1) / 2) ((n + 1) / 2) (by omega) (Nat.le_refl _)

theorem pow2_succ (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem pow2_eq_add (k : Nat) : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  rw [pow2_succ]; omega

theorem int_pow_ne_zero {a : Int} (ha : a ≠ 0) : ∀ n : Nat, a ^ n ≠ 0
  | 0 => by simp [Int.pow_zero]
  | n + 1 => by rw [Int.pow_succ]; exact Int.mul_ne_zero (int_pow_ne_zero ha n) ha

theorem int_pow_eq_zero_iff {a : Int} {n : Nat} (hn : 1 ≤ n) : a ^ n = 0 ↔ a = 0 := by
  constructor
  · intro h
    exact Classical.byContradiction (fun ha => int_pow_ne_zero ha n h)
  · intro ha; subst ha
    cases n with
    | zero => omega
    | succ m => rw [Int.pow_succ, Int.mul_zero]

theorem popcount_two_mul_add (m b : Nat) (hb : b < 2) :
    popcount (2 * m + b) = b + popcount m := by
  cases m with
  | zero =>
    cases b with
    | zero => decide
    | succ b' =>
      have hb0 : b' = 0 := by omega
      subst hb0; decide
  | succ m' =>
    have hpos : ∃ t, 2 * (m' + 1) + b = t + 1 := ⟨2 * m' + 1 + b, by omega⟩
    rcases hpos with ⟨t, ht⟩
    rw [ht, popcount_succ]
    have hmod : (t + 1) % 2 = b := by omega
    have hdiv : (t + 1) / 2 = m' + 1 := by omega
    rw [hmod, hdiv]

theorem popcount_add_pow2_mul : ∀ (k q x : Nat), x < 2 ^ k →
    popcount (q * 2 ^ k + x) = popcount q + popcount x
  | 0, q, x, hx => by
    have hx0 : x = 0 := by simp at hx; omega
    subst hx0; have hp0 : popcount 0 = 0 := rfl; simp [hp0]
  | k + 1, q, x, hx => by
    have h1 : q * 2 ^ (k + 1) + x = 2 * (q * 2 ^ k + x / 2) + x % 2 := by
      rw [pow2_succ, ← Nat.mul_assoc, Nat.mul_comm q 2, Nat.mul_assoc]; omega
    have h2 : x = 2 * (x / 2) + x % 2 := by omega
    have hx' : x / 2 < 2 ^ k := by rw [pow2_succ] at hx; omega
    rw [h1, popcount_two_mul_add _ _ (by omega), popcount_add_pow2_mul k q (x / 2) hx']
    conv => rhs; rw [h2]
    rw [popcount_two_mul_add _ _ (by omega)]
    omega

theorem popcount_add_pow2 (k x : Nat) (hx : x < 2 ^ k) :
    popcount (2 ^ k + x) = 1 + popcount x := by
  have h := popcount_add_pow2_mul k 1 x hx
  have hp1 : popcount 1 = 1 := by decide
  simp only [Nat.one_mul, hp1] at h
  exact h

theorem paritySign_sq (x : Nat) : paritySign x * paritySign x = 1 := by
  unfold paritySign; split <;> decide

theorem paritySign_add_pow2 (k x : Nat) (hx : x < 2 ^ k) :
    paritySign (2 ^ k + x) = -paritySign x := by
  unfold paritySign; rw [popcount_add_pow2 k x hx]
  split <;> split <;> omega

theorem testBit_lt_pow2 : ∀ (k x : Nat), x < 2 ^ k → ∀ i, k ≤ i → x.testBit i = false
  | 0, x, hx, i, _ => by
    have hx0 : x = 0 := by simp at hx; omega
    subst hx0; simp
  | k + 1, x, hx, 0, hi => by omega
  | k + 1, x, hx, i + 1, hi => by
    rw [Nat.testBit_succ]
    exact testBit_lt_pow2 k (x / 2) (by rw [pow2_succ] at hx; omega) i (by omega)

theorem lt_pow2_of_testBit : ∀ (k x : Nat), (∀ i, k ≤ i → x.testBit i = false) → x < 2 ^ k
  | 0, x, h => by
    have hx0 : x = 0 := Nat.eq_of_testBit_eq (fun i => by rw [h i (Nat.zero_le i)]; simp)
    subst hx0; decide
  | k + 1, x, h => by
    have hdiv : x / 2 < 2 ^ k := lt_pow2_of_testBit k (x / 2) (fun i hi => by
      rw [← Nat.testBit_succ]; exact h (i + 1) (by omega))
    rw [pow2_succ]; omega

theorem testBit_add_pow2 : ∀ (k x : Nat), x < 2 ^ k → ∀ i,
    (2 ^ k + x).testBit i = (decide (i = k) || x.testBit i)
  | 0, x, hx, i => by
    have hx0 : x = 0 := by simp at hx; omega
    subst hx0; cases i with
    | zero => decide
    | succ n => rw [Nat.testBit_succ]; simp
  | k + 1, x, hx, 0 => by
    rw [Nat.testBit_zero, Nat.testBit_zero, pow2_succ]
    have hmod : (2 * 2 ^ k + x) % 2 = x % 2 := by omega
    simp [hmod]
  | k + 1, x, hx, i + 1 => by
    rw [Nat.testBit_succ, Nat.testBit_succ]
    have hdiv : (2 ^ (k + 1) + x) / 2 = 2 ^ k + x / 2 := by rw [pow2_succ]; omega
    rw [hdiv, testBit_add_pow2 k (x / 2) (by rw [pow2_succ] at hx; omega) i]
    by_cases hik : i = k <;> simp [hik]

theorem testBit_sub_pow2 : ∀ (k x : Nat), x < 2 ^ k → ∀ i,
    (2 ^ k - 1 - x).testBit i = (decide (i < k) && !x.testBit i)
  | 0, x, hx, i => by
    have hx0 : x = 0 := by simp at hx; omega
    subst hx0; simp
  | k + 1, x, hx, 0 => by
    rw [Nat.testBit_zero, Nat.testBit_zero]
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    have hmod : (2 ^ (k + 1) - 1 - x) % 2 = 1 - x % 2 := by rw [pow2_succ]; omega
    rw [hmod]
    have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases hx2 with h0 | h1
    · simp [h0]
    · simp [h1]
  | k + 1, x, hx, i + 1 => by
    rw [Nat.testBit_succ, Nat.testBit_succ]
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    have hdiv : (2 ^ (k + 1) - 1 - x) / 2 = 2 ^ k - 1 - x / 2 := by rw [pow2_succ]; omega
    rw [hdiv, testBit_sub_pow2 k (x / 2) (by rw [pow2_succ] at hx; omega) i]
    by_cases hik : i < k <;> simp [hik]

theorem bitCompl_eq_sub (k x : Nat) (hx : x < 2 ^ k) :
    (2 ^ k - 1) ^^^ x = 2 ^ k - 1 - x := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_sub_pow2 k x hx i]
  have hmask := testBit_sub_pow2 k 0 (Nat.two_pow_pos k) i
  simp only [Nat.sub_zero, Nat.zero_testBit, Bool.not_false, Bool.and_true] at hmask
  rw [hmask]
  by_cases hik : i < k
  · simp [hik]
  · have hxf := testBit_lt_pow2 k x hx i (by omega)
    simp [hik, hxf]

theorem popcount_xor_two_pow : ∀ (k x : Nat), paritySign (x ^^^ 2 ^ k) = -paritySign x
  | 0, x => by
    have hxor : x ^^^ 1 = if x % 2 = 0 then x + 1 else x - 1 := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_xor]
      cases i with
      | zero =>
        rw [Nat.testBit_zero]
        have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
        rcases hx2 with h0 | h1
        · have hx1 : (x + 1) % 2 = 1 := by omega
          simp [h0, Nat.testBit_zero, hx1]
        · have hx1 : (x - 1) % 2 = 0 := by omega
          simp [h1, Nat.testBit_zero, hx1]
      | succ i =>
        rw [Nat.testBit_succ]
        have h1 : (1 : Nat).testBit (i + 1) = false := by rw [Nat.testBit_succ]; simp
        rw [h1, Bool.xor_false]
        split
        · rw [Nat.testBit_succ]; congr 1; omega
        · rw [Nat.testBit_succ]; congr 1; omega
    rw [hxor]; unfold paritySign
    by_cases h0 : x % 2 = 0
    · simp only [h0, ↓reduceIte]
      have hx : x = 2 * (x / 2) + 0 := by omega
      have hx1 : x + 1 = 2 * (x / 2) + 1 := by omega
      rw [hx1, popcount_two_mul_add _ _ (by decide)]
      conv => rhs; rw [hx]
      rw [popcount_two_mul_add _ _ (by decide)]
      split <;> split <;> omega
    · simp only [h0, ↓reduceIte]
      have hx : x = 2 * (x / 2) + 1 := by omega
      have hx1 : x - 1 = 2 * (x / 2) + 0 := by omega
      rw [hx1, popcount_two_mul_add _ _ (by decide)]
      conv => rhs; rw [hx]
      rw [popcount_two_mul_add _ _ (by decide)]
      split <;> split <;> omega
  | k + 1, x => by
    have hmod : (x ^^^ 2 ^ (k + 1)) % 2 = x % 2 := by
      have h0 : (x ^^^ 2 ^ (k + 1)).testBit 0 = x.testBit 0 := by
        rw [Nat.testBit_xor, Nat.testBit_two_pow]; simp
      rw [Nat.testBit_zero, Nat.testBit_zero] at h0
      have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hy2 : (x ^^^ 2 ^ (k + 1)) % 2 = 0 ∨ (x ^^^ 2 ^ (k + 1)) % 2 = 1 := by omega
      rcases hx2 with h1 | h1 <;> rcases hy2 with h2 | h2 <;> simp_all
    have hdiv : (x ^^^ 2 ^ (k + 1)) / 2 = (x / 2) ^^^ 2 ^ k := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ,
          Nat.testBit_two_pow, Nat.testBit_two_pow]
      by_cases hik : k = i <;> simp [hik]
    have hdecomp1 : x ^^^ 2 ^ (k + 1) = 2 * ((x / 2) ^^^ 2 ^ k) + x % 2 := by omega
    have hdecomp2 : x = 2 * (x / 2) + x % 2 := by omega
    have hih := popcount_xor_two_pow k (x / 2)
    unfold paritySign at hih ⊢
    rw [hdecomp1, popcount_two_mul_add _ _ (by omega)]
    conv => rhs; rw [hdecomp2]
    rw [popcount_two_mul_add _ _ (by omega)]
    split at hih <;> split at hih <;> split <;> split <;> omega

theorem paritySign_and_xor_pow2 (k x y : Nat) :
    paritySign (x &&& (2 ^ k ^^^ y)) = (if x.testBit k then -1 else 1) * paritySign (x &&& y) := by
  by_cases hxk : x.testBit k = true
  · simp only [hxk, ↓reduceIte]
    have heq : (x &&& (2 ^ k ^^^ y)) = (x &&& y) ^^^ 2 ^ k := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hik : k = i
      · subst hik; simp [hxk]
      · simp [hik]
    rw [heq, popcount_xor_two_pow]; omega
  · have hxkf : x.testBit k = false := by cases h : x.testBit k <;> simp_all
    simp only [hxkf, Bool.false_eq_true, ↓reduceIte, Int.one_mul]
    congr 1
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hik : k = i
    · subst hik; simp [hxkf]
    · simp [hik]

theorem gray_lt_pow2 (k x : Nat) (hx : x < 2 ^ k) : gray x < 2 ^ k := by
  apply lt_pow2_of_testBit; intro i hi
  unfold gray; rw [Nat.testBit_xor, Nat.testBit_shiftRight]
  rw [testBit_lt_pow2 k x hx i hi, testBit_lt_pow2 k x hx (1 + i) (by omega)]; rfl

theorem gray_add_pow2 (k x : Nat) (hk : 1 ≤ k) (hx : x < 2 ^ k) :
    gray (2 ^ k + x) = 2 ^ k + (2 ^ (k - 1) ^^^ gray x) := by
  have hglt : 2 ^ (k - 1) ^^^ gray x < 2 ^ k := by
    apply lt_pow2_of_testBit; intro i hi
    rw [Nat.testBit_xor, Nat.testBit_two_pow, testBit_lt_pow2 k (gray x) (gray_lt_pow2 k x hx) i hi]
    have hne : k - 1 ≠ i := by omega
    simp [hne]
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_add_pow2 k _ hglt i, Nat.testBit_xor, Nat.testBit_two_pow]
  unfold gray
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, testBit_add_pow2 k x hx i,
      testBit_add_pow2 k x hx (1 + i), Nat.testBit_xor, Nat.testBit_shiftRight]
  by_cases hi1 : i = k
  · rw [hi1]
    have hne2 : ¬ (k - 1 = k) := by omega
    have hf1 := testBit_lt_pow2 k x hx k (Nat.le_refl k)
    have hf2 := testBit_lt_pow2 k x hx (1 + k) (by omega)
    simp [hne2, hf1, hf2]
  · by_cases hi2 : 1 + i = k
    · have hkm : k - 1 = i := by omega
      have hf2 := testBit_lt_pow2 k x hx k (Nat.le_refl k)
      simp [hi1, hi2, hkm, hf2]
    · have hkm : ¬ (k - 1 = i) := by omega
      simp [hi1, hi2, hkm]

theorem gray_compl (k x : Nat) (hx : x < 2 ^ (k + 1)) :
    gray (2 ^ (k + 1) - 1 - x) = 2 ^ k ^^^ gray x := by
  apply Nat.eq_of_testBit_eq; intro i
  unfold gray
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_two_pow,
      Nat.testBit_xor, Nat.testBit_shiftRight,
      testBit_sub_pow2 (k + 1) x hx i, testBit_sub_pow2 (k + 1) x hx (1 + i)]
  by_cases hi : i < k
  · have hi1 : i < k + 1 := by omega
    have hi2 : 1 + i < k + 1 := by omega
    have hne : k ≠ i := by omega
    simp only [hi1, hi2, hne, decide_true, decide_false, Bool.true_and, Bool.false_bne]
    cases x.testBit i <;> cases x.testBit (1 + i) <;> rfl
  · by_cases hik : k = i
    · subst hik
      have hi1 : k < k + 1 := by omega
      have hi2 : ¬ (1 + k < k + 1) := by omega
      have hf2 := testBit_lt_pow2 (k + 1) x hx (1 + k) (by omega)
      simp only [hi1, hi2, hf2, decide_true, decide_false, Bool.true_and, Bool.false_and,
                 Bool.bne_false, Bool.true_bne]
    · have hi1 : ¬ (i < k + 1) := by omega
      have hi2 : ¬ (1 + i < k + 1) := by omega
      have hf1 := testBit_lt_pow2 (k + 1) x hx i (by omega)
      have hf2 := testBit_lt_pow2 (k + 1) x hx (1 + i) (by omega)
      simp [hi1, hi2, hik, hf1, hf2]

theorem and_add_pow2_left (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    ((2 ^ k + x) &&& y) = (x &&& y) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_and, testBit_add_pow2 k x hx i]
  by_cases hik : i = k
  · rw [hik, testBit_lt_pow2 k y hy k (Nat.le_refl k)]; simp
  · simp [hik]

theorem and_add_pow2_both (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    ((2 ^ k + x) &&& (2 ^ k + y)) = 2 ^ k + (x &&& y) := by
  have hlt : (x &&& y) < 2 ^ k := by
    apply lt_pow2_of_testBit; intro i hi
    rw [Nat.testBit_and, testBit_lt_pow2 k x hx i hi]; rfl
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, testBit_add_pow2 k x hx i, testBit_add_pow2 k y hy i,
      testBit_add_pow2 k (x &&& y) hlt i, Nat.testBit_and]
  by_cases hik : i = k <;> simp [hik]

theorem msb_eq_of_bounds : ∀ (k n : Nat), 2 ^ k ≤ n → n < 2 ^ (k + 1) → msb n = k
  | 0, n, h1, h2 => by
    have hn : n = 1 := by simp at h1 h2; omega
    subst hn; decide
  | k + 1, n, h1, h2 => by
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    have hn_pos : ∃ m, n = m + 1 := ⟨n - 1, by rw [pow2_succ] at h1; omega⟩
    rcases hn_pos with ⟨m, hm⟩
    rw [hm, msb_succ]
    have hdiv_pos : (m + 1) / 2 ≠ 0 := by rw [pow2_succ] at h1; omega
    simp only [hdiv_pos, ↓reduceIte]
    have hih := msb_eq_of_bounds k ((m + 1) / 2)
      (by rw [pow2_succ] at h1; omega) (by rw [pow2_succ] at h2; omega)
    omega

theorem xor_add_pow2_right (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    x ^^^ (2 ^ k + y) = 2 ^ k + (x ^^^ y) := by
  have hlt : x ^^^ y < 2 ^ k := by
    apply lt_pow2_of_testBit; intro i hi
    rw [Nat.testBit_xor, testBit_lt_pow2 k x hx i hi, testBit_lt_pow2 k y hy i hi]; rfl
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_add_pow2 k y hy i, testBit_add_pow2 k (x ^^^ y) hlt i, Nat.testBit_xor]
  by_cases hik : i = k
  · rw [hik, testBit_lt_pow2 k x hx k (Nat.le_refl k)]; simp
  · simp [hik]

theorem xor_add_pow2_both (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    (2 ^ k + x) ^^^ (2 ^ k + y) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_add_pow2 k x hx i, testBit_add_pow2 k y hy i]
  by_cases hik : i = k
  · rw [hik, testBit_lt_pow2 k x hx k (Nat.le_refl k), testBit_lt_pow2 k y hy k (Nat.le_refl k)]; simp
  · simp [hik]

theorem msb_xor_add_pow2_right (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    msb (x ^^^ (2 ^ k + y)) = k := by
  rw [xor_add_pow2_right k x y hx hy]
  have hlt : x ^^^ y < 2 ^ k := by
    apply lt_pow2_of_testBit; intro i hi
    rw [Nat.testBit_xor, testBit_lt_pow2 k x hx i hi, testBit_lt_pow2 k y hy i hi]; rfl
  exact msb_eq_of_bounds k _ (by omega) (by rw [pow2_eq_add]; omega)

-- ----------------------------------------------------------------------------
-- 5.2 Theorem A: Carry-Asymmetry Homogeneous Mersenne-Root Pfaffian Pencil
-- ----------------------------------------------------------------------------

def skewOnesMat (n : Nat) : Mat n :=
  fun i j => sgnInt i.val j.val

def carryAsymMat (k : Nat) : Mat (2 ^ k) :=
  fun i j => carries i.val ((2 ^ k - 1) ^^^ j.val) - carries j.val ((2 ^ k - 1) ^^^ i.val)

def carryPencilMat (k : Nat) (a b : Int) : Mat (2 ^ k) :=
  fun i j => a * carryAsymMat k i j + b * skewOnesMat (2 ^ k) i j

theorem isSkew_skewOnes (n : Nat) : IsSkew (skewOnesMat n) := by
  constructor
  · intro i; unfold skewOnesMat sgnInt; simp
  · intro i j; unfold skewOnesMat sgnInt
    by_cases h1 : i.val < j.val
    · have h2 : ¬ (j.val < i.val) := by omega
      simp [h1, h2]
    · by_cases h2 : j.val < i.val
      · simp [h1, h2]
      · simp [h1, h2]

theorem isSkew_carryAsym (k : Nat) : IsSkew (carryAsymMat k) := by
  constructor
  · intro i; unfold carryAsymMat; omega
  · intro i j; unfold carryAsymMat; omega

theorem isSkew_carryPencil (k : Nat) (a b : Int) : IsSkew (carryPencilMat k a b) := by
  constructor
  · intro i; unfold carryPencilMat
    rw [(isSkew_carryAsym k).1 i, (isSkew_skewOnes (2 ^ k)).1 i]; simp
  · intro i j; unfold carryPencilMat
    rw [(isSkew_carryAsym k).2 i j, (isSkew_skewOnes (2 ^ k)).2 i j]
    simp only [Int.mul_neg]; omega

theorem sumFin_altSign_even : ∀ m : Nat, sumFin (fun k : Fin (2 * m) => altSign k.val) = 0
  | 0 => rfl
  | m + 1 => by
    rw [← sumFin_cast (show 2 + 2 * m = 2 * (m + 1) by omega), sumFin_split]
    have h1 : sumFin (fun i : Fin 2 => altSign i.val) = 0 := by decide
    have h2 : sumFin (fun j : Fin (2 * m) => altSign (2 + j.val)) =
              sumFin (fun j : Fin (2 * m) => altSign j.val) :=
      sumFin_congr (fun j => by rw [altSign_add, altSign_two_mul 1, Int.one_mul])
    change sumFin (fun i : Fin 2 => altSign i.val) + sumFin (fun j : Fin (2 * m) => altSign (2 + j.val)) = 0
    rw [h1, h2, sumFin_altSign_even m]; rfl

theorem sumFin_altSign_skewOnes : ∀ (m : Nat) (j : Fin (2 * m)),
    sumFin (fun k : Fin (2 * m) => altSign k.val * skewOnesMat (2 * m) k j) = 1
  | 0, j => Fin.elim0 j
  | m + 1, j => by
    rw [← sumFin_cast (show 2 + 2 * m = 2 * (m + 1) by omega), sumFin_split]
    by_cases hj : j.val < 2
    · have h1 : sumFin (fun i : Fin 2 => altSign i.val * skewOnesMat (2 * (m + 1)) ⟨i.val, by omega⟩ j) = 1 := by
        simp only [sumFin_succ, sumFin_zero, Int.add_zero]
        have hj2 : j.val = 0 ∨ j.val = 1 := by omega
        rcases hj2 with h0 | h1
        · unfold skewOnesMat sgnInt; simp [h0]
        · unfold skewOnesMat sgnInt; simp [h1]
      have h2 : sumFin (fun i : Fin (2 * m) => altSign (2 + i.val) * skewOnesMat (2 * (m + 1)) ⟨2 + i.val, by omega⟩ j) = 0 := by
        have hcongr : sumFin (fun i : Fin (2 * m) => altSign (2 + i.val) * skewOnesMat (2 * (m + 1)) ⟨2 + i.val, by omega⟩ j) =
                      sumFin (fun i : Fin (2 * m) => -altSign i.val) := by
          apply sumFin_congr; intro i
          rw [altSign_add, altSign_two_mul 1, Int.one_mul]
          unfold skewOnesMat sgnInt
          have hgt : j.val < 2 + i.val := by omega
          have hnl : ¬ (2 + i.val < j.val) := by omega
          simp [hgt, hnl]
        rw [hcongr, sumFin_neg, sumFin_altSign_even m]; rfl
      change sumFin (fun i : Fin 2 => altSign i.val * skewOnesMat (2 * (m + 1)) ⟨i.val, by omega⟩ j) +
             sumFin (fun i : Fin (2 * m) => altSign (2 + i.val) * skewOnesMat (2 * (m + 1)) ⟨2 + i.val, by omega⟩ j) = 1
      rw [h1, h2]; rfl
    · have h1 : sumFin (fun i : Fin 2 => altSign i.val * skewOnesMat (2 * (m + 1)) ⟨i.val, by omega⟩ j) = 0 := by
        simp only [sumFin_succ, sumFin_zero, Int.add_zero]
        unfold skewOnesMat sgnInt
        have hlt0 : 0 < j.val := by omega
        have hlt1 : 1 < j.val := by omega
        simp [hlt0, hlt1]
      have h2 : sumFin (fun i : Fin (2 * m) => altSign (2 + i.val) * skewOnesMat (2 * (m + 1)) ⟨2 + i.val, by omega⟩ j) =
                sumFin (fun i : Fin (2 * m) => altSign i.val * skewOnesMat (2 * m) i ⟨j.val - 2, by omega⟩) := by
        apply sumFin_congr; intro i
        rw [altSign_add, altSign_two_mul 1, Int.one_mul]
        unfold skewOnesMat sgnInt
        have hiff1 : 2 + i.val < j.val ↔ i.val < j.val - 2 := by omega
        have hiff2 : j.val < 2 + i.val ↔ j.val - 2 < i.val := by omega
        simp [hiff1, hiff2]
      change sumFin (fun i : Fin 2 => altSign i.val * skewOnesMat (2 * (m + 1)) ⟨i.val, by omega⟩ j) +
             sumFin (fun i : Fin (2 * m) => altSign (2 + i.val) * skewOnesMat (2 * (m + 1)) ⟨2 + i.val, by omega⟩ j) = 1
      rw [h1, h2, sumFin_altSign_skewOnes m ⟨j.val - 2, by omega⟩]; rfl

theorem carries_add_pow2_right (k x z : Nat) (hx : x < 2 ^ k) (hz : z < 2 ^ k) :
    carries x (2 ^ k + z) = carries x z + if 2 ^ k ≤ x + z then 1 else 0 := by
  unfold carries
  rw [popcount_add_pow2 k z hz]
  by_cases hle : 2 ^ k ≤ x + z
  · simp only [hle, ↓reduceIte]
    have hsplit1 : x + z = 1 * 2 ^ k + (x + z - 2 ^ k) := by omega
    have hsplit2 : x + (2 ^ k + z) = 2 * 2 ^ k + (x + z - 2 ^ k) := by omega
    have hr : x + z - 2 ^ k < 2 ^ k := by omega
    have hpop1 : popcount (x + z) = 1 + popcount (x + z - 2 ^ k) := by
      have h := popcount_add_pow2_mul k 1 (x + z - 2 ^ k) hr
      have hp1 : popcount 1 = 1 := by decide
      rw [← hsplit1, hp1] at h; exact h
    have hpop2 : popcount (x + (2 ^ k + z)) = 1 + popcount (x + z - 2 ^ k) := by
      have h := popcount_add_pow2_mul k 2 (x + z - 2 ^ k) hr
      have hp2 : popcount 2 = 1 := by decide
      rw [← hsplit2, hp2] at h; exact h
    rw [hpop1, hpop2]; omega
  · simp only [hle, ↓reduceIte]
    have hlt : x + z < 2 ^ k := by omega
    have hre : x + (2 ^ k + z) = 2 ^ k + (x + z) := by omega
    rw [hre, popcount_add_pow2 k (x + z) hlt]; omega

theorem carries_add_pow2_both (k x z : Nat) (hx : x < 2 ^ k) (hz : z < 2 ^ k) :
    carries (2 ^ k + x) (2 ^ k + z) = 1 + carries x z := by
  unfold carries
  rw [popcount_add_pow2 k x hx, popcount_add_pow2 k z hz]
  by_cases hle : 2 ^ k ≤ x + z
  · have hsplit1 : x + z = 1 * 2 ^ k + (x + z - 2 ^ k) := by omega
    have hsplit2 : (2 ^ k + x) + (2 ^ k + z) = 3 * 2 ^ k + (x + z - 2 ^ k) := by omega
    have hr : x + z - 2 ^ k < 2 ^ k := by omega
    have hpop1 : popcount (x + z) = 1 + popcount (x + z - 2 ^ k) := by
      have h := popcount_add_pow2_mul k 1 (x + z - 2 ^ k) hr
      have hp1 : popcount 1 = 1 := by decide
      rw [← hsplit1, hp1] at h; exact h
    have hpop2 : popcount ((2 ^ k + x) + (2 ^ k + z)) = 2 + popcount (x + z - 2 ^ k) := by
      have h := popcount_add_pow2_mul k 3 (x + z - 2 ^ k) hr
      have hp3 : popcount 3 = 2 := by decide
      rw [← hsplit2, hp3] at h; exact h
    rw [hpop1, hpop2]; omega
  · have hlt : x + z < 2 ^ k := by omega
    have hsplit2 : (2 ^ k + x) + (2 ^ k + z) = 2 * 2 ^ k + (x + z) := by omega
    rw [hsplit2, popcount_add_pow2_mul k 2 _ hlt]
    have hp2 : popcount 2 = 1 := by decide
    rw [hp2]; omega

theorem carryAsym_block (k : Nat) :
    carryAsymMat (k + 1) =
    castMat (show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by rw [pow2_eq_add])
      (blockMat
        (fun i j => carryAsymMat k i j - skewOnesMat (2 ^ k) i j)
        (fun i j => carryAsymMat k i j - 1)
        (fun i j => carryAsymMat k i j + 1)
        (fun i j => carryAsymMat k i j - skewOnesMat (2 ^ k) i j)) := by
  funext i j
  unfold castMat blockMat carryAsymMat skewOnesMat sgnInt
  have h1 : (2 ^ (k + 1) - 1) ^^^ j.val = 2 ^ (k + 1) - 1 - j.val := bitCompl_eq_sub (k + 1) j.val j.isLt
  have h2 : (2 ^ (k + 1) - 1) ^^^ i.val = 2 ^ (k + 1) - 1 - i.val := bitCompl_eq_sub (k + 1) i.val i.isLt
  rw [h1, h2]
  have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := pow2_eq_add k
  by_cases hi : i.val < 2 ^ k <;> by_cases hj : j.val < 2 ^ k
  · simp only [hi, hj, ↓reduceDIte]
    rw [bitCompl_eq_sub k j.val hj, bitCompl_eq_sub k i.val hi]
    have hc1 : 2 ^ (k + 1) - 1 - j.val = 2 ^ k + (2 ^ k - 1 - j.val) := by omega
    have hc2 : 2 ^ (k + 1) - 1 - i.val = 2 ^ k + (2 ^ k - 1 - i.val) := by omega
    rw [hc1, hc2,
        carries_add_pow2_right k i.val (2 ^ k - 1 - j.val) hi (by omega),
        carries_add_pow2_right k j.val (2 ^ k - 1 - i.val) hj (by omega)]
    by_cases hlt : i.val < j.val
    · have h1' : ¬ (2 ^ k ≤ i.val + (2 ^ k - 1 - j.val)) := by omega
      have h2' : 2 ^ k ≤ j.val + (2 ^ k - 1 - i.val) := by omega
      simp [hlt, h1', h2']; omega
    · by_cases hgt : j.val < i.val
      · have h1' : 2 ^ k ≤ i.val + (2 ^ k - 1 - j.val) := by omega
        have h2' : ¬ (2 ^ k ≤ j.val + (2 ^ k - 1 - i.val)) := by omega
        simp [hlt, hgt, h1', h2']; omega
      · have heq : i.val = j.val := by omega
        have h1' : ¬ (2 ^ k ≤ i.val + (2 ^ k - 1 - j.val)) := by omega
        have h2' : ¬ (2 ^ k ≤ j.val + (2 ^ k - 1 - i.val)) := by omega
        simp [hlt, hgt, h1', h2']
  · simp only [hi, hj, ↓reduceDIte]
    have hj' : j.val - 2 ^ k < 2 ^ k := by omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    rw [bitCompl_eq_sub k (j.val - 2 ^ k) hj', bitCompl_eq_sub k i.val hi]
    have hc1 : 2 ^ (k + 1) - 1 - j.val = 2 ^ k - 1 - (j.val - 2 ^ k) := by omega
    have hc2 : 2 ^ (k + 1) - 1 - i.val = 2 ^ k + (2 ^ k - 1 - i.val) := by omega
    have hj_eq : j.val = 2 ^ k + (j.val - 2 ^ k) := by omega
    have hcb : carries j.val (2 ^ k + (2 ^ k - 1 - i.val)) = 1 + carries (j.val - 2 ^ k) (2 ^ k - 1 - i.val) := by
      have h := carries_add_pow2_both k (j.val - 2 ^ k) (2 ^ k - 1 - i.val) hj' (by omega)
      rw [← hj_eq] at h; exact h
    rw [hc1, hc2, hcb]; omega
  · simp only [hi, hj, ↓reduceDIte]
    have hi' : i.val - 2 ^ k < 2 ^ k := by omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    rw [bitCompl_eq_sub k j.val hj, bitCompl_eq_sub k (i.val - 2 ^ k) hi']
    have hc1 : 2 ^ (k + 1) - 1 - j.val = 2 ^ k + (2 ^ k - 1 - j.val) := by omega
    have hc2 : 2 ^ (k + 1) - 1 - i.val = 2 ^ k - 1 - (i.val - 2 ^ k) := by omega
    have hi_eq : i.val = 2 ^ k + (i.val - 2 ^ k) := by omega
    have hcb : carries i.val (2 ^ k + (2 ^ k - 1 - j.val)) = 1 + carries (i.val - 2 ^ k) (2 ^ k - 1 - j.val) := by
      have h := carries_add_pow2_both k (i.val - 2 ^ k) (2 ^ k - 1 - j.val) hi' (by omega)
      rw [← hi_eq] at h; exact h
    rw [hc1, hc2, hcb]; omega
  · simp only [hi, hj, ↓reduceDIte]
    have hi' : i.val - 2 ^ k < 2 ^ k := by omega
    have hj' : j.val - 2 ^ k < 2 ^ k := by omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    rw [bitCompl_eq_sub k (j.val - 2 ^ k) hj', bitCompl_eq_sub k (i.val - 2 ^ k) hi']
    have hc1 : 2 ^ (k + 1) - 1 - j.val = 2 ^ k - 1 - (j.val - 2 ^ k) := by omega
    have hc2 : 2 ^ (k + 1) - 1 - i.val = 2 ^ k - 1 - (i.val - 2 ^ k) := by omega
    have hi_eq : i.val = 2 ^ k + (i.val - 2 ^ k) := by omega
    have hj_eq : j.val = 2 ^ k + (j.val - 2 ^ k) := by omega
    have hcomm : ∀ u v, carries u v = carries v u := fun u v => by unfold carries; rw [Nat.add_comm u v]; omega
    rw [hc1, hc2]
    have hcar1 : carries i.val (2 ^ k - 1 - (j.val - 2 ^ k)) =
                 carries (i.val - 2 ^ k) (2 ^ k - 1 - (j.val - 2 ^ k)) +
                 if 2 ^ k ≤ (i.val - 2 ^ k) + (2 ^ k - 1 - (j.val - 2 ^ k)) then 1 else 0 := by
      have h := carries_add_pow2_right k (2 ^ k - 1 - (j.val - 2 ^ k)) (i.val - 2 ^ k) (by omega) hi'
      rw [hcomm, ← hi_eq] at h
      rw [h, hcomm, Nat.add_comm (2 ^ k - 1 - (j.val - 2 ^ k))]
    have hcar2 : carries j.val (2 ^ k - 1 - (i.val - 2 ^ k)) =
                 carries (j.val - 2 ^ k) (2 ^ k - 1 - (i.val - 2 ^ k)) +
                 if 2 ^ k ≤ (j.val - 2 ^ k) + (2 ^ k - 1 - (i.val - 2 ^ k)) then 1 else 0 := by
      have h := carries_add_pow2_right k (2 ^ k - 1 - (i.val - 2 ^ k)) (j.val - 2 ^ k) (by omega) hj'
      rw [hcomm, ← hj_eq] at h
      rw [h, hcomm, Nat.add_comm (2 ^ k - 1 - (i.val - 2 ^ k))]
    rw [hcar1, hcar2]
    by_cases hlt : i.val - 2 ^ k < j.val - 2 ^ k
    · have h1' : ¬ (2 ^ k ≤ (i.val - 2 ^ k) + (2 ^ k - 1 - (j.val - 2 ^ k))) := by omega
      have h2' : 2 ^ k ≤ (j.val - 2 ^ k) + (2 ^ k - 1 - (i.val - 2 ^ k)) := by omega
      simp [hlt, h1', h2']; omega
    · by_cases hgt : j.val - 2 ^ k < i.val - 2 ^ k
      · have h1' : 2 ^ k ≤ (i.val - 2 ^ k) + (2 ^ k - 1 - (j.val - 2 ^ k)) := by omega
        have h2' : ¬ (2 ^ k ≤ (j.val - 2 ^ k) + (2 ^ k - 1 - (i.val - 2 ^ k))) := by omega
        simp [hlt, hgt, h1', h2']; omega
      · have h1' : ¬ (2 ^ k ≤ (i.val - 2 ^ k) + (2 ^ k - 1 - (j.val - 2 ^ k))) := by omega
        have h2' : ¬ (2 ^ k ≤ (j.val - 2 ^ k) + (2 ^ k - 1 - (i.val - 2 ^ k))) := by omega
        simp [hlt, hgt, h1', h2']

/-- Explicit closed-form Mersenne-root product for `Pf(a C_k + b S_{2^k})` (`k ≥ 1`). -/
def carryPencilClosed (k : Nat) (a b : Int) : Int :=
  (b - ((2 : Int) ^ k - 1) * a) *
  prodFin (fun j : Fin (k - 1) => (b - ((2 : Int) ^ (j.val + 1) - 1) * a) ^ (2 ^ (k - 2 - j.val)))

def grayHadMat (k : Nat) : Mat (2 ^ k) :=
  fun i j => paritySign (gray i.val &&& gray j.val)

def grayDiag (k : Nat) (i : Fin (2 ^ k)) : Int :=
  if i.val.testBit (k - 1) then -1 else 1

def grayWalshWeightedMat (k : Nat) (b : Nat → Int) : Mat (2 ^ k) :=
  fun i j =>
    if i = j then 0
    else b (msb (i.val ^^^ j.val)) * sgnInt i.val j.val * paritySign (gray i.val &&& gray j.val)

def grayWalshMat (n : Nat) : Mat n :=
  fun i j => sgnInt i.val j.val * paritySign (gray i.val &&& gray j.val)

def grayMu (b : Nat → Int) : Nat → Int
  | 0 => 0
  | 1 => b 0 * b 0
  | k + 2 => grayMu b (k + 1) + (2 : Int) ^ (k + 1) * (b (k + 1) * b (k + 1))

theorem grayDiag_sq (k : Nat) (i : Fin (2 ^ k)) : grayDiag k i * grayDiag k i = 1 := by
  unfold grayDiag; split <;> decide

theorem grayHad_symm (k : Nat) (i j : Fin (2 ^ k)) : grayHadMat k i j = grayHadMat k j i := by
  unfold grayHadMat; rw [Nat.and_comm]

theorem isSkew_grayWalshWeighted (k : Nat) (b : Nat → Int) : IsSkew (grayWalshWeightedMat k b) := by
  constructor
  · intro i; unfold grayWalshWeightedMat; simp
  · intro i j; unfold grayWalshWeightedMat
    by_cases h : i = j
    · subst h; simp
    · have hne : j ≠ i := Ne.symm h
      simp only [h, hne, ↓reduceIte]
      rw [Nat.xor_comm i.val j.val, Nat.and_comm (gray i.val) (gray j.val)]
      unfold sgnInt
      by_cases h1 : i.val < j.val
      · have h2 : ¬ (j.val < i.val) := by omega
        simp [h1, h2, Int.neg_mul]
      · have h2 : j.val < i.val := by have : i.val ≠ j.val := fun e => h (Fin.ext e); omega
        simp [h1, h2, Int.neg_mul]

theorem isSkew_grayWalsh (n : Nat) : IsSkew (grayWalshMat n) := by
  constructor
  · intro i; unfold grayWalshMat sgnInt; simp
  · intro i j; unfold grayWalshMat
    rw [Nat.and_comm (gray i.val) (gray j.val)]
    unfold sgnInt
    by_cases h1 : i.val < j.val
    · have h2 : ¬ (j.val < i.val) := by omega
      simp [h1, h2]
    · by_cases h2 : j.val < i.val
      · simp [h1, h2]
      · simp [h1, h2]

theorem grayWalshMat_eq_weighted (k : Nat) :
    grayWalshMat (2 ^ k) = grayWalshWeightedMat k (fun _ => 1) := by
  funext i j; unfold grayWalshMat grayWalshWeightedMat
  by_cases h : i = j
  · subst h; unfold sgnInt; simp
  · simp [h]

theorem grayMu_ones : ∀ k : Nat, 1 ≤ k → grayMu (fun _ => 1) k = (2 : Int) ^ k - 1
  | 0, hk => by omega
  | 1, _ => by decide
  | k + 2, _ => by
    unfold grayMu
    rw [grayMu_ones (k + 1) (by omega)]
    have hpow : (2 : Int) ^ (k + 2) = (2 : Int) ^ (k + 1) * 2 := Int.pow_succ (2 : Int) (k + 1)
    rw [hpow]; simp only [Int.mul_one]; omega

theorem grayMu_pos (b : Nat → Int) (hb0 : b 0 ≠ 0) : ∀ k : Nat, 1 ≤ k → 0 < grayMu b k
  | 0, hk => by omega
  | 1, _ => by
    unfold grayMu
    have : 0 < b 0 * b 0 := by
      by_cases h : 0 < b 0
      · exact Int.mul_pos h h
      · have hneg : b 0 < 0 := by omega
        have h1 : 0 < -b 0 := by omega
        have h2 := Int.mul_pos h1 h1
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at h2; exact h2
    exact this
  | k + 2, _ => by
    unfold grayMu
    have hih := grayMu_pos b hb0 (k + 1) (by omega)
    have hsq : 0 ≤ b (k + 1) * b (k + 1) := by
      by_cases h : 0 ≤ b (k + 1)
      · exact Int.mul_nonneg h h
      · have h1 : 0 ≤ -b (k + 1) := by omega
        have h2 := Int.mul_nonneg h1 h1
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at h2; exact h2
    have hp : (0 : Int) ≤ (2 : Int) ^ (k + 1) := by
      have : ∀ n : Nat, (0 : Int) ≤ (2 : Int) ^ n := by
        intro n; induction n with
        | zero => decide
        | succ t it => rw [Int.pow_succ]; omega
      exact this (k + 1)
    have hterm := Int.mul_nonneg hp hsq
    omega

theorem testBit_gray_top (k x : Nat) (hk : 1 ≤ k) (hx : x < 2 ^ k) :
    (gray x).testBit (k - 1) = x.testBit (k - 1) := by
  unfold gray; rw [Nat.testBit_xor, Nat.testBit_shiftRight]
  have hf := testBit_lt_pow2 k x hx (1 + (k - 1)) (by omega)
  rw [hf, Bool.xor_false]

theorem paritySign_gray_add_pow2_right (k x y : Nat) (hk : 1 ≤ k) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    paritySign (gray x &&& gray (2 ^ k + y)) =
    grayDiag k ⟨x, hx⟩ * paritySign (gray x &&& gray y) := by
  rw [gray_add_pow2 k y hk hy]
  have hglt : 2 ^ (k - 1) ^^^ gray y < 2 ^ k := by
    apply lt_pow2_of_testBit; intro i hi
    rw [Nat.testBit_xor, Nat.testBit_two_pow, testBit_lt_pow2 k (gray y) (gray_lt_pow2 k y hy) i hi]
    have hne : k - 1 ≠ i := by omega
    simp [hne]
  rw [Nat.and_comm, and_add_pow2_left k _ _ hglt (gray_lt_pow2 k x hx), Nat.and_comm]
  rw [paritySign_and_xor_pow2 (k - 1) (gray x) (gray y), testBit_gray_top k x hk hx]
  rfl

theorem paritySign_gray_add_pow2_both (k x y : Nat) (hk : 1 ≤ k) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    paritySign (gray (2 ^ k + x) &&& gray (2 ^ k + y)) =
    grayDiag k ⟨x, hx⟩ * grayDiag k ⟨y, hy⟩ * paritySign (gray x &&& gray y) := by
  rw [gray_add_pow2 k x hk hx, gray_add_pow2 k y hk hy]
  have hlt1 : 2 ^ (k - 1) ^^^ gray x < 2 ^ k := by
    apply lt_pow2_of_testBit; intro i hi
    rw [Nat.testBit_xor, Nat.testBit_two_pow, testBit_lt_pow2 k (gray x) (gray_lt_pow2 k x hx) i hi]
    have hne : k - 1 ≠ i := by omega
    simp [hne]
  have hlt2 : 2 ^ (k - 1) ^^^ gray y < 2 ^ k := by
    apply lt_pow2_of_testBit; intro i hi
    rw [Nat.testBit_xor, Nat.testBit_two_pow, testBit_lt_pow2 k (gray y) (gray_lt_pow2 k y hy) i hi]
    have hne : k - 1 ≠ i := by omega
    simp [hne]
  rw [and_add_pow2_both k _ _ hlt1 hlt2]
  have hand_lt : ((2 ^ (k - 1) ^^^ gray x) &&& (2 ^ (k - 1) ^^^ gray y)) < 2 ^ k := by
    apply lt_pow2_of_testBit; intro i hi
    rw [Nat.testBit_and, testBit_lt_pow2 k _ hlt1 i hi]; rfl
  rw [paritySign_add_pow2 k _ hand_lt]
  rw [paritySign_and_xor_pow2 (k - 1) (2 ^ (k - 1) ^^^ gray x) (gray y)]
  rw [Nat.and_comm, paritySign_and_xor_pow2 (k - 1) (gray y) (gray x), Nat.and_comm]
  rw [Nat.testBit_xor, Nat.testBit_two_pow, testBit_gray_top k x hk hx, testBit_gray_top k y hk hy]
  unfold grayDiag
  cases x.testBit (k - 1) <;> cases y.testBit (k - 1) <;> simp

theorem grayHad_block (k : Nat) (hk : 1 ≤ k) :
    grayHadMat (k + 1) =
    castMat (show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by rw [pow2_eq_add])
      (blockMat
        (grayHadMat k)
        (fun i j => grayDiag k i * grayHadMat k i j)
        (fun i j => grayDiag k j * grayHadMat k i j)
        (fun i j => grayDiag k i * grayDiag k j * grayHadMat k i j)) := by
  funext i j; unfold castMat blockMat grayHadMat
  have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := pow2_eq_add k
  by_cases hi : i.val < 2 ^ k <;> by_cases hj : j.val < 2 ^ k
  · simp [hi, hj]
  · simp only [hi, hj, ↓reduceDIte]
    have hj_eq : j.val = 2 ^ k + (j.val - 2 ^ k) := by omega
    conv => lhs; rw [hj_eq]
    exact paritySign_gray_add_pow2_right k i.val (j.val - 2 ^ k) hk hi (by omega)
  · simp only [hi, hj, ↓reduceDIte]
    have hi_eq : i.val = 2 ^ k + (i.val - 2 ^ k) := by omega
    rw [Nat.and_comm]; conv => lhs; rw [hi_eq]
    rw [paritySign_gray_add_pow2_right k j.val (i.val - 2 ^ k) hk hj (by omega), Nat.and_comm]
  · simp only [hi, hj, ↓reduceDIte]
    have hi_eq : i.val = 2 ^ k + (i.val - 2 ^ k) := by omega
    have hj_eq : j.val = 2 ^ k + (j.val - 2 ^ k) := by omega
    conv => lhs; rw [hi_eq, hj_eq]
    exact paritySign_gray_add_pow2_both k (i.val - 2 ^ k) (j.val - 2 ^ k) hk (by omega) (by omega)

theorem grayWalshWeighted_block (k : Nat) (hk : 1 ≤ k) (b : Nat → Int) :
    grayWalshWeightedMat (k + 1) b =
    castMat (show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by rw [pow2_eq_add])
      (blockMat
        (grayWalshWeightedMat k b)
        (fun i j => b k * (grayDiag k i * grayHadMat k i j))
        (fun i j => -(b k * (grayDiag k j * grayHadMat k j i)))
        (diagCong (grayDiag k) (grayWalshWeightedMat k b))) := by
  funext i j; unfold castMat blockMat grayWalshWeightedMat grayHadMat diagCong
  have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := pow2_eq_add k
  by_cases hi : i.val < 2 ^ k <;> by_cases hj : j.val < 2 ^ k
  · simp only [hi, hj, ↓reduceDIte]
    have hiff : i = j ↔ (⟨i.val, hi⟩ : Fin (2 ^ k)) = ⟨j.val, hj⟩ := by simp only [Fin.ext_iff]
    simp [hiff]
  · simp only [hi, hj, ↓reduceDIte]
    have hne : i ≠ j := fin_ne_of_val (by omega)
    have hlt : i.val < j.val := by omega
    have hj_eq : j.val = 2 ^ k + (j.val - 2 ^ k) := by omega
    simp only [hne, ↓reduceIte]
    have hms : msb (i.val ^^^ j.val) = k := by
      rw [hj_eq]; exact msb_xor_add_pow2_right k i.val (j.val - 2 ^ k) hi (by omega)
    have hsg : sgnInt i.val j.val = 1 := by unfold sgnInt; simp [hlt]
    rw [hms, hsg, Int.mul_one]
    conv => lhs; rw [hj_eq]
    rw [paritySign_gray_add_pow2_right k i.val (j.val - 2 ^ k) hk hi (by omega)]
  · simp only [hi, hj, ↓reduceDIte]
    have hne : i ≠ j := fin_ne_of_val (by omega)
    have hgt : j.val < i.val := by omega
    have hnl : ¬ (i.val < j.val) := by omega
    have hi_eq : i.val = 2 ^ k + (i.val - 2 ^ k) := by omega
    simp only [hne, ↓reduceIte]
    have hms : msb (i.val ^^^ j.val) = k := by
      rw [Nat.xor_comm, hi_eq]; exact msb_xor_add_pow2_right k j.val (i.val - 2 ^ k) hj (by omega)
    have hsg : sgnInt i.val j.val = -1 := by unfold sgnInt; simp [hgt, hnl]
    rw [hms, hsg, Nat.and_comm]
    conv => lhs; rw [hi_eq]
    rw [paritySign_gray_add_pow2_right k j.val (i.val - 2 ^ k) hk hj (by omega)]
    rw [Int.mul_neg, Int.mul_one, Int.neg_mul]
  · simp only [hi, hj, ↓reduceDIte]
    have hiff : i = j ↔ (⟨i.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = ⟨j.val - 2 ^ k, by omega⟩ := by
      simp only [Fin.ext_iff]; omega
    by_cases hij : i = j
    · simp [hij]
    · have hij' : (⟨i.val - 2 ^ k, by omega⟩ : Fin (2 ^ k)) ≠ ⟨j.val - 2 ^ k, by omega⟩ := fun h => hij (hiff.mpr h)
      simp only [hij, hij', ↓reduceIte]
      have hi' : i.val - 2 ^ k < 2 ^ k := by omega
      have hj' : j.val - 2 ^ k < 2 ^ k := by omega
      have hi_eq : i.val = 2 ^ k + (i.val - 2 ^ k) := by omega
      have hj_eq : j.val = 2 ^ k + (j.val - 2 ^ k) := by omega
      have hxor : i.val ^^^ j.val = (i.val - 2 ^ k) ^^^ (j.val - 2 ^ k) := by
        have h := xor_add_pow2_both k (i.val - 2 ^ k) (j.val - 2 ^ k) hi' hj'
        rw [← hi_eq, ← hj_eq] at h; exact h
      have hsg : sgnInt i.val j.val = sgnInt (i.val - 2 ^ k) (j.val - 2 ^ k) := by
        unfold sgnInt
        have h1 : i.val < j.val ↔ i.val - 2 ^ k < j.val - 2 ^ k := by omega
        have h2 : j.val < i.val ↔ j.val - 2 ^ k < i.val - 2 ^ k := by omega
        simp [h1, h2]
      have hps : paritySign (gray i.val &&& gray j.val) =
                 grayDiag k ⟨i.val - 2 ^ k, hi'⟩ * grayDiag k ⟨j.val - 2 ^ k, hj'⟩ *
                 paritySign (gray (i.val - 2 ^ k) &&& gray (j.val - 2 ^ k)) := by
        have h := paritySign_gray_add_pow2_both k (i.val - 2 ^ k) (j.val - 2 ^ k) hk hi' hj'
        rw [← hi_eq, ← hj_eq] at h; exact h
      rw [hxor, hsg, hps]; ac_rfl

theorem grayDiag_succ (k : Nat) (i : Fin (2 ^ (k + 1))) :
    grayDiag (k + 1) i = if i.val < 2 ^ k then 1 else -1 := by
  unfold grayDiag
  have hk : k + 1 - 1 = k := by omega
  rw [hk]
  by_cases hi : i.val < 2 ^ k
  · rw [testBit_lt_pow2 k i.val hi k (Nat.le_refl k)]; simp [hi]
  · have hi_eq : i.val = 2 ^ k + (i.val - 2 ^ k) := by omega
    have hr : i.val - 2 ^ k < 2 ^ k := by have := pow2_eq_add k; omega
    rw [hi_eq, testBit_add_pow2 k _ hr k]; simp

theorem sumFin_pow2_split (k : Nat) (f : Fin (2 ^ (k + 1)) → Int) :
    sumFin f = sumFin (fun i : Fin (2 ^ k) => f ⟨i.val, by have := pow2_eq_add k; omega⟩) +
               sumFin (fun j : Fin (2 ^ k) => f ⟨2 ^ k + j.val, by have := pow2_eq_add k; omega⟩) := by
  rw [← sumFin_cast (show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by rw [pow2_eq_add]), sumFin_split]

/-- Simultaneous induction: `H_k^2 = 2^k I` AND `H_k D_k H_k + D_k H_k D_k H_k D_k = 0`. -/
theorem grayHad_algebra : ∀ (k : Nat), 1 ≤ k →
    (∀ i j : Fin (2 ^ k), matMul (grayHadMat k) (grayHadMat k) i j = if i = j then (2 : Int) ^ k else 0) ∧
    (∀ i j : Fin (2 ^ k),
      sumFin (fun t : Fin (2 ^ k) => grayHadMat k i t * grayDiag k t * grayHadMat k t j) +
      grayDiag k i * grayDiag k j *
        sumFin (fun t : Fin (2 ^ k) => grayHadMat k i t * grayDiag k t * grayHadMat k t j) = 0)
  | 0, hk => by omega
  | 1, _ => by
    constructor
    · intro i j
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      have hj : j.val = 0 ∨ j.val = 1 := by omega
      rcases hi with h1 | h1 <;> rcases hj with h2 | h2
      · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars
        unfold matMul; simp only [sumFin_succ, sumFin_zero, Int.add_zero]; decide
      · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars
        unfold matMul; simp only [sumFin_succ, sumFin_zero, Int.add_zero]; decide
      · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars
        unfold matMul; simp only [sumFin_succ, sumFin_zero, Int.add_zero]; decide
      · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars
        unfold matMul; simp only [sumFin_succ, sumFin_zero, Int.add_zero]; decide
    · intro i j
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      have hj : j.val = 0 ∨ j.val = 1 := by omega
      rcases hi with h1 | h1 <;> rcases hj with h2 | h2
      · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars
        simp only [sumFin_succ, sumFin_zero, Int.add_zero]; decide
      · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars
        simp only [sumFin_succ, sumFin_zero, Int.add_zero]; decide
      · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars
        simp only [sumFin_succ, sumFin_zero, Int.add_zero]; decide
      · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars
        simp only [sumFin_succ, sumFin_zero, Int.add_zero]; decide
  | k + 2, _ => by
    have hk1 : 1 ≤ k + 1 := by omega
    rcases grayHad_algebra (k + 1) hk1 with ⟨ihSq, ihAnti⟩
    let H := grayHadMat (k + 1)
    let D := grayDiag (k + 1)
    have hDsq : ∀ u : Fin (2 ^ (k + 1)), D u * D u = 1 := grayDiag_sq (k + 1)
    have hHsymm : ∀ u v : Fin (2 ^ (k + 1)), H u v = H v u := grayHad_symm (k + 1)
    have hp : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := pow2_eq_add (k + 1)
    have hH_quad : ∀ i j : Fin (2 ^ (k + 2)), grayHadMat (k + 2) i j =
        if hi : i.val < 2 ^ (k + 1) then
          if hj : j.val < 2 ^ (k + 1) then H ⟨i.val, hi⟩ ⟨j.val, hj⟩
          else D ⟨i.val, hi⟩ * H ⟨i.val, hi⟩ ⟨j.val - 2 ^ (k + 1), by omega⟩
        else
          if hj : j.val < 2 ^ (k + 1) then D ⟨j.val, hj⟩ * H ⟨i.val - 2 ^ (k + 1), by omega⟩ ⟨j.val, hj⟩
          else D ⟨i.val - 2 ^ (k + 1), by omega⟩ *
               D ⟨j.val - 2 ^ (k + 1), by omega⟩ *
               H ⟨i.val - 2 ^ (k + 1), by omega⟩ ⟨j.val - 2 ^ (k + 1), by omega⟩ := by
      intro i j; rw [grayHad_block (k + 1) hk1]; unfold castMat blockMat
      by_cases hi : i.val < 2 ^ (k + 1) <;> by_cases hj : j.val < 2 ^ (k + 1) <;> simp [hi, hj, H, D]
    constructor
    · -- Part 1: (H_{k+2})^2 = 2^{k+2} I
      intro i j; unfold matMul; rw [sumFin_pow2_split (k + 1)]
      by_cases hi : i.val < 2 ^ (k + 1) <;> by_cases hj : j.val < 2 ^ (k + 1)
      · let i' : Fin (2 ^ (k + 1)) := ⟨i.val, hi⟩; let j' : Fin (2 ^ (k + 1)) := ⟨j.val, hj⟩
        have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨t.val, by omega⟩ * grayHadMat (k + 2) ⟨t.val, by omega⟩ j) =
                  matMul H H i' j' := by
          unfold matMul; apply sumFin_congr; intro t
          rw [hH_quad i ⟨t.val, by omega⟩, hH_quad ⟨t.val, by omega⟩ j]; simp [hi, hj, t.isLt]; rfl
        have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayHadMat (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ j) =
                  D i' * D j' * matMul H H i' j' := by
          unfold matMul; rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          rw [hH_quad i ⟨2 ^ (k + 1) + t.val, by omega⟩, hH_quad ⟨2 ^ (k + 1) + t.val, by omega⟩ j]
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          simp only [hi, hj, hnt, ↓reduceDIte]
          have ht' : (⟨2 ^ (k + 1) + t.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = t := Fin.ext (by dsimp; omega)
          rw [ht']; dsimp only [i', j']; ac_rfl
        rw [h1, h2, ihSq i' j']
        by_cases hij : i = j
        · have hij' : i' = j' := Fin.ext (by dsimp [i', j']; exact congrArg Fin.val hij)
          have hpow : (2 : Int) ^ (k + 2) = (2 : Int) ^ (k + 1) * 2 := Int.pow_succ (2 : Int) (k + 1)
          simp only [hij, hij', ↓reduceIte, hDsq, Int.one_mul, hpow]; omega
        · have hij' : i' ≠ j' := fun h => hij (Fin.ext (by have := congrArg Fin.val h; dsimp [i', j'] at this; exact this))
          simp [hij, hij']
      · let i' : Fin (2 ^ (k + 1)) := ⟨i.val, hi⟩; let j' : Fin (2 ^ (k + 1)) := ⟨j.val - 2 ^ (k + 1), by omega⟩
        have hne : i ≠ j := fin_ne_of_val (by omega)
        simp only [hne, ↓reduceIte]
        have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨t.val, by omega⟩ * grayHadMat (k + 2) ⟨t.val, by omega⟩ j) =
                  sumFin (fun t : Fin (2 ^ (k + 1)) => H i' t * D t * H t j') := by
          apply sumFin_congr; intro t
          rw [hH_quad i ⟨t.val, by omega⟩, hH_quad ⟨t.val, by omega⟩ j]
          simp only [hi, hj, t.isLt, ↓reduceDIte]; dsimp only [i', j']; ac_rfl
        have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayHadMat (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ j) =
                  D i' * D j' * sumFin (fun t : Fin (2 ^ (k + 1)) => H i' t * D t * H t j') := by
          rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          rw [hH_quad i ⟨2 ^ (k + 1) + t.val, by omega⟩, hH_quad ⟨2 ^ (k + 1) + t.val, by omega⟩ j]
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          simp only [hi, hj, hnt, ↓reduceDIte]
          have ht' : (⟨2 ^ (k + 1) + t.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = t := Fin.ext (by dsimp; omega)
          rw [ht']; dsimp only [i', j']; ac_rfl
        rw [h1, h2]; exact ihAnti i' j'
      · let i' : Fin (2 ^ (k + 1)) := ⟨i.val - 2 ^ (k + 1), by omega⟩; let j' : Fin (2 ^ (k + 1)) := ⟨j.val, hj⟩
        have hne : i ≠ j := fin_ne_of_val (by omega)
        simp only [hne, ↓reduceIte]
        have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨t.val, by omega⟩ * grayHadMat (k + 2) ⟨t.val, by omega⟩ j) =
                  sumFin (fun t : Fin (2 ^ (k + 1)) => H j' t * D t * H t i') := by
          apply sumFin_congr; intro t
          rw [hH_quad i ⟨t.val, by omega⟩, hH_quad ⟨t.val, by omega⟩ j]
          simp only [hi, hj, t.isLt, ↓reduceDIte]
          dsimp only [i', j']; rw [hHsymm ⟨i.val - 2 ^ (k + 1), by omega⟩ t, hHsymm t ⟨j.val, hj⟩]; ac_rfl
        have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayHadMat (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ j) =
                  D j' * D i' * sumFin (fun t : Fin (2 ^ (k + 1)) => H j' t * D t * H t i') := by
          rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          rw [hH_quad i ⟨2 ^ (k + 1) + t.val, by omega⟩, hH_quad ⟨2 ^ (k + 1) + t.val, by omega⟩ j]
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          simp only [hi, hj, hnt, ↓reduceDIte]
          have ht' : (⟨2 ^ (k + 1) + t.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = t := Fin.ext (by dsimp; omega)
          rw [ht']; dsimp only [i', j']; rw [hHsymm ⟨i.val - 2 ^ (k + 1), by omega⟩ t, hHsymm t ⟨j.val, hj⟩]; ac_rfl
        rw [h1, h2]; exact ihAnti j' i'
      · let i' : Fin (2 ^ (k + 1)) := ⟨i.val - 2 ^ (k + 1), by omega⟩; let j' : Fin (2 ^ (k + 1)) := ⟨j.val - 2 ^ (k + 1), by omega⟩
        have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨t.val, by omega⟩ * grayHadMat (k + 2) ⟨t.val, by omega⟩ j) =
                  matMul H H i' j' := by
          unfold matMul; apply sumFin_congr; intro t
          rw [hH_quad i ⟨t.val, by omega⟩, hH_quad ⟨t.val, by omega⟩ j]
          simp only [hi, hj, t.isLt, ↓reduceDIte]
          dsimp only [i', j']
          calc D t * H ⟨i.val - 2 ^ (k + 1), by omega⟩ t * (D t * H t ⟨j.val - 2 ^ (k + 1), by omega⟩) =
                (D t * D t) * (H ⟨i.val - 2 ^ (k + 1), by omega⟩ t * H t ⟨j.val - 2 ^ (k + 1), by omega⟩) := by ac_rfl
            _ = H ⟨i.val - 2 ^ (k + 1), by omega⟩ t * H t ⟨j.val - 2 ^ (k + 1), by omega⟩ := by rw [hDsq, Int.one_mul]
        have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayHadMat (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ j) =
                  D i' * D j' * matMul H H i' j' := by
          unfold matMul; rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          rw [hH_quad i ⟨2 ^ (k + 1) + t.val, by omega⟩, hH_quad ⟨2 ^ (k + 1) + t.val, by omega⟩ j]
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          simp only [hi, hj, hnt, ↓reduceDIte]
          have ht' : (⟨2 ^ (k + 1) + t.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = t := Fin.ext (by dsimp; omega)
          rw [ht']; dsimp only [i', j']
          calc D ⟨i.val - 2 ^ (k + 1), by omega⟩ * D t * H ⟨i.val - 2 ^ (k + 1), by omega⟩ t *
               (D t * D ⟨j.val - 2 ^ (k + 1), by omega⟩ * H t ⟨j.val - 2 ^ (k + 1), by omega⟩) =
               (D t * D t) * (D ⟨i.val - 2 ^ (k + 1), by omega⟩ * D ⟨j.val - 2 ^ (k + 1), by omega⟩ *
                 (H ⟨i.val - 2 ^ (k + 1), by omega⟩ t * H t ⟨j.val - 2 ^ (k + 1), by omega⟩)) := by ac_rfl
            _ = D ⟨i.val - 2 ^ (k + 1), by omega⟩ * D ⟨j.val - 2 ^ (k + 1), by omega⟩ *
                (H ⟨i.val - 2 ^ (k + 1), by omega⟩ t * H t ⟨j.val - 2 ^ (k + 1), by omega⟩) := by rw [hDsq, Int.one_mul]
        rw [h1, h2, ihSq i' j']
        by_cases hij : i = j
        · have hij' : i' = j' := Fin.ext (by dsimp [i', j']; rw [hij])
          have hpow : (2 : Int) ^ (k + 2) = (2 : Int) ^ (k + 1) * 2 := Int.pow_succ (2 : Int) (k + 1)
          simp only [hij, hij', ↓reduceIte, hDsq, Int.one_mul, hpow]; omega
        · have hij' : i' ≠ j' := fin_ne_of_val (by dsimp [i', j']; have : i.val ≠ j.val := fun e => hij (Fin.ext e); omega)
          simp [hij, hij']
    · -- Part 2: H_{k+2} D_{k+2} H_{k+2} + D_{k+2} (H_{k+2} D_{k+2} H_{k+2}) D_{k+2} = 0!
      intro i j
      rw [grayDiag_succ (k + 1) i, grayDiag_succ (k + 1) j]
      by_cases hi : i.val < 2 ^ (k + 1) <;> by_cases hj : j.val < 2 ^ (k + 1)
      · -- Top-left block of H_{k+2} D_{k+2} H_{k+2} is H^2 - D H^2 D = 0!
        have hzero : sumFin (fun t : Fin (2 ^ (k + 2)) => grayHadMat (k + 2) i t * grayDiag (k + 2) t * grayHadMat (k + 2) t j) = 0 := by
          rw [sumFin_pow2_split (k + 1)]
          let i' : Fin (2 ^ (k + 1)) := ⟨i.val, hi⟩; let j' : Fin (2 ^ (k + 1)) := ⟨j.val, hj⟩
          have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨t.val, by omega⟩ * grayDiag (k + 2) ⟨t.val, by omega⟩ * grayHadMat (k + 2) ⟨t.val, by omega⟩ j) =
                    matMul H H i' j' := by
            unfold matMul; apply sumFin_congr; intro t
            rw [grayDiag_succ (k + 1), hH_quad i ⟨t.val, by omega⟩, hH_quad ⟨t.val, by omega⟩ j]
            simp [hi, hj, t.isLt]; rfl
          have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayDiag (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayHadMat (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ j) =
                    -(D i' * D j' * matMul H H i' j') := by
            unfold matMul; rw [← sumFin_mul_left, ← sumFin_neg]; apply sumFin_congr; intro t
            rw [grayDiag_succ (k + 1), hH_quad i ⟨2 ^ (k + 1) + t.val, by omega⟩, hH_quad ⟨2 ^ (k + 1) + t.val, by omega⟩ j]
            have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
            simp only [hi, hj, hnt, ↓reduceIte, ↓reduceDIte]
            have ht' : (⟨2 ^ (k + 1) + t.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = t := Fin.ext (by dsimp; omega)
            rw [ht', Int.mul_neg, Int.mul_one, Int.neg_mul]; congr 1; dsimp only [i', j']; ac_rfl
          rw [h1, h2, ihSq i' j']
          by_cases hij' : i' = j'
          · rw [hij']; simp [hDsq]; omega
          · simp [hij']
        rw [hzero]; simp
      · -- Off-diagonal: (+1) * (-1) = -1 cancels identically!
        simp only [hi, hj, ↓reduceIte]; omega
      · simp only [hi, hj, ↓reduceIte]; omega
      · -- Bottom-right block is H^2 - D H^2 D = 0!
        have hzero : sumFin (fun t : Fin (2 ^ (k + 2)) => grayHadMat (k + 2) i t * grayDiag (k + 2) t * grayHadMat (k + 2) t j) = 0 := by
          rw [sumFin_pow2_split (k + 1)]
          let i' : Fin (2 ^ (k + 1)) := ⟨i.val - 2 ^ (k + 1), by omega⟩; let j' : Fin (2 ^ (k + 1)) := ⟨j.val - 2 ^ (k + 1), by omega⟩
          have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨t.val, by omega⟩ * grayDiag (k + 2) ⟨t.val, by omega⟩ * grayHadMat (k + 2) ⟨t.val, by omega⟩ j) =
                    matMul H H i' j' := by
            unfold matMul; apply sumFin_congr; intro t
            rw [grayDiag_succ (k + 1), hH_quad i ⟨t.val, by omega⟩, hH_quad ⟨t.val, by omega⟩ j]
            simp only [hi, hj, t.isLt, ↓reduceIte, ↓reduceDIte, Int.mul_one]
            dsimp only [i', j']
            calc D t * H ⟨i.val - 2 ^ (k + 1), by omega⟩ t * (D t * H t ⟨j.val - 2 ^ (k + 1), by omega⟩) =
                  (D t * D t) * (H ⟨i.val - 2 ^ (k + 1), by omega⟩ t * H t ⟨j.val - 2 ^ (k + 1), by omega⟩) := by ac_rfl
              _ = H ⟨i.val - 2 ^ (k + 1), by omega⟩ t * H t ⟨j.val - 2 ^ (k + 1), by omega⟩ := by rw [hDsq, Int.one_mul]
          have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayHadMat (k + 2) i ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayDiag (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayHadMat (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ j) =
                    -(D i' * D j' * matMul H H i' j') := by
            unfold matMul; rw [← sumFin_mul_left, ← sumFin_neg]; apply sumFin_congr; intro t
            rw [grayDiag_succ (k + 1), hH_quad i ⟨2 ^ (k + 1) + t.val, by omega⟩, hH_quad ⟨2 ^ (k + 1) + t.val, by omega⟩ j]
            have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
            simp only [hi, hj, hnt, ↓reduceIte, ↓reduceDIte]
            have ht' : (⟨2 ^ (k + 1) + t.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = t := Fin.ext (by dsimp; omega)
            rw [ht', Int.mul_neg, Int.mul_one, Int.neg_mul]; congr 1; dsimp only [i', j']
            calc D ⟨i.val - 2 ^ (k + 1), by omega⟩ * D t * H ⟨i.val - 2 ^ (k + 1), by omega⟩ t *
                 (D t * D ⟨j.val - 2 ^ (k + 1), by omega⟩ * H t ⟨j.val - 2 ^ (k + 1), by omega⟩) =
                 (D t * D t) * (D ⟨i.val - 2 ^ (k + 1), by omega⟩ * D ⟨j.val - 2 ^ (k + 1), by omega⟩ *
                   (H ⟨i.val - 2 ^ (k + 1), by omega⟩ t * H t ⟨j.val - 2 ^ (k + 1), by omega⟩)) := by ac_rfl
              _ = D ⟨i.val - 2 ^ (k + 1), by omega⟩ * D ⟨j.val - 2 ^ (k + 1), by omega⟩ *
                  (H ⟨i.val - 2 ^ (k + 1), by omega⟩ t * H t ⟨j.val - 2 ^ (k + 1), by omega⟩) := by rw [hDsq, Int.one_mul]
          rw [h1, h2, ihSq i' j']
          by_cases hij' : i' = j'
          · rw [hij']; simp [hDsq]; omega
          · simp [hij']
        rw [hzero]; simp

/-- Simultaneous induction: `G_k H_k + H_k G_k = 0` AND `G_k (D_k H_k) + (D_k H_k)(D_k G_k D_k) = 0`. -/
theorem grayWalshWeighted_anticomm (b : Nat → Int) : ∀ (k : Nat), 1 ≤ k →
    (∀ i j : Fin (2 ^ k), matMul (grayWalshWeightedMat k b) (grayHadMat k) i j +
                          matMul (grayHadMat k) (grayWalshWeightedMat k b) i j = 0) ∧
    (∀ i j : Fin (2 ^ k),
      sumFin (fun t : Fin (2 ^ k) => grayWalshWeightedMat k b i t * grayDiag k t * grayHadMat k t j) +
      sumFin (fun t : Fin (2 ^ k) => grayDiag k i * grayHadMat k i t * (grayDiag k t * grayWalshWeightedMat k b t j * grayDiag k j)) = 0)
  | 0, hk => by omega
  | 1, _ => by
    have hg00 : grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by unfold grayWalshWeightedMat; simp
    have hg11 : grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by unfold grayWalshWeightedMat; simp
    have hg01 : grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ = b 0 := by
      unfold grayWalshWeightedMat
      have hne : (⟨0, by decide⟩ : Fin (2 ^ 1)) ≠ ⟨1, by decide⟩ := by decide
      have hm : msb (0 ^^^ 1) = 0 := by decide
      have hs : sgnInt 0 1 = 1 := by decide
      have hp : paritySign (gray 0 &&& gray 1) = 1 := by decide
      change (if (⟨0, by decide⟩ : Fin (2 ^ 1)) = ⟨1, by decide⟩ then 0 else b (msb (0 ^^^ 1)) * sgnInt 0 1 * paritySign (gray 0 &&& gray 1)) = b 0
      simp only [hne, ↓reduceIte, hm, hs, hp, Int.mul_one]
    have hg10 : grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ = -b 0 := by
      rw [(isSkew_grayWalshWeighted 1 b).2, hg01]
    have hh00 : grayHadMat 1 ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := by decide
    have hh01 : grayHadMat 1 ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 := by decide
    have hh10 : grayHadMat 1 ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 := by decide
    have hh11 : grayHadMat 1 ⟨1, by decide⟩ ⟨1, by decide⟩ = -1 := by decide
    have hd0 : grayDiag 1 ⟨0, by decide⟩ = 1 := by decide
    have hd1 : grayDiag 1 ⟨1, by decide⟩ = -1 := by decide
    constructor
    · intro i j; unfold matMul
      simp only [sumFin_succ, sumFin_zero, Int.add_zero]
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      have hj : j.val = 0 ∨ j.val = 1 := by omega
      rcases hi with h1 | h1 <;> rcases hj with h2 | h2
      · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars
        change grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨0, by decide⟩ +
               grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨0, by decide⟩ +
               (grayHadMat 1 ⟨0, by decide⟩ ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ +
                grayHadMat 1 ⟨0, by decide⟩ ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩) = 0
        rw [hg00, hg01, hg10, hh00, hh01, hh10]; omega
      · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars
        change grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨1, by decide⟩ +
               grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨1, by decide⟩ +
               (grayHadMat 1 ⟨0, by decide⟩ ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ +
                grayHadMat 1 ⟨0, by decide⟩ ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩) = 0
        rw [hg00, hg01, hg11, hh00, hh01, hh11]; omega
      · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars
        change grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨0, by decide⟩ +
               grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨0, by decide⟩ +
               (grayHadMat 1 ⟨1, by decide⟩ ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ +
                grayHadMat 1 ⟨1, by decide⟩ ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩) = 0
        rw [hg00, hg10, hg11, hh00, hh10, hh11]; omega
      · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars
        change grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨1, by decide⟩ +
               grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨1, by decide⟩ +
               (grayHadMat 1 ⟨1, by decide⟩ ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ +
                grayHadMat 1 ⟨1, by decide⟩ ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩) = 0
        rw [hg01, hg10, hg11, hh01, hh10, hh11]; omega
    · intro i j
      simp only [sumFin_succ, sumFin_zero, Int.add_zero]
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      have hj : j.val = 0 ∨ j.val = 1 := by omega
      rcases hi with h1 | h1 <;> rcases hj with h2 | h2
      · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars
        change grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ * grayDiag 1 ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨0, by decide⟩ +
               grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ * grayDiag 1 ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨0, by decide⟩ +
               (grayDiag 1 ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨0, by decide⟩ * (grayDiag 1 ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ * grayDiag 1 ⟨0, by decide⟩) +
                grayDiag 1 ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨1, by decide⟩ * (grayDiag 1 ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ * grayDiag 1 ⟨0, by decide⟩)) = 0
        rw [hg00, hg01, hg10, hh00, hh01, hh10, hd0, hd1]; omega
      · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars
        change grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ * grayDiag 1 ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨1, by decide⟩ +
               grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ * grayDiag 1 ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨1, by decide⟩ +
               (grayDiag 1 ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨0, by decide⟩ * (grayDiag 1 ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ * grayDiag 1 ⟨1, by decide⟩) +
                grayDiag 1 ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨1, by decide⟩ * (grayDiag 1 ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ * grayDiag 1 ⟨1, by decide⟩)) = 0
        rw [hg00, hg01, hg11, hh00, hh01, hh11, hd0, hd1]; omega
      · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars
        change grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ * grayDiag 1 ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨0, by decide⟩ +
               grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ * grayDiag 1 ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨0, by decide⟩ +
               (grayDiag 1 ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨0, by decide⟩ * (grayDiag 1 ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ * grayDiag 1 ⟨0, by decide⟩) +
                grayDiag 1 ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨1, by decide⟩ * (grayDiag 1 ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ * grayDiag 1 ⟨0, by decide⟩)) = 0
        rw [hg00, hg10, hg11, hh00, hh10, hh11, hd0, hd1]; omega
      · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars
        change grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ * grayDiag 1 ⟨0, by decide⟩ * grayHadMat 1 ⟨0, by decide⟩ ⟨1, by decide⟩ +
               grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ * grayDiag 1 ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨1, by decide⟩ +
               (grayDiag 1 ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨0, by decide⟩ * (grayDiag 1 ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ * grayDiag 1 ⟨1, by decide⟩) +
                grayDiag 1 ⟨1, by decide⟩ * grayHadMat 1 ⟨1, by decide⟩ ⟨1, by decide⟩ * (grayDiag 1 ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ * grayDiag 1 ⟨1, by decide⟩)) = 0
        rw [hg01, hg10, hg11, hh01, hh10, hh11, hd0, hd1]; omega
  | k + 2, _ => by
    have hk1 : 1 ≤ k + 1 := by omega
    rcases grayWalshWeighted_anticomm b (k + 1) hk1 with ⟨ihGH, ihGB⟩
    rcases grayHad_algebra (k + 1) hk1 with ⟨hHsq, hHDH⟩
    let G := grayWalshWeightedMat (k + 1) b
    let H := grayHadMat (k + 1)
    let D := grayDiag (k + 1)
    let bk : Int := b (k + 1)
    have hGskew : IsSkew G := isSkew_grayWalshWeighted (k + 1) b
    have hHsymm : ∀ a c : Fin (2 ^ (k + 1)), H a c = H c a := grayHad_symm (k + 1)
    have hDsq : ∀ a : Fin (2 ^ (k + 1)), D a * D a = 1 := grayDiag_sq (k + 1)
    have hp : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := pow2_eq_add (k + 1)
    -- Transpose of ihGB gives: H D G + D G D H D = 0
    have ihGB_T : ∀ u v : Fin (2 ^ (k + 1)),
        sumFin (fun t : Fin (2 ^ (k + 1)) => H u t * D t * G t v) +
        sumFin (fun t : Fin (2 ^ (k + 1)) => D u * G u t * D t * H t v * D v) = 0 := by
      intro u v
      have h0 : sumFin (fun t : Fin (2 ^ (k + 1)) => G v t * D t * H t u) +
                sumFin (fun t : Fin (2 ^ (k + 1)) => D v * H v t * (D t * G t u * D u)) = 0 := ihGB v u
      have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => G v t * D t * H t u) =
                -sumFin (fun t : Fin (2 ^ (k + 1)) => H u t * D t * G t v) := by
        rw [← sumFin_neg]; apply sumFin_congr; intro t
        rw [hGskew.2 v t, hHsymm t u, Int.neg_mul, Int.neg_mul]; congr 1; ac_rfl
      have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => D v * H v t * (D t * G t u * D u)) =
                -sumFin (fun t : Fin (2 ^ (k + 1)) => D u * G u t * D t * H t v * D v) := by
        rw [← sumFin_neg]; apply sumFin_congr; intro t
        rw [hGskew.2 t u, hHsymm v t, Int.mul_neg, Int.neg_mul, Int.mul_neg]; congr 1; ac_rfl
      rw [h1, h2] at h0; omega
    -- Helper: evaluate G_{k+2} and H_{k+2} on top/bottom halves
    have hG00 : ∀ u v : Fin (2 ^ (k + 1)), grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ = G u v := by
      intro u v; rw [grayWalshWeighted_block (k + 1) hk1 b]; unfold castMat blockMat; simp [u.isLt, v.isLt]; rfl
    have hG01 : ∀ u v : Fin (2 ^ (k + 1)), grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩ = bk * (D u * H u v) := by
      intro u v; rw [grayWalshWeighted_block (k + 1) hk1 b]; unfold castMat blockMat
      have hnv : ¬ (2 ^ (k + 1) + v.val < 2 ^ (k + 1)) := by omega
      simp only [u.isLt, hnv, ↓reduceDIte]
      have hv' : (⟨2 ^ (k + 1) + v.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = v := Fin.ext (by dsimp; omega)
      rw [hv']
    have hG10 : ∀ u v : Fin (2 ^ (k + 1)), grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨v.val, by omega⟩ = -(bk * (D v * H u v)) := by
      intro u v; rw [grayWalshWeighted_block (k + 1) hk1 b]; unfold castMat blockMat
      have hnu : ¬ (2 ^ (k + 1) + u.val < 2 ^ (k + 1)) := by omega
      simp only [hnu, v.isLt, ↓reduceDIte]
      have hu' : (⟨2 ^ (k + 1) + u.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = u := Fin.ext (by dsimp; omega)
      rw [hu', grayHad_symm (k + 1) v u]
    have hG11 : ∀ u v : Fin (2 ^ (k + 1)), grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩ = D u * G u v * D v := by
      intro u v; rw [grayWalshWeighted_block (k + 1) hk1 b]; unfold castMat blockMat diagCong
      have hnu : ¬ (2 ^ (k + 1) + u.val < 2 ^ (k + 1)) := by omega
      have hnv : ¬ (2 ^ (k + 1) + v.val < 2 ^ (k + 1)) := by omega
      simp only [hnu, hnv, ↓reduceDIte]
      have hu' : (⟨2 ^ (k + 1) + u.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = u := Fin.ext (by dsimp; omega)
      have hv' : (⟨2 ^ (k + 1) + v.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = v := Fin.ext (by dsimp; omega)
      rw [hu', hv']
    have hH00 : ∀ u v : Fin (2 ^ (k + 1)), grayHadMat (k + 2) ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ = H u v := by
      intro u v; rw [grayHad_block (k + 1) hk1]; unfold castMat blockMat; simp [u.isLt, v.isLt]; rfl
    have hH01 : ∀ u v : Fin (2 ^ (k + 1)), grayHadMat (k + 2) ⟨u.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩ = D u * H u v := by
      intro u v; rw [grayHad_block (k + 1) hk1]; unfold castMat blockMat
      have hnv : ¬ (2 ^ (k + 1) + v.val < 2 ^ (k + 1)) := by omega
      simp only [u.isLt, hnv, ↓reduceDIte]
      have hv' : (⟨2 ^ (k + 1) + v.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = v := Fin.ext (by dsimp; omega)
      rw [hv']
    have hH10 : ∀ u v : Fin (2 ^ (k + 1)), grayHadMat (k + 2) ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨v.val, by omega⟩ = D v * H u v := by
      intro u v; rw [grayHad_block (k + 1) hk1]; unfold castMat blockMat
      have hnu : ¬ (2 ^ (k + 1) + u.val < 2 ^ (k + 1)) := by omega
      simp only [hnu, v.isLt, ↓reduceDIte]
      have hu' : (⟨2 ^ (k + 1) + u.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = u := Fin.ext (by dsimp; omega)
      rw [hu']
    have hH11 : ∀ u v : Fin (2 ^ (k + 1)), grayHadMat (k + 2) ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩ = D u * D v * H u v := by
      intro u v; rw [grayHad_block (k + 1) hk1]; unfold castMat blockMat
      have hnu : ¬ (2 ^ (k + 1) + u.val < 2 ^ (k + 1)) := by omega
      have hnv : ¬ (2 ^ (k + 1) + v.val < 2 ^ (k + 1)) := by omega
      simp only [hnu, hnv, ↓reduceDIte]
      have hu' : (⟨2 ^ (k + 1) + u.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = u := Fin.ext (by dsimp; omega)
      have hv' : (⟨2 ^ (k + 1) + v.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = v := Fin.ext (by dsimp; omega)
      rw [hu', hv']
    -- Unify BOTH Part 1 (s = +1: G*H + H*G = 0) and Part 2 (s = -1: G*(D*H) + (D*H)*(D*G*D) = 0)!
    -- Look! Since D_{k+2} = diag(I, -I), the sum for Part 1 has (ε = 1) and Part 2 has (ε = -1) on the D_{k+2} signs!
    -- Even cleaner: prove each of the 4 quadrants cleanly for both!
    have hBoth : ∀ (ε : Int), ε * ε = 1 → ∀ i j : Fin (2 ^ (k + 2)),
        sumFin (fun t : Fin (2 ^ (k + 2)) =>
          grayWalshWeightedMat (k + 2) b i t * (if t.val < 2 ^ (k + 1) then (1 : Int) else ε) * grayHadMat (k + 2) t j) +
        sumFin (fun t : Fin (2 ^ (k + 2)) =>
          (if i.val < 2 ^ (k + 1) then (1 : Int) else ε) * grayHadMat (k + 2) i t *
          ((if t.val < 2 ^ (k + 1) then (1 : Int) else ε) * grayWalshWeightedMat (k + 2) b t j *
           (if j.val < 2 ^ (k + 1) then (1 : Int) else ε))) = 0 := by
      intro ε hε i j
      rw [sumFin_pow2_split (k + 1), sumFin_pow2_split (k + 1)]
      by_cases hi : i.val < 2 ^ (k + 1) <;> by_cases hj : j.val < 2 ^ (k + 1)
      · let u : Fin (2 ^ (k + 1)) := ⟨i.val, hi⟩; let v : Fin (2 ^ (k + 1)) := ⟨j.val, hj⟩
        have hi_eq : i = ⟨u.val, by omega⟩ := Fin.ext rfl
        have hj_eq : j = ⟨v.val, by omega⟩ := Fin.ext rfl
        rw [hi_eq, hj_eq]
        have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨t.val, by omega⟩ * (if t.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨t.val, by omega⟩ ⟨v.val, by omega⟩) =
                  matMul G H u v := by
          unfold matMul; apply sumFin_congr; intro t; rw [hG00, hH00]; simp [t.isLt]
        have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * (if 2 ^ (k + 1) + t.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨v.val, by omega⟩) =
                  ε * bk * D u * D v * matMul H H u v := by
          unfold matMul; rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          rw [hG01, hH10]; simp only [hnt, ↓reduceIte]; ac_rfl
        have h3 : sumFin (fun t : Fin (2 ^ (k + 1)) => (if u.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨u.val, by omega⟩ ⟨t.val, by omega⟩ * ((if t.val < 2 ^ (k + 1) then 1 else ε) * grayWalshWeightedMat (k + 2) b ⟨t.val, by omega⟩ ⟨v.val, by omega⟩ * (if v.val < 2 ^ (k + 1) then 1 else ε))) =
                  matMul H G u v := by
          unfold matMul; apply sumFin_congr; intro t; rw [hH00, hG00]; simp [u.isLt, v.isLt, t.isLt]
        have h4 : sumFin (fun t : Fin (2 ^ (k + 1)) => (if u.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * ((if 2 ^ (k + 1) + t.val < 2 ^ (k + 1) then 1 else ε) * grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨v.val, by omega⟩ * (if v.val < 2 ^ (k + 1) then 1 else ε))) =
                  -(ε * bk * D u * D v * matMul H H u v) := by
          unfold matMul; rw [← sumFin_mul_left, ← sumFin_neg]; apply sumFin_congr; intro t
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          rw [hH01, hG10]; simp only [u.isLt, v.isLt, hnt, ↓reduceIte, Int.one_mul, Int.mul_one, Int.mul_neg]
          congr 1; ac_rfl
        rw [h1, h2, h3, h4]
        have hGH0 : matMul G H u v + matMul H G u v = 0 := ihGH u v
        omega
      · let u : Fin (2 ^ (k + 1)) := ⟨i.val, hi⟩; let v : Fin (2 ^ (k + 1)) := ⟨j.val - 2 ^ (k + 1), by omega⟩
        have hi_eq : i = ⟨u.val, by omega⟩ := Fin.ext rfl
        have hj_eq : j = ⟨2 ^ (k + 1) + v.val, by omega⟩ := Fin.ext (by dsimp [v]; omega)
        rw [hi_eq, hj_eq]
        have hnv : ¬ (2 ^ (k + 1) + v.val < 2 ^ (k + 1)) := by omega
        have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨t.val, by omega⟩ * (if t.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩) =
                  sumFin (fun t : Fin (2 ^ (k + 1)) => G u t * D t * H t v) := by
          apply sumFin_congr; intro t; rw [hG00, hH01]; simp only [t.isLt, ↓reduceIte, Int.mul_one]; ac_rfl
        have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * (if 2 ^ (k + 1) + t.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩) =
                  ε * bk * (D u * D v * sumFin (fun t : Fin (2 ^ (k + 1)) => H u t * D t * H t v)) := by
          rw [← sumFin_mul_left, ← sumFin_mul_left]; apply sumFin_congr; intro t
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          rw [hG01, hH11]; simp only [hnt, ↓reduceIte]; ac_rfl
        have h3 : sumFin (fun t : Fin (2 ^ (k + 1)) => (if u.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨u.val, by omega⟩ ⟨t.val, by omega⟩ * ((if t.val < 2 ^ (k + 1) then 1 else ε) * grayWalshWeightedMat (k + 2) b ⟨t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩ * (if 2 ^ (k + 1) + v.val < 2 ^ (k + 1) then 1 else ε))) =
                  ε * bk * sumFin (fun t : Fin (2 ^ (k + 1)) => H u t * D t * H t v) := by
          rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          rw [hH00, hG01]; simp only [u.isLt, t.isLt, hnv, ↓reduceIte, Int.one_mul]; ac_rfl
        have h4 : sumFin (fun t : Fin (2 ^ (k + 1)) => (if u.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * ((if 2 ^ (k + 1) + t.val < 2 ^ (k + 1) then 1 else ε) * grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩ * (if 2 ^ (k + 1) + v.val < 2 ^ (k + 1) then 1 else ε))) =
                  sumFin (fun t : Fin (2 ^ (k + 1)) => D u * H u t * (D t * G t v * D v)) := by
          apply sumFin_congr; intro t
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          rw [hH01, hG11]; simp only [u.isLt, hnt, hnv, ↓reduceIte, Int.one_mul]
          calc D u * H u t * (ε * (D t * G t v * D v) * ε) = (ε * ε) * (D u * H u t * (D t * G t v * D v)) := by ac_rfl
            _ = D u * H u t * (D t * G t v * D v) := by rw [hε, Int.one_mul]
        rw [h1, h2, h3, h4]
        have hA : sumFin (fun t : Fin (2 ^ (k + 1)) => G u t * D t * H t v) +
                  sumFin (fun t : Fin (2 ^ (k + 1)) => D u * H u t * (D t * G t v * D v)) = 0 := ihGB u v
        have hB : sumFin (fun t : Fin (2 ^ (k + 1)) => H u t * D t * H t v) +
                  D u * D v * sumFin (fun t : Fin (2 ^ (k + 1)) => H u t * D t * H t v) = 0 := hHDH u v
        have hB' : ε * bk * (D u * D v * sumFin (fun t => H u t * D t * H t v)) +
                   ε * bk * sumFin (fun t => H u t * D t * H t v) = 0 := by
          rw [← Int.mul_add, Int.add_comm, hB, Int.mul_zero]
        omega
      · let u : Fin (2 ^ (k + 1)) := ⟨i.val - 2 ^ (k + 1), by omega⟩; let v : Fin (2 ^ (k + 1)) := ⟨j.val, hj⟩
        have hi_eq : i = ⟨2 ^ (k + 1) + u.val, by omega⟩ := Fin.ext (by dsimp [u]; omega)
        have hj_eq : j = ⟨v.val, by omega⟩ := Fin.ext rfl
        rw [hi_eq, hj_eq]
        have hnu : ¬ (2 ^ (k + 1) + u.val < 2 ^ (k + 1)) := by omega
        have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨t.val, by omega⟩ * (if t.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨t.val, by omega⟩ ⟨v.val, by omega⟩) =
                  -(bk * sumFin (fun t : Fin (2 ^ (k + 1)) => H u t * D t * H t v)) := by
          rw [← sumFin_mul_left, ← sumFin_neg]; apply sumFin_congr; intro t
          rw [hG10, hH00]; simp only [t.isLt, ↓reduceIte, Int.mul_one, Int.neg_mul]; congr 1; ac_rfl
        have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * (if 2 ^ (k + 1) + t.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨v.val, by omega⟩) =
                  ε * sumFin (fun t : Fin (2 ^ (k + 1)) => D u * G u t * D t * H t v * D v) := by
          rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          rw [hG11, hH10]; simp only [hnt, ↓reduceIte]; ac_rfl
        have h3 : sumFin (fun t : Fin (2 ^ (k + 1)) => (if 2 ^ (k + 1) + u.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨t.val, by omega⟩ * ((if t.val < 2 ^ (k + 1) then 1 else ε) * grayWalshWeightedMat (k + 2) b ⟨t.val, by omega⟩ ⟨v.val, by omega⟩ * (if v.val < 2 ^ (k + 1) then 1 else ε))) =
                  ε * sumFin (fun t : Fin (2 ^ (k + 1)) => H u t * D t * G t v) := by
          rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          rw [hH10, hG00]; simp only [hnu, t.isLt, v.isLt, ↓reduceIte, Int.one_mul, Int.mul_one]; ac_rfl
        have h4 : sumFin (fun t : Fin (2 ^ (k + 1)) => (if 2 ^ (k + 1) + u.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * ((if 2 ^ (k + 1) + t.val < 2 ^ (k + 1) then 1 else ε) * grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨v.val, by omega⟩ * (if v.val < 2 ^ (k + 1) then 1 else ε))) =
                  -(bk * (D u * D v * sumFin (fun t : Fin (2 ^ (k + 1)) => H u t * D t * H t v))) := by
          rw [← sumFin_mul_left, ← sumFin_mul_left, ← sumFin_neg]; apply sumFin_congr; intro t
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          rw [hH11, hG10]; simp only [hnu, hnt, v.isLt, ↓reduceIte, Int.mul_one, Int.mul_neg]
          congr 1
          calc ε * (D u * D t * H u t) * (ε * (bk * (D v * H t v))) = (ε * ε) * (bk * (D u * D v * (H u t * D t * H t v))) := by ac_rfl
            _ = bk * (D u * D v * (H u t * D t * H t v)) := by rw [hε, Int.one_mul]
        rw [h1, h2, h3, h4]
        have hA : ε * sumFin (fun t => D u * G u t * D t * H t v * D v) + ε * sumFin (fun t => H u t * D t * G t v) = 0 := by
          rw [← Int.mul_add, Int.add_comm, ihGB_T u v, Int.mul_zero]
        have hB : -(bk * sumFin (fun t => H u t * D t * H t v)) + -(bk * (D u * D v * sumFin (fun t => H u t * D t * H t v))) = 0 := by
          have := hHDH u v
          have : bk * (sumFin (fun t => H u t * D t * H t v) + D u * D v * sumFin (fun t => H u t * D t * H t v)) = 0 := by
            rw [this, Int.mul_zero]
          rw [Int.mul_add] at this; omega
        omega
      · let u : Fin (2 ^ (k + 1)) := ⟨i.val - 2 ^ (k + 1), by omega⟩; let v : Fin (2 ^ (k + 1)) := ⟨j.val - 2 ^ (k + 1), by omega⟩
        have hi_eq : i = ⟨2 ^ (k + 1) + u.val, by omega⟩ := Fin.ext (by dsimp [u]; omega)
        have hj_eq : j = ⟨2 ^ (k + 1) + v.val, by omega⟩ := Fin.ext (by dsimp [v]; omega)
        rw [hi_eq, hj_eq]
        have hnu : ¬ (2 ^ (k + 1) + u.val < 2 ^ (k + 1)) := by omega
        have hnv : ¬ (2 ^ (k + 1) + v.val < 2 ^ (k + 1)) := by omega
        have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨t.val, by omega⟩ * (if t.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩) =
                  -(bk * matMul H H u v) := by
          unfold matMul; rw [← sumFin_mul_left, ← sumFin_neg]; apply sumFin_congr; intro t
          rw [hG10, hH01]; simp only [t.isLt, ↓reduceIte, Int.mul_one, Int.neg_mul]; congr 1
          calc bk * (D t * H u t) * (D t * H t v) = (D t * D t) * (bk * (H u t * H t v)) := by ac_rfl
            _ = bk * (H u t * H t v) := by rw [grayDiag_sq, Int.one_mul]
        have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * (if 2 ^ (k + 1) + t.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩) =
                  ε * D u * D v * matMul G H u v := by
          unfold matMul; rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          rw [hG11, hH11]; simp only [hnt, ↓reduceIte]
          calc D u * G u t * D t * ε * (D t * D v * H t v) = (D t * D t) * (ε * D u * D v * (G u t * H t v)) := by ac_rfl
            _ = ε * D u * D v * (G u t * H t v) := by rw [grayDiag_sq, Int.one_mul]
        have h3 : sumFin (fun t : Fin (2 ^ (k + 1)) => (if 2 ^ (k + 1) + u.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨t.val, by omega⟩ * ((if t.val < 2 ^ (k + 1) then 1 else ε) * grayWalshWeightedMat (k + 2) b ⟨t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩ * (if 2 ^ (k + 1) + v.val < 2 ^ (k + 1) then 1 else ε))) =
                  bk * matMul H H u v := by
          unfold matMul; rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          rw [hH10, hG01]; simp only [hnu, t.isLt, hnv, ↓reduceIte, Int.one_mul]
          calc ε * (D t * H u t) * (bk * (D t * H t v) * ε) = (ε * ε) * ((D t * D t) * (bk * (H u t * H t v))) := by ac_rfl
            _ = bk * (H u t * H t v) := by rw [hε, grayDiag_sq, Int.one_mul, Int.one_mul]
        have h4 : sumFin (fun t : Fin (2 ^ (k + 1)) => (if 2 ^ (k + 1) + u.val < 2 ^ (k + 1) then 1 else ε) * grayHadMat (k + 2) ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * ((if 2 ^ (k + 1) + t.val < 2 ^ (k + 1) then 1 else ε) * grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩ * (if 2 ^ (k + 1) + v.val < 2 ^ (k + 1) then 1 else ε))) =
                  ε * D u * D v * matMul H G u v := by
          unfold matMul; rw [← sumFin_mul_left]; apply sumFin_congr; intro t
          have hnt : ¬ (2 ^ (k + 1) + t.val < 2 ^ (k + 1)) := by omega
          rw [hH11, hG11]; simp only [hnu, hnt, hnv, ↓reduceIte]
          calc ε * (D u * D t * H u t) * (ε * (D t * G t v * D v) * ε) =
                (ε * ε) * ((D t * D t) * (ε * D u * D v * (H u t * G t v))) := by ac_rfl
            _ = ε * D u * D v * (H u t * G t v) := by rw [hε, grayDiag_sq, Int.one_mul, Int.one_mul]
        rw [h1, h2, h3, h4]
        have hA : ε * D u * D v * matMul G H u v + ε * D u * D v * matMul H G u v = 0 := by
          rw [← Int.mul_add, ihGH u v, Int.mul_zero]
        omega
    constructor
    · intro i j; have h1 := hBoth 1 rfl i j
      unfold matMul; simp only [ite_self, Int.mul_one, Int.one_mul] at h1; exact h1
    · intro i j; have h2 := hBoth (-1) rfl i j
      simp only [← grayDiag_succ (k + 1)] at h2; exact h2

/-- **Theorem B1 (Universal Skew-Conference Identity for All Weight Sequences `b`):**
    `(G_k^{(b)})^2 = -μ_k(b) * I_{2^k}` for all `k ≥ 1` and ALL `b : Nat → Int`. -/
theorem grayWalshWeighted_sq (b : Nat → Int) : ∀ (k : Nat), 1 ≤ k →
    ∀ i j : Fin (2 ^ k),
      matMul (grayWalshWeightedMat k b) (grayWalshWeightedMat k b) i j =
      if i = j then -grayMu b k else 0
  | 0, hk, _, _ => by omega
  | 1, _, i, j => by
    have hg00 : grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by unfold grayWalshWeightedMat; simp
    have hg11 : grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by unfold grayWalshWeightedMat; simp
    have hg01 : grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ = b 0 := by
      unfold grayWalshWeightedMat
      have hne : (⟨0, by decide⟩ : Fin (2 ^ 1)) ≠ ⟨1, by decide⟩ := by decide
      have hm : msb (0 ^^^ 1) = 0 := by decide
      have hs : sgnInt 0 1 = 1 := by decide
      have hp : paritySign (gray 0 &&& gray 1) = 1 := by decide
      change (if (⟨0, by decide⟩ : Fin (2 ^ 1)) = ⟨1, by decide⟩ then 0 else b (msb (0 ^^^ 1)) * sgnInt 0 1 * paritySign (gray 0 &&& gray 1)) = b 0
      simp only [hne, ↓reduceIte, hm, hs, hp, Int.mul_one]
    have hg10 : grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ = -b 0 := by
      rw [(isSkew_grayWalshWeighted 1 b).2, hg01]
    unfold matMul grayMu
    simp only [sumFin_succ, sumFin_zero, Int.add_zero]
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hi with h1 | h1 <;> rcases hj with h2 | h2
    · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars
      change grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ +
             grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ = _
      rw [hg00, hg01, hg10]; simp [Int.mul_neg]
    · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars
      change grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ +
             grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ = _
      rw [hg00, hg11]; simp
    · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars
      change grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨0, by decide⟩ +
             grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ = _
      rw [hg00, hg11]; simp
    · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars
      change grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨0, by decide⟩ * grayWalshWeightedMat 1 b ⟨0, by decide⟩ ⟨1, by decide⟩ +
             grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ * grayWalshWeightedMat 1 b ⟨1, by decide⟩ ⟨1, by decide⟩ = _
      rw [hg01, hg10, hg11]; simp [Int.neg_mul]
  | k + 2, _, i, j => by
    have hk1 : 1 ≤ k + 1 := by omega
    have ihSq := grayWalshWeighted_sq b (k + 1) hk1
    have hHsq := (grayHad_algebra (k + 1) hk1).1
    have hGB := (grayWalshWeighted_anticomm b (k + 1) hk1).2
    let G := grayWalshWeightedMat (k + 1) b
    let H := grayHadMat (k + 1)
    let D := grayDiag (k + 1)
    let bk : Int := b (k + 1)
    have hGskew : IsSkew G := isSkew_grayWalshWeighted (k + 1) b
    have hHsymm : ∀ a c : Fin (2 ^ (k + 1)), H a c = H c a := grayHad_symm (k + 1)
    have hDsq : ∀ a : Fin (2 ^ (k + 1)), D a * D a = 1 := grayDiag_sq (k + 1)
    have hp : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := pow2_eq_add (k + 1)
    have hG00 : ∀ u v : Fin (2 ^ (k + 1)), grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ = G u v := by
      intro u v; rw [grayWalshWeighted_block (k + 1) hk1 b]; unfold castMat blockMat; simp [u.isLt, v.isLt]; rfl
    have hG01 : ∀ u v : Fin (2 ^ (k + 1)), grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩ = bk * (D u * H u v) := by
      intro u v; rw [grayWalshWeighted_block (k + 1) hk1 b]; unfold castMat blockMat
      have hnv : ¬ (2 ^ (k + 1) + v.val < 2 ^ (k + 1)) := by omega
      simp only [u.isLt, hnv, ↓reduceDIte]
      have hv' : (⟨2 ^ (k + 1) + v.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = v := Fin.ext (by dsimp; omega)
      rw [hv']
    have hG10 : ∀ u v : Fin (2 ^ (k + 1)), grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨v.val, by omega⟩ = -(bk * (D v * H u v)) := by
      intro u v; rw [grayWalshWeighted_block (k + 1) hk1 b]; unfold castMat blockMat
      have hnu : ¬ (2 ^ (k + 1) + u.val < 2 ^ (k + 1)) := by omega
      simp only [hnu, v.isLt, ↓reduceDIte]
      have hu' : (⟨2 ^ (k + 1) + u.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = u := Fin.ext (by dsimp; omega)
      rw [hu', grayHad_symm (k + 1) v u]
    have hG11 : ∀ u v : Fin (2 ^ (k + 1)), grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩ = D u * G u v * D v := by
      intro u v; rw [grayWalshWeighted_block (k + 1) hk1 b]; unfold castMat blockMat diagCong
      have hnu : ¬ (2 ^ (k + 1) + u.val < 2 ^ (k + 1)) := by omega
      have hnv : ¬ (2 ^ (k + 1) + v.val < 2 ^ (k + 1)) := by omega
      simp only [hnu, hnv, ↓reduceDIte]
      have hu' : (⟨2 ^ (k + 1) + u.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = u := Fin.ext (by dsimp; omega)
      have hv' : (⟨2 ^ (k + 1) + v.val - 2 ^ (k + 1), by omega⟩ : Fin (2 ^ (k + 1))) = v := Fin.ext (by dsimp; omega)
      rw [hu', hv']
    unfold matMul; rw [sumFin_pow2_split (k + 1)]
    by_cases hi : i.val < 2 ^ (k + 1) <;> by_cases hj : j.val < 2 ^ (k + 1)
    · let u : Fin (2 ^ (k + 1)) := ⟨i.val, hi⟩; let v : Fin (2 ^ (k + 1)) := ⟨j.val, hj⟩
      have hi_eq : i = ⟨u.val, by omega⟩ := Fin.ext rfl
      have hj_eq : j = ⟨v.val, by omega⟩ := Fin.ext rfl
      rw [hi_eq, hj_eq]
      have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨t.val, by omega⟩ * grayWalshWeightedMat (k + 2) b ⟨t.val, by omega⟩ ⟨v.val, by omega⟩) =
                matMul G G u v := by
        unfold matMul; exact sumFin_congr (fun t => by rw [hG00, hG00])
      have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨v.val, by omega⟩) =
                -(bk * bk * (D u * D v * matMul H H u v)) := by
        unfold matMul; rw [← sumFin_mul_left, ← sumFin_mul_left, ← sumFin_neg]
        apply sumFin_congr; intro t; rw [hG01, hG10, Int.mul_neg]; congr 1; ac_rfl
      rw [h1, h2, ihSq u v, hHsq u v]
      by_cases huv : u = v
      · simp only [huv, ↓reduceIte, hDsq, Int.one_mul]
        have hmu : grayMu b (k + 2) = grayMu b (k + 1) + (2 : Int) ^ (k + 1) * (bk * bk) := rfl
        rw [hmu, Int.mul_comm (bk * bk)]; omega
      · have hne : (⟨u.val, by omega⟩ : Fin (2 ^ (k + 2))) ≠ ⟨v.val, by omega⟩ :=
          fin_ne_of_val (by dsimp; exact fun e => huv (Fin.ext e))
        simp [huv, hne]
    · let u : Fin (2 ^ (k + 1)) := ⟨i.val, hi⟩; let v : Fin (2 ^ (k + 1)) := ⟨j.val - 2 ^ (k + 1), by omega⟩
      have hi_eq : i = ⟨u.val, by omega⟩ := Fin.ext rfl
      have hj_eq : j = ⟨2 ^ (k + 1) + v.val, by omega⟩ := Fin.ext (by dsimp [v]; omega)
      have hne : i ≠ j := fin_ne_of_val (by omega)
      simp only [hne, ↓reduceIte]; rw [hi_eq, hj_eq]
      have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨t.val, by omega⟩ * grayWalshWeightedMat (k + 2) b ⟨t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩) =
                bk * sumFin (fun t : Fin (2 ^ (k + 1)) => G u t * D t * H t v) := by
        rw [← sumFin_mul_left]; apply sumFin_congr; intro t; rw [hG00, hG01]; ac_rfl
      have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩) =
                bk * sumFin (fun t : Fin (2 ^ (k + 1)) => D u * H u t * (D t * G t v * D v)) := by
        rw [← sumFin_mul_left]; apply sumFin_congr; intro t; rw [hG01, hG11]; ac_rfl
      rw [h1, h2, ← Int.mul_add, hGB u v, Int.mul_zero]
    · let u : Fin (2 ^ (k + 1)) := ⟨i.val - 2 ^ (k + 1), by omega⟩; let v : Fin (2 ^ (k + 1)) := ⟨j.val, hj⟩
      have hi_eq : i = ⟨2 ^ (k + 1) + u.val, by omega⟩ := Fin.ext (by dsimp [u]; omega)
      have hj_eq : j = ⟨v.val, by omega⟩ := Fin.ext rfl
      have hne : i ≠ j := fin_ne_of_val (by omega)
      simp only [hne, ↓reduceIte]; rw [hi_eq, hj_eq]
      have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨t.val, by omega⟩ * grayWalshWeightedMat (k + 2) b ⟨t.val, by omega⟩ ⟨v.val, by omega⟩) =
                bk * sumFin (fun t : Fin (2 ^ (k + 1)) => G v t * D t * H t u) := by
        rw [← sumFin_mul_left]; apply sumFin_congr; intro t
        rw [hG10, hG00, hGskew.2 t v, hHsymm u t, Int.neg_mul, Int.mul_neg, Int.neg_neg]; ac_rfl
      have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨v.val, by omega⟩) =
                bk * sumFin (fun t : Fin (2 ^ (k + 1)) => D v * H v t * (D t * G t u * D u)) := by
        rw [← sumFin_mul_left]; apply sumFin_congr; intro t
        rw [hG11, hG10, hGskew.2 u t, hHsymm t v]
        simp only [Int.mul_neg, Int.neg_mul, Int.neg_neg]; ac_rfl
      rw [h1, h2, ← Int.mul_add, hGB v u, Int.mul_zero]
    · let u : Fin (2 ^ (k + 1)) := ⟨i.val - 2 ^ (k + 1), by omega⟩; let v : Fin (2 ^ (k + 1)) := ⟨j.val - 2 ^ (k + 1), by omega⟩
      have hi_eq : i = ⟨2 ^ (k + 1) + u.val, by omega⟩ := Fin.ext (by dsimp [u]; omega)
      have hj_eq : j = ⟨2 ^ (k + 1) + v.val, by omega⟩ := Fin.ext (by dsimp [v]; omega)
      rw [hi_eq, hj_eq]
      have h1 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨t.val, by omega⟩ * grayWalshWeightedMat (k + 2) b ⟨t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩) =
                -(bk * bk * matMul H H u v) := by
        unfold matMul; rw [← sumFin_mul_left, ← sumFin_neg]; apply sumFin_congr; intro t
        rw [hG10, hG01, Int.neg_mul]; congr 1
        calc bk * (D t * H u t) * (bk * (D t * H t v)) = (D t * D t) * (bk * bk * (H u t * H t v)) := by ac_rfl
          _ = bk * bk * (H u t * H t v) := by rw [grayDiag_sq, Int.one_mul]
      have h2 : sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + u.val, by omega⟩ ⟨2 ^ (k + 1) + t.val, by omega⟩ * grayWalshWeightedMat (k + 2) b ⟨2 ^ (k + 1) + t.val, by omega⟩ ⟨2 ^ (k + 1) + v.val, by omega⟩) =
                D u * D v * matMul G G u v := by
        unfold matMul; rw [← sumFin_mul_left]; apply sumFin_congr; intro t
        rw [hG11, hG11]
        calc D u * G u t * D t * (D t * G t v * D v) = (D t * D t) * (D u * D v * (G u t * G t v)) := by ac_rfl
          _ = D u * D v * (G u t * G t v) := by rw [grayDiag_sq, Int.one_mul]
      rw [h1, h2, hHsq u v, ihSq u v]
      by_cases huv : u = v
      · simp only [huv, ↓reduceIte, hDsq, Int.one_mul]
        have hmu : grayMu b (k + 2) = grayMu b (k + 1) + (2 : Int) ^ (k + 1) * (bk * bk) := rfl
        rw [hmu, Int.mul_comm (bk * bk)]; omega
      · have hne : (⟨2 ^ (k + 1) + u.val, by omega⟩ : Fin (2 ^ (k + 2))) ≠ ⟨2 ^ (k + 1) + v.val, by omega⟩ :=
          fin_ne_of_val (by dsimp; have : u.val ≠ v.val := fun e => huv (Fin.ext e); omega)
        simp [huv, hne]

theorem prodFin_grayDiag (k : Nat) (hk : 1 ≤ k) :
    prodFin (grayDiag k) = (-1 : Int) ^ (2 ^ (k - 1)) := by
  cases k with
  | zero => omega
  | succ k' =>
    rw [← prodFin_cast (show 2 ^ k' + 2 ^ k' = 2 ^ (k' + 1) by rw [pow2_eq_add]), prodFin_split]
    have hL : prodFin (fun i : Fin (2 ^ k') => grayDiag (k' + 1) ⟨i.val, by have := pow2_eq_add k'; omega⟩) = 1 := by
      have : prodFin (fun i : Fin (2 ^ k') => grayDiag (k' + 1) ⟨i.val, by have := pow2_eq_add k'; omega⟩) =
             prodFin (fun _ : Fin (2 ^ k') => (1 : Int)) :=
        prodFin_congr (fun i => by rw [grayDiag_succ]; simp [i.isLt])
      rw [this, prodFin_const]; exact Int.one_pow
    have hR : prodFin (fun j : Fin (2 ^ k') => grayDiag (k' + 1) ⟨2 ^ k' + j.val, by have := pow2_eq_add k'; omega⟩) = (-1 : Int) ^ (2 ^ k') := by
      have : prodFin (fun j : Fin (2 ^ k') => grayDiag (k' + 1) ⟨2 ^ k' + j.val, by have := pow2_eq_add k'; omega⟩) =
             prodFin (fun _ : Fin (2 ^ k') => (-1 : Int)) :=
        prodFin_congr (fun j => by
          rw [grayDiag_succ]
          have hnj : ¬ (2 ^ k' + j.val < 2 ^ k') := by omega
          simp [hnj])
      rw [this, prodFin_const]
    rw [hL, hR, Int.one_mul]; rfl

theorem neg_one_pow_two_pow (k : Nat) (hk : 1 ≤ k) : (-1 : Int) ^ (2 ^ k) = 1 := by
  have : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
    have hk' : k = (k - 1) + 1 := by omega
    conv => lhs; rw [hk']; rw [pow2_eq_add]
  rw [this, Int.pow_add]
  have h1 : ∀ n : Nat, (-1 : Int) ^ n * (-1 : Int) ^ n = 1 := by
    intro n; induction n with
    | zero => rfl
    | succ t ih => simp only [Int.pow_succ]; calc
        (-1 : Int) ^ t * (-1 : Int) * ((-1 : Int) ^ t * (-1 : Int)) = ((-1 : Int) ^ t * (-1 : Int) ^ t) * ((-1 : Int) * (-1 : Int)) := by ac_rfl
        _ = 1 := by rw [ih]; decide
  exact h1 (2 ^ (k - 1))

theorem grayWalsh_compl_entry (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    sgnInt (2 ^ (k + 1) - 1 - x) (2 ^ (k + 1) - 1 - y) *
    paritySign (gray (2 ^ (k + 1) - 1 - x) &&& gray (2 ^ (k + 1) - 1 - y)) =
    sgnInt x y * paritySign (gray x &&& gray y) := by
  have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := pow2_eq_add k
  have hx' : x < 2 ^ (k + 1) := by omega
  have hy' : y < 2 ^ (k + 1) := by omega
  rw [gray_compl k x hx', gray_compl k y hy']
  have hgx : gray x < 2 ^ k := gray_lt_pow2 k x hx
  have hgy : gray y < 2 ^ k := gray_lt_pow2 k y hy
  have hxor_add : ∀ z : Nat, z < 2 ^ k → 2 ^ k ^^^ z = 2 ^ k + z := by
    intro z hz; apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_xor, Nat.testBit_two_pow, testBit_add_pow2 k z hz i]
    by_cases hik : i = k
    · rw [hik, testBit_lt_pow2 k z hz k (Nat.le_refl k)]; simp
    · have hki : k ≠ i := Ne.symm hik; simp [hik, hki]
  rw [hxor_add _ hgx, hxor_add _ hgy, and_add_pow2_both k _ _ hgx hgy]
  have hand_lt : (gray x &&& gray y) < 2 ^ k := by
    apply lt_pow2_of_testBit; intro i hi
    rw [Nat.testBit_and, testBit_lt_pow2 k (gray x) hgx i hi]; rfl
  rw [paritySign_add_pow2 k _ hand_lt]
  have hsgn : sgnInt (2 ^ (k + 1) - 1 - x) (2 ^ (k + 1) - 1 - y) = -sgnInt x y := by
    unfold sgnInt
    by_cases h1 : x < y
    · have h2 : ¬ (2 ^ (k + 1) - 1 - x < 2 ^ (k + 1) - 1 - y) := by omega
      have h3 : 2 ^ (k + 1) - 1 - y < 2 ^ (k + 1) - 1 - x := by omega
      simp [h1, h2, h3]
    · by_cases h2 : y < x
      · have h3 : 2 ^ (k + 1) - 1 - x < 2 ^ (k + 1) - 1 - y := by omega
        simp [h1, h2, h3]
      · have h3 : ¬ (2 ^ (k + 1) - 1 - x < 2 ^ (k + 1) - 1 - y) := by omega
        have h4 : ¬ (2 ^ (k + 1) - 1 - y < 2 ^ (k + 1) - 1 - x) := by omega
        simp [h1, h2, h3, h4]
  rw [hsgn, Int.neg_mul, Int.mul_neg, Int.neg_neg]

def skewWalshMat (k : Nat) : Mat (2 ^ k) :=
  fun i j => sgnInt i.val j.val * paritySign (i.val &&& j.val)

end SiliconPfaffian

-- ============================================================================
-- Axiom Verification Receipts (All Main Mechanisms, Theorems, & Witnesses)
-- ============================================================================
