import BruhatTitsCarryGaugeAutomata.Defs

namespace BruhatTitsCarryEngine
theorem sumFin_zero_fn (d : Nat) : sumFin d (fun _ => 0) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [sumFin, ih]

theorem sumFin_congr {d : Nat} {f g : Fin d → Int} (h : ∀ i, f i = g i) :
    sumFin d f = sumFin d g := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [sumFin]
    rw [ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩), h ⟨d, Nat.lt_succ_self d⟩]

theorem sumFin_add {d : Nat} (f g : Fin d → Int) :
    sumFin d (fun i => f i + g i) = sumFin d f + sumFin d g := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [sumFin]
    rw [ih]
    omega

theorem sumFin_mul_left {d : Nat} (c : Int) (f : Fin d → Int) :
    sumFin d (fun i => c * f i) = c * sumFin d f := by
  induction d with
  | zero => simp [sumFin]
  | succ d ih =>
    simp only [sumFin]
    rw [ih, Int.mul_add]

theorem sumFin_mul_right {d : Nat} (f : Fin d → Int) (c : Int) :
    sumFin d (fun i => f i * c) = sumFin d f * c := by
  induction d with
  | zero => simp [sumFin]
  | succ d ih =>
    simp only [sumFin]
    rw [ih, Int.add_mul]

theorem sumFin_comm {d1 d2 : Nat} (f : Fin d1 → Fin d2 → Int) :
    sumFin d1 (fun i => sumFin d2 (fun j => f i j)) =
    sumFin d2 (fun j => sumFin d1 (fun i => f i j)) := by
  induction d1 with
  | zero =>
    simp only [sumFin]
    exact (sumFin_zero_fn d2).symm
  | succ d1 ih1 =>
    simp only [sumFin]
    rw [ih1, ← sumFin_add]

theorem matVec_matMul {d : Nat} (A B : Mat d) (v : Vec d) :
    matVec (matMul A B) v = matVec A (matVec B v) := by
  funext i
  simp only [matVec, matMul]
  calc
    sumFin d (fun j => sumFin d (fun k => A i k * B k j) * v j)
        = sumFin d (fun j => sumFin d (fun k => (A i k * B k j) * v j)) := by
          apply sumFin_congr; intro j; rw [← sumFin_mul_right]
    _ = sumFin d (fun k => sumFin d (fun j => (A i k * B k j) * v j)) := sumFin_comm _
    _ = sumFin d (fun k => sumFin d (fun j => A i k * (B k j * v j))) := by
          apply sumFin_congr; intro k; apply sumFin_congr; intro j; rw [Int.mul_assoc]
    _ = sumFin d (fun k => A i k * sumFin d (fun j => B k j * v j)) := by
          apply sumFin_congr; intro k; rw [sumFin_mul_left]

theorem matVec_scale {d : Nat} (M : Mat d) (s : Int) (v : Vec d) :
    matVec M (vecScale s v) = vecScale s (matVec M v) := by
  funext i
  simp only [matVec, vecScale]
  calc
    sumFin d (fun j => M i j * (s * v j))
        = sumFin d (fun j => s * (M i j * v j)) := by
          apply sumFin_congr; intro j
          rw [← Int.mul_assoc, Int.mul_comm (M i j) s, Int.mul_assoc]
    _ = s * sumFin d (fun j => M i j * v j) := sumFin_mul_left s _

theorem matVec_matScale {d : Nat} (s : Int) (M : Mat d) (v : Vec d) :
    matVec (matScale s M) v = vecScale s (matVec M v) := by
  funext i
  simp only [matVec, matScale, vecScale]
  calc
    sumFin d (fun j => (s * M i j) * v j)
        = sumFin d (fun j => s * (M i j * v j)) := by
          apply sumFin_congr; intro j; rw [Int.mul_assoc]
    _ = s * sumFin d (fun j => M i j * v j) := sumFin_mul_left s _

theorem sumFin_mod_congr {d : Nat} (m : Int) {f g : Fin d → Int}
    (h : ∀ i, f i % m = g i % m) :
    (sumFin d f) % m = (sumFin d g) % m := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [sumFin]
    have h1 := ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have h2 := h ⟨d, Nat.lt_succ_self d⟩
    rw [Int.add_emod, h1, h2, ← Int.add_emod]

theorem matVec_mod_congr {d : Nat} (m : Int) (M : Mat d) {u v : Vec d}
    (h : ∀ j, u j % m = v j % m) :
    ∀ i, (matVec M u i) % m = (matVec M v i) % m := by
  intro i
  simp only [matVec]
  apply sumFin_mod_congr
  intro j
  rw [Int.mul_emod, h j, ← Int.mul_emod]

/-- Binary induction on `Nat`: zero, and `2 * n + bit`. -/
theorem nat_bit_ind (P : Nat → Prop) (h0 : P 0)
    (hstep : ∀ n (b : Bool), P n → P (2 * n + if b then 1 else 0)) :
    ∀ n, P n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; exact h0
    · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have hp := ih (n / 2) hlt
      by_cases hpar : n % 2 = 0
      · have hstep0 := hstep (n / 2) false hp
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hstep0
        have heq : 2 * (n / 2) = n := by omega
        rwa [heq] at hstep0
      · have hstep1 := hstep (n / 2) true hp
        simp only [↓reduceIte] at hstep1
        have heq : 2 * (n / 2) + 1 = n := by omega
        rwa [heq] at hstep1

theorem bitFoldFuel_eq {α : Type} (init : α) (step : α → Bool → α) :
    ∀ fuel1 fuel2 n, n ≤ fuel1 → n ≤ fuel2 →
      bitFoldFuel init step fuel1 n = bitFoldFuel init step fuel2 n := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 n h1 _
    have hn : n = 0 := by omega
    subst hn
    cases fuel2 <;> simp [bitFoldFuel]
  | succ fuel1 ih =>
    intro fuel2 n h1 h2
    cases fuel2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [bitFoldFuel]
    | succ fuel2 =>
      simp only [bitFoldFuel]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        have hq1 : n / 2 ≤ fuel1 := by omega
        have hq2 : n / 2 ≤ fuel2 := by omega
        rw [ih fuel2 (n / 2) hq1 hq2]

theorem bitFold_zero {α : Type} (init : α) (step : α → Bool → α) :
    bitFold init step 0 = init := rfl

theorem bitFold_step {α : Type} (init : α) (step : α → Bool → α)
    (h0 : step init false = init) (n : Nat) (b : Bool) :
    bitFold init step (2 * n + if b then 1 else 0) = step (bitFold init step n) b := by
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    by_cases hn : n = 0
    · subst hn; simp [bitFold_zero, h0]
    · have h2n_ne : 2 * n ≠ 0 := by omega
      have hfuel : bitFold init step (2 * n) = bitFoldFuel init step (2 * n - 1 + 1) (2 * n) := by
        unfold bitFold
        have heq : 2 * n - 1 + 1 = 2 * n := by omega
        rw [heq]
      rw [hfuel]
      simp only [bitFoldFuel, h2n_ne, ↓reduceIte]
      have hdiv : (2 * n) / 2 = n := by omega
      have hmod : decide ((2 * n) % 2 = 1) = false := decide_eq_false (by omega)
      rw [hdiv, hmod]
      have hle : n ≤ 2 * n - 1 := by omega
      rw [bitFoldFuel_eq init step (2 * n - 1) n n hle (Nat.le_refl n)]
      rfl
  | true =>
    simp only [↓reduceIte]
    have h2n1_ne : 2 * n + 1 ≠ 0 := by omega
    unfold bitFold
    simp only [bitFoldFuel, h2n1_ne, ↓reduceIte]
    have hdiv : (2 * n + 1) / 2 = n := by omega
    have hmod : decide ((2 * n + 1) % 2 = 1) = true := by
      have h1 : (2 * n + 1) % 2 = 1 := by omega
      rw [h1]; rfl
    rw [hdiv, hmod]
    have hle : n ≤ 2 * n := by omega
    rw [bitFoldFuel_eq init step (2 * n) n n hle (Nat.le_refl n)]

theorem evalMat_zero {d : Nat} (M0 M1 : Mat d) (v0 : Vec d) :
    evalMat M0 M1 v0 0 = v0 := rfl

theorem evalMat_step {d : Nat} (M0 M1 : Mat d) (v0 : Vec d) (h0 : matVec M0 v0 = v0)
    (n : Nat) (b : Bool) :
    evalMat M0 M1 v0 (2 * n + if b then 1 else 0) =
      matVec (if b then M1 else M0) (evalMat M0 M1 v0 n) :=
  bitFold_step v0 (fun v b => matVec (if b then M1 else M0) v) h0 n b

theorem ExactVal2.unique {x : Int} {e1 e2 : Nat}
    (h1 : ExactVal2 x e1) (h2 : ExactVal2 x e2) : e1 = e2 := by
  rcases h1 with ⟨m1, hx1, hm1⟩
  rcases h2 with ⟨m2, hx2, hm2⟩
  have heq : (2 : Int) ^ e1 * m1 = (2 : Int) ^ e2 * m2 := by rw [← hx1, ← hx2]
  have aux : ∀ a b : Nat, ∀ u v : Int,
      (2 : Int) ^ a * u = (2 : Int) ^ b * v → u % 2 = 1 → v % 2 = 1 → a = b := by
    intro a
    induction a with
    | zero =>
      intro b u v heq hu hv
      cases b with
      | zero => rfl
      | succ b =>
        simp only [Int.pow_zero, Int.one_mul, Int.pow_succ] at heq
        rw [Int.mul_right_comm] at heq
        omega
    | succ a ih =>
      intro b u v heq hu hv
      cases b with
      | zero =>
        simp only [Int.pow_zero, Int.one_mul, Int.pow_succ] at heq
        rw [Int.mul_right_comm] at heq
        omega
      | succ b =>
        simp only [Int.pow_succ] at heq
        rw [Int.mul_right_comm ((2 : Int) ^ a) 2 u, Int.mul_right_comm ((2 : Int) ^ b) 2 v] at heq
        have hcancel : (2 : Int) ^ a * u = (2 : Int) ^ b * v := by omega
        have := ih b u v hcancel hu hv
        omega
  exact aux e1 e2 m1 m2 heq hm1 hm2

theorem two_pow_pos (e : Nat) : 0 < (2 : Int) ^ e := by
  induction e with
  | zero => decide
  | succ e ih => rw [Int.pow_succ]; exact Int.mul_pos ih (by decide)

theorem ExactVal2.ne_zero {x : Int} {e : Nat} (h : ExactVal2 x e) : x ≠ 0 := by
  rcases h with ⟨m, rfl, hm⟩
  have hpow : 0 < (2 : Int) ^ e := two_pow_pos e
  intro hz
  rcases Int.mul_eq_zero.mp hz with h0 | h0
  · omega
  · omega

theorem exactVal2_zero_iff (x : Int) : ExactVal2 x 0 ↔ x % 2 = 1 := by
  constructor
  · rintro ⟨m, rfl, hm⟩; simp [hm]
  · intro hx; exact ⟨x, by simp, hx⟩

theorem exactVal2_one_iff (x : Int) : ExactVal2 x 1 ↔ x % 4 = 2 := by
  constructor
  · rintro ⟨m, rfl, hm⟩; simp only [Int.pow_one]; omega
  · intro hx; exact ⟨x / 2, by simp only [Int.pow_one]; omega, by omega⟩

theorem exactVal2_two_iff (x : Int) : ExactVal2 x 2 ↔ x % 8 = 4 := by
  constructor
  · rintro ⟨m, rfl, hm⟩; change (4 * m) % 8 = 4; omega
  · intro hx; exact ⟨x / 4, by change x = 4 * (x / 4); omega, by omega⟩

theorem exactVal2_three_iff (x : Int) : ExactVal2 x 3 ↔ x % 16 = 8 := by
  constructor
  · rintro ⟨m, rfl, hm⟩; change (8 * m) % 16 = 8; omega
  · intro hx; exact ⟨x / 8, by change x = 8 * (x / 8); omega, by omega⟩

-- Small core-Lean Fin elimination helpers (zero Mathlib dependency)
theorem fin8_all {P : Fin 8 → Prop}
    (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩) (h2 : P ⟨2, by decide⟩) (h3 : P ⟨3, by decide⟩)
    (h4 : P ⟨4, by decide⟩) (h5 : P ⟨5, by decide⟩) (h6 : P ⟨6, by decide⟩) (h7 : P ⟨7, by decide⟩) :
    ∀ i, P i := by
  intro ⟨i, hi⟩
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | 5 => exact h5
  | 6 => exact h6
  | 7 => exact h7

-- ============================================================================
-- Section 2: First-Principles Combinatorial Grounding of Carry-Bounded Representations
-- ============================================================================

theorem carryMat_zero_fix (w : Nat → Int) (hw0 : w 0 = 1) (C : Nat) :
    matVec (carryMat w C false) (e0Vec C) = e0Vec C := by
  funext c
  simp only [matVec, carryMat, e0Vec, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  have hsum : ∀ (k : Nat) (f : Fin (k + 1) → Int),
      (∀ j : Fin (k + 1), j.val ≠ 0 → f j = 0) → sumFin (k + 1) f = f ⟨0, Nat.zero_lt_succ k⟩ := by
    intro k
    induction k with
    | zero =>
      intro f _; simp [sumFin]
    | succ k ih =>
      intro f hf
      simp only [sumFin]
      have hlast : f ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ = 0 :=
        hf ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ (Nat.succ_ne_zero k)
      rw [hlast, Int.add_zero]
      exact ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun j hj => hf ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ hj)
  rw [hsum C]
  · by_cases hc : c.val = 0
    · simp [hc, hw0]
    · have hnot : ¬ c.val ≤ 2 * 0 := by omega
      simp [hc, hnot]
  · intro j hj
    simp [hj]

/--
**First-Principles Combinatorial Equivalence Theorem**:
For ANY digit weight table `w` with `w 0 = 1`, ANY carry cap `C`, ANY bit-width `width`,
and ANY `n < 2 ^ width`, the direct combinatorial weighted count of carry-bounded representations
`carryCount w C width n c` equals the `(C + 1)`-dimensional binary matrix product
`evalMat (carryMat w C false) (carryMat w C true) (e0Vec C) n c`.
-/
theorem carryCount_eq_evalMat (w : Nat → Int) (hw0 : w 0 = 1) (C : Nat) :
    ∀ width n, n < 2 ^ width → ∀ c : Fin (C + 1),
      carryCount w C width n c.val =
        evalMat (carryMat w C false) (carryMat w C true) (e0Vec C) n c := by
  intro width
  induction width with
  | zero =>
    intro n hn c
    have hn0 : n = 0 := by simp at hn; omega
    subst hn0
    simp [carryCount, evalMat_zero, e0Vec]
  | succ width ih =>
    intro n hn c
    have hq : n / 2 < 2 ^ width := by
      have hpow : 2 ^ (width + 1) = 2 * 2 ^ width := by rw [Nat.pow_succ]; omega
      omega
    simp only [carryCount]
    have hrec : ∀ c' : Fin (C + 1),
        carryCount w C width (n / 2) c'.val =
        evalMat (carryMat w C false) (carryMat w C true) (e0Vec C) (n / 2) c' :=
      fun c' => ih (n / 2) hq c'
    by_cases hpar : n % 2 = 0
    · have hstep := evalMat_step (carryMat w C false) (carryMat w C true) (e0Vec C)
        (carryMat_zero_fix w hw0 C) (n / 2) false
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hstep
      have hn_eq : 2 * (n / 2) = n := by omega
      rw [hn_eq] at hstep
      rw [hstep]
      simp only [matVec]
      apply sumFin_congr
      intro c'
      rw [hrec c', hpar]
      unfold carryMat
      simp only [Bool.false_eq_true, ↓reduceIte]
      split <;> simp
    · have hmod1 : n % 2 = 1 := by omega
      have hstep := evalMat_step (carryMat w C false) (carryMat w C true) (e0Vec C)
        (carryMat_zero_fix w hw0 C) (n / 2) true
      simp only [↓reduceIte] at hstep
      have hn_eq : 2 * (n / 2) + 1 = n := by omega
      rw [hn_eq] at hstep
      rw [hstep]
      simp only [matVec]
      apply sumFin_congr
      intro c'
      rw [hrec c', hmod1]
      unfold carryMat
      simp only [↓reduceIte]
      split <;> simp

-- ============================================================================
-- Section 3: Reusable Infinite Proof Engine I — 2-Adic Bruhat–Tits Lattice-Gauge Engine
-- ============================================================================

namespace LatticeGaugeCert
variable {d K : Nat} {hd : 0 < d} {M0 M1 : Mat d} {v0 : Vec d}

theorem runState_zero (C : LatticeGaugeCert d K hd M0 M1 v0) :
    C.runState 0 = (C.q0, 0, C.u0) := rfl

theorem runState_step (C : LatticeGaugeCert d K hd M0 M1 v0) (n : Nat) (b : Bool) :
    C.runState (2 * n + if b then 1 else 0) =
      (C.delta (C.runQ n) b, C.runE n + C.eGain (C.runQ n) b, matVec (C.Mt (C.runQ n) b) (C.runU n)) := by
  have h0 : (C.delta C.q0 false, 0 + C.eGain C.q0 false, matVec (C.Mt C.q0 false) C.u0) = (C.q0, 0, C.u0) := by
    simp [C.hInit_q0, C.hInit_e0, C.hInit_u0]
  exact bitFold_step (C.q0, 0, C.u0)
    (fun (q, e, u) b => (C.delta q b, e + C.eGain q b, matVec (C.Mt q b) u)) h0 n b

theorem runQ_step (C : LatticeGaugeCert d K hd M0 M1 v0) (n : Nat) (b : Bool) :
    C.runQ (2 * n + if b then 1 else 0) = C.delta (C.runQ n) b := by
  simp [runQ, runState_step]

theorem runE_step (C : LatticeGaugeCert d K hd M0 M1 v0) (n : Nat) (b : Bool) :
    C.runE (2 * n + if b then 1 else 0) = C.runE n + C.eGain (C.runQ n) b := by
  simp [runE, runState_step]

theorem runU_step (C : LatticeGaugeCert d K hd M0 M1 v0) (n : Nat) (b : Bool) :
    C.runU (2 * n + if b then 1 else 0) = matVec (C.Mt (C.runQ n) b) (C.runU n) := by
  simp [runU, runState_step]

/-- **Master Engine Theorem 1 (Exact Lattice-Gauge Factorization, `∀ n : Nat`)**. -/
theorem factorization (C : LatticeGaugeCert d K hd M0 M1 v0) :
    ∀ n : Nat,
      evalMat M0 M1 v0 n = vecScale ((2 : Int) ^ (C.runE n)) (matVec (C.L (C.runQ n)) (C.runU n))
      ∧ C.parInv (C.runQ n) (C.runU n) := by
  apply nat_bit_ind
  · constructor
    · funext i
      simp only [evalMat_zero, runQ, runE, runU, runState_zero, vecScale, Int.pow_zero, Int.one_mul]
      exact congrFun C.hInit_vec i
    · exact C.hInit_inv
  · intro n b ⟨hvec, hinv⟩
    constructor
    · rw [evalMat_step M0 M1 v0 C.hM0_fix n b, hvec, matVec_scale, ← matVec_matMul,
          C.hGauge (C.runQ n) b, matVec_matScale, matVec_matMul,
          runE_step, runQ_step, runU_step]
      funext i
      simp only [vecScale]
      rw [← Int.mul_assoc, Int.pow_add]
    · rw [runQ_step, runU_step]
      exact C.hParStep (C.runQ n) b (C.runU n) hinv

/-- **Master Engine Theorem 2 (Exact Odd-Part Decomposition, `∀ n : Nat`)**. -/
theorem oddPart_decomp (C : LatticeGaugeCert d K hd M0 M1 v0) (n : Nat) :
    evalMat M0 M1 v0 n ⟨0, hd⟩ = (2 : Int) ^ (C.totalVal n) * C.oddPart n
    ∧ C.oddPart n % 2 = 1 := by
  rcases C.factorization n with ⟨hvec, hinv⟩
  constructor
  · have h0 := congrFun hvec ⟨0, hd⟩
    rw [h0]
    simp only [vecScale, matVec, totalVal, oddPart, dot]
    have hrow : sumFin d (fun j => C.L (C.runQ n) ⟨0, hd⟩ j * C.runU n j) =
        (2 : Int) ^ (C.aOff (C.runQ n)) *
          sumFin d (fun j => C.targetRow (C.runQ n) j * C.runU n j) := by
      calc
        sumFin d (fun j => C.L (C.runQ n) ⟨0, hd⟩ j * C.runU n j)
            = sumFin d (fun j => ((2 : Int) ^ (C.aOff (C.runQ n)) * C.targetRow (C.runQ n) j) * C.runU n j) := by
              apply sumFin_congr; intro j; rw [C.hTargetRow]
        _ = sumFin d (fun j => (2 : Int) ^ (C.aOff (C.runQ n)) * (C.targetRow (C.runQ n) j * C.runU n j)) := by
              apply sumFin_congr; intro j; rw [Int.mul_assoc]
        _ = (2 : Int) ^ (C.aOff (C.runQ n)) *
              sumFin d (fun j => C.targetRow (C.runQ n) j * C.runU n j) :=
              sumFin_mul_left _ _
    rw [hrow, ← Int.mul_assoc, Int.pow_add]
  · exact C.hTargetOdd (C.runQ n) (C.runU n) hinv

/-- **Master Engine Theorem 3 (Exact Unbounded 2-Adic Valuation Law, `∀ n : Nat`)**. -/
theorem exact_v2 (C : LatticeGaugeCert d K hd M0 M1 v0) (n : Nat) :
    ExactVal2 (evalMat M0 M1 v0 n ⟨0, hd⟩) (C.totalVal n) :=
  ⟨C.oddPart n, C.oddPart_decomp n⟩

end LatticeGaugeCert
namespace ModQuotientCert
variable {d K : Nat} {m : Int} {M0 M1 : Mat d} {v0 : Vec d}

theorem runQ_zero (C : ModQuotientCert d K m M0 M1 v0) : C.runQ 0 = C.q0 := rfl

theorem runQ_step (C : ModQuotientCert d K m M0 M1 v0) (n : Nat) (b : Bool) :
    C.runQ (2 * n + if b then 1 else 0) = C.delta (C.runQ n) b :=
  bitFold_step C.q0 C.delta C.hInit_q0 n b

/-- **Master Engine Theorem 4 (Exact Modular Quotient Soundness, `∀ n : Nat`)**. -/
theorem sound (C : ModQuotientCert d K m M0 M1 v0) :
    ∀ n i, evalMat M0 M1 v0 n i % m = C.phi (C.runQ n) i % m := by
  apply nat_bit_ind
  · intro i; rw [evalMat_zero, runQ_zero]; exact C.hInit_phi i
  · intro n b ih i
    rw [evalMat_step M0 M1 v0 C.hM0_fix n b, runQ_step]
    have h1 := matVec_mod_congr m (if b then M1 else M0) ih i
    rw [h1, C.hStep]

end ModQuotientCert
theorem carryMat_eq_M2 (w1 w2 w3 : Int) :
    carryMat (w2Fun w1 w2 w3) 1 false = M2_0 w1 w2 ∧
    carryMat (w2Fun w1 w2 w3) 1 true = M2_1 w1 w2 w3 ∧
    e0Vec 1 = v2_0 := by
  refine ⟨?_, ?_, ?_⟩
  · funext i j; revert i j; apply fin2_all <;> (apply fin2_all <;> rfl)
  · funext i j; revert i j; apply fin2_all <;> (apply fin2_all <;> rfl)
  · funext i; revert i; apply fin2_all <;> rfl

/-- Direct combinatorial identity for 1-bit-carry weighted `{0,1,2,3}`-representations. -/
theorem carryCount_eq_f2 (w1 w2 w3 : Int) (width n : Nat) (hn : n < 2 ^ width) :
    carryCount (w2Fun w1 w2 w3) 1 width n 0 = f2 w1 w2 w3 n := by
  have h := carryCount_eq_evalMat (w2Fun w1 w2 w3) rfl 1 width n hn ⟨0, by decide⟩
  rcases carryMat_eq_M2 w1 w2 w3 with ⟨h0, h1, hv⟩
  rw [h0, h1, hv] at h
  exact h

theorem runQE3_step (n : Nat) (b : Bool) :
    runQE3 (2 * n + if b then 1 else 0) = (delta2 (runQ3 n) b, runE3 n + eGain2 (runQ3 n) b) :=
  bitFold_step (⟨0, by decide⟩, 0) (fun (q, e) b => (delta2 q b, e + eGain2 q b)) rfl n b

theorem runQ3_step (n : Nat) (b : Bool) :
    runQ3 (2 * n + if b then 1 else 0) = delta2 (runQ3 n) b := by
  simp [runQ3, runQE3_step]

theorem runE3_step (n : Nat) (b : Bool) :
    runE3 (2 * n + if b then 1 else 0) = runE3 n + eGain2 (runQ3 n) b := by
  simp [runE3, runQE3_step]

theorem runQ3_ne_zero_of_pos : ∀ n, 0 < n → runQ3 n ≠ ⟨0, by decide⟩ := by
  have hstep0 : ∀ q : Fin 3, q ≠ ⟨0, by decide⟩ → delta2 q false ≠ ⟨0, by decide⟩ := by decide
  have hstep1 : ∀ q : Fin 3, delta2 q true ≠ ⟨0, by decide⟩ := by decide
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hpos
    by_cases h1 : n = 1
    · subst h1; decide
    · have hqpos : 0 < n / 2 := by omega
      have hlt : n / 2 < n := Nat.div_lt_self hpos (by decide)
      have hne := ih (n / 2) hlt hqpos
      by_cases hpar : n % 2 = 0
      · have hs := runQ3_step (n / 2) false
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hs
        have heq : 2 * (n / 2) = n := by omega
        rw [heq] at hs; rw [hs]
        exact hstep0 (runQ3 (n / 2)) hne
      · have hs := runQ3_step (n / 2) true
        simp only [↓reduceIte] at hs
        have heq : 2 * (n / 2) + 1 = n := by omega
        rw [heq] at hs; rw [hs]
        exact hstep1 (runQ3 (n / 2))

/-- Helper: parity of linear combination `(2*c + 1) * x + (2*d) * y` when `x % 2 = 1`. -/
private theorem odd_lin2 (c d x y : Int) (hx : x % 2 = 1) :
    ((2 * c + 1) * x + (2 * d) * y) % 2 = 1 := by
  rw [Int.add_mul, Int.one_mul, Int.mul_assoc, Int.mul_assoc]
  omega

theorem cert2Param_runQE_eq (a1 a2 s : Int) :
    ∀ n : Nat, ((cert2Param a1 a2 s).runQ n, (cert2Param a1 a2 s).runE n) = runQE3 n := by
  apply nat_bit_ind
  · rfl
  · intro n b ih
    have ihq : (cert2Param a1 a2 s).runQ n = runQ3 n := congrArg Prod.fst ih
    have ihe : (cert2Param a1 a2 s).runE n = runE3 n := congrArg Prod.snd ih
    rw [(cert2Param a1 a2 s).runQ_step, (cert2Param a1 a2 s).runE_step, runQE3_step, ihq, ihe]
    rfl

theorem cert2Param_totalVal_eq (a1 a2 s : Int) (n : Nat) :
    (cert2Param a1 a2 s).totalVal n = phi3 n := by
  have h := cert2Param_runQE_eq a1 a2 s n
  have hq : (cert2Param a1 a2 s).runQ n = runQ3 n := congrArg Prod.fst h
  have he : (cert2Param a1 a2 s).runE n = runE3 n := congrArg Prod.snd h
  rw [LatticeGaugeCert.totalVal, phi3, hq, he]
  rfl

/--
**Infinite Theorem A1 (2×2 Exact Unbounded 2-Adic Valuation Law)**:
For ALL `(w1, w2, w3) ∈ ℤ³` with `w1 % 4 = 3 ∧ w2 % 4 = 3 ∧ w3 % 4 = 1 ∧ (w1 + w2 + w3) % 8 = 7`,
`∀ n : Nat, ExactVal2 (f2 w1 w2 w3 n) (phi3 n)`.
-/
theorem thm_2x2_exact_v2 (w1 w2 w3 : Int)
    (h1 : w1 % 4 = 3) (h2 : w2 % 4 = 3) (h3 : w3 % 4 = 1) (hs : (w1 + w2 + w3) % 8 = 7) :
    ∀ n : Nat, ExactVal2 (f2 w1 w2 w3 n) (phi3 n) := by
  have hw1 : w1 = 4 * (w1 / 4) + 3 := by omega
  have hw2 : w2 = 4 * (w2 / 4) + 3 := by omega
  have hw3 : w3 = 8 * ((w1 + w2 + w3 - 7) / 8) - 4 * (w1 / 4) - 4 * (w2 / 4) + 1 := by omega
  intro n
  have h := (cert2Param (w1 / 4) (w2 / 4) ((w1 + w2 + w3 - 7) / 8)).exact_v2 n
  rw [cert2Param_totalVal_eq] at h
  rw [f2, hw1, hw2, hw3]
  exact h

/-- **Infinite Theorem A2 (Sibling Valuation Symmetry, `∀ n ≥ 1`)**. -/
theorem thm_2x2_sibling_v2_symmetry (n : Nat) (hn : 0 < n) :
    phi3 (2 * n) = phi3 (2 * n + 1) := by
  have hne := runQ3_ne_zero_of_pos n hn
  have hq0 := runQ3_step n false
  have hq1 := runQ3_step n true
  have he0 := runE3_step n false
  have he1 := runE3_step n true
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hq0 he0
  simp only [↓reduceIte] at hq1 he1
  simp only [phi3, hq0, hq1, he0, he1]
  have aux : ∀ q : Fin 3, q ≠ ⟨0, by decide⟩ →
      runE3 n + eGain2 q false + aOff2 (delta2 q false) =
      runE3 n + eGain2 q true + aOff2 (delta2 q true) := by
    apply fin3_all
    · intro h; exact absurd rfl h
    · intro _; rfl
    · intro _; rfl
  exact aux (runQ3 n) hne

/--
**Infinite Theorem A3 (Sibling Odd-Part Mod-4 Antithesis, `∀ n ≥ 1`)**:
Across the ENTIRE 3-parameter 2×2 family, the exact odd parts of `f_w(2n)` and `f_w(2n+1)` satisfy
`odd_2(f_w(2n)) + odd_2(f_w(2n+1)) ≡ 0 (mod 4)` for EVERY `n ≥ 1`.
-/
theorem thm_2x2_oddPart_mod4_antithesis (a1 a2 s : Int) (n : Nat) (hn : 0 < n) :
    ((cert2Param a1 a2 s).oddPart (2 * n) + (cert2Param a1 a2 s).oddPart (2 * n + 1)) % 4 = 0 := by
  have hne : (cert2Param a1 a2 s).runQ n ≠ ⟨0, by decide⟩ := by
    have hq : (cert2Param a1 a2 s).runQ n = runQ3 n := congrArg Prod.fst (cert2Param_runQE_eq a1 a2 s n)
    rw [hq]; exact runQ3_ne_zero_of_pos n hn
  have hq0 := (cert2Param a1 a2 s).runQ_step n false
  have hq1 := (cert2Param a1 a2 s).runQ_step n true
  have hu0 := (cert2Param a1 a2 s).runU_step n false
  have hu1 := (cert2Param a1 a2 s).runU_step n true
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hq0 hu0
  simp only [↓reduceIte] at hq1 hu1
  simp only [LatticeGaugeCert.oddPart, hq0, hq1, hu0, hu1]
  have aux : ∀ (q : Fin 3) (u : Vec 2), q ≠ ⟨0, by decide⟩ →
      (dot (targetRow2 (delta2 q false)) (matVec (Mt2 a1 a2 s q false) u)
     + dot (targetRow2 (delta2 q true))  (matVec (Mt2 a1 a2 s q true)  u)) % 4 = 0 := by
    apply fin3_all
    · intro _ h; exact absurd rfl h
    · intro u _
      simp only [delta2, targetRow2, dot, matVec, sumFin, Mt2]
      generalize u ⟨0, by decide⟩ = x
      generalize u ⟨1, by decide⟩ = y
      have hfac :
          (0 + 1 * (0 + (6 + 8 * a1) * x + (-3 - 4 * a1) * y) +
               2 * (0 + (-1 - 4 * a1 + 2 * a2) * x + (1 + 2 * a1 - a2) * y)) +
          (0 + 2 * (0 + (2 + 2 * s) * x + (a1 - s) * y) +
               1 * (0 + (-4 * a2 + 4 * s) * x + (1 + 2 * a1 + 2 * a2 - 2 * s) * y))
          = 4 * ((2 + 2 * s) * x + (a1 - s) * y) := by
        have hr : 4 * ((2 + 2 * s) * x + (a1 - s) * y) =
            (4 * (2 + 2 * s)) * x + (4 * (a1 - s)) * y := by
          rw [Int.mul_add, ← Int.mul_assoc, ← Int.mul_assoc]
        have hl :
            (0 + 1 * (0 + (6 + 8 * a1) * x + (-3 - 4 * a1) * y) +
                 2 * (0 + (-1 - 4 * a1 + 2 * a2) * x + (1 + 2 * a1 - a2) * y)) +
            (0 + 2 * (0 + (2 + 2 * s) * x + (a1 - s) * y) +
                 1 * (0 + (-4 * a2 + 4 * s) * x + (1 + 2 * a1 + 2 * a2 - 2 * s) * y))
            = ((6 + 8 * a1) + 2 * (-1 - 4 * a1 + 2 * a2) + 2 * (2 + 2 * s) + (-4 * a2 + 4 * s)) * x
            + ((-3 - 4 * a1) + 2 * (1 + 2 * a1 - a2) + 2 * (a1 - s) + (1 + 2 * a1 + 2 * a2 - 2 * s)) * y := by
          simp only [Int.zero_add, Int.one_mul, Int.mul_add, Int.add_mul, Int.mul_assoc]
          omega
        rw [hl, hr]
        have hx : (6 + 8 * a1) + 2 * (-1 - 4 * a1 + 2 * a2) + 2 * (2 + 2 * s) + (-4 * a2 + 4 * s) =
            4 * (2 + 2 * s) := by omega
        have hy : (-3 - 4 * a1) + 2 * (1 + 2 * a1 - a2) + 2 * (a1 - s) + (1 + 2 * a1 + 2 * a2 - 2 * s) =
            4 * (a1 - s) := by omega
        rw [hx, hy]
      rw [hfac]; omega
    · intro u _
      simp only [delta2, targetRow2, dot, matVec, sumFin, Mt2]
      generalize u ⟨0, by decide⟩ = x
      generalize u ⟨1, by decide⟩ = y
      have hfac :
          (0 + 2 * (0 + (2 + a1 + a2) * x + 1 * y) +
               1 * (0 + (1 - 2 * a1 + 2 * a2) * x + 2 * y)) +
          (0 + 2 * (0 + (3 + a1 + 2 * s) * x + (4 + 4 * a1) * y) +
               1 * (0 + (1 + 2 * a1 - 4 * a2 + 4 * s) * x + (4 + 8 * a1) * y))
          = 4 * ((3 + a1 + 2 * s) * x + (4 + 4 * a1) * y) := by
        have hr : 4 * ((3 + a1 + 2 * s) * x + (4 + 4 * a1) * y) =
            (4 * (3 + a1 + 2 * s)) * x + (4 * (4 + 4 * a1)) * y := by
          rw [Int.mul_add, ← Int.mul_assoc, ← Int.mul_assoc]
        have hl :
            (0 + 2 * (0 + (2 + a1 + a2) * x + 1 * y) +
                 1 * (0 + (1 - 2 * a1 + 2 * a2) * x + 2 * y)) +
            (0 + 2 * (0 + (3 + a1 + 2 * s) * x + (4 + 4 * a1) * y) +
                 1 * (0 + (1 + 2 * a1 - 4 * a2 + 4 * s) * x + (4 + 8 * a1) * y))
            = (2 * (2 + a1 + a2) + (1 - 2 * a1 + 2 * a2) + 2 * (3 + a1 + 2 * s) + (1 + 2 * a1 - 4 * a2 + 4 * s)) * x
            + (2 * 1 + 2 + 2 * (4 + 4 * a1) + (4 + 8 * a1)) * y := by
          simp only [Int.zero_add, Int.one_mul, Int.mul_add, Int.add_mul, Int.mul_assoc]
          omega
        rw [hl, hr]
        have hx : 2 * (2 + a1 + a2) + (1 - 2 * a1 + 2 * a2) + 2 * (3 + a1 + 2 * s) + (1 + 2 * a1 - 4 * a2 + 4 * s) =
            4 * (3 + a1 + 2 * s) := by omega
        have hy : 2 * 1 + 2 + 2 * (4 + 4 * a1) + (4 + 8 * a1) = 4 * (4 + 4 * a1) := by omega
        rw [hx, hy]
      rw [hfac]; omega
  exact aux ((cert2Param a1 a2 s).runQ n) ((cert2Param a1 a2 s).runU n) hne

private theorem f2_eval_12378 (w1 w2 w3 : Int) :
    f2 w1 w2 w3 1 = w1 ∧
    f2 w1 w2 w3 2 = w1 + w2 ∧
    f2 w1 w2 w3 3 = w1 * w1 + w3 ∧
    f2 w1 w2 w3 7 = w1 * (w1 * w1 + w3) + w3 * (w1 + w2) ∧
    f2 w1 w2 w3 8 = w1 + w2 + w2 * w1 + w2 * (w1 * w1) := by
  have hfix : matVec (M2_0 w1 w2) v2_0 = v2_0 := by
    funext i; revert i; apply fin2_all <;> simp [matVec, sumFin, M2_0, v2_0]
  have h0 : evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 0 = v2_0 := evalMat_zero _ _ _
  have h1 : evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 1 = matVec (M2_1 w1 w2 w3) v2_0 := by
    simpa [h0] using evalMat_step (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 hfix 0 true
  have h2 : evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 2 =
      matVec (M2_0 w1 w2) (evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 1) := by
    simpa using evalMat_step (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 hfix 1 false
  have h3 : evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 3 =
      matVec (M2_1 w1 w2 w3) (evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 1) := by
    simpa using evalMat_step (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 hfix 1 true
  have h4 : evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 4 =
      matVec (M2_0 w1 w2) (evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 2) := by
    simpa using evalMat_step (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 hfix 2 false
  have h7 : evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 7 =
      matVec (M2_1 w1 w2 w3) (evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 3) := by
    simpa using evalMat_step (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 hfix 3 true
  have h8 : evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 8 =
      matVec (M2_0 w1 w2) (evalMat (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 4) := by
    simpa using evalMat_step (M2_0 w1 w2) (M2_1 w1 w2 w3) v2_0 hfix 4 false
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [f2, h1, matVec, sumFin, M2_1, v2_0]
  · simp [f2, h2, h1, matVec, sumFin, M2_0, M2_1, v2_0]
  · simp [f2, h3, h1, matVec, sumFin, M2_1, v2_0]
  · simp [f2, h7, h3, h1, matVec, sumFin, M2_1, v2_0]
  · simp [f2, h8, h4, h2, h1, matVec, sumFin, M2_0, M2_1, v2_0]

private theorem mod8_add {a a' b b' : Int} (ha : a % 8 = a' % 8) (hb : b % 8 = b' % 8) :
    (a + b) % 8 = (a' + b') % 8 := by
  rw [Int.add_emod, ha, hb, ← Int.add_emod]

private theorem mod8_mul {a a' b b' : Int} (ha : a % 8 = a' % 8) (hb : b % 8 = b' % 8) :
    (a * b) % 8 = (a' * b') % 8 := by
  rw [Int.mul_emod, ha, hb, ← Int.mul_emod]

private theorem rigidity2_mod8_table :
    ∀ r1 r2 r3 : Fin 8,
      (r1.val : Int) % 2 = 1 →
      ((r1.val : Int) + (r2.val : Int)) % 4 = 2 →
      ((r1.val : Int) * (r1.val : Int) + (r3.val : Int)) % 4 = 2 →
      ((r1.val : Int) * ((r1.val : Int) * (r1.val : Int) + (r3.val : Int)) +
        (r3.val : Int) * ((r1.val : Int) + (r2.val : Int))) % 8 = 4 →
      ((r1.val : Int) + (r2.val : Int) + (r2.val : Int) * (r1.val : Int) +
        (r2.val : Int) * ((r1.val : Int) * (r1.val : Int))) % 4 = 2 →
      (r1.val : Int) % 4 = 3 ∧ (r2.val : Int) % 4 = 3 ∧ (r3.val : Int) % 4 = 1 ∧
        ((r1.val : Int) + (r2.val : Int) + (r3.val : Int)) % 8 = 7 := by
  decide

/--
**Infinite Theorem A4 (2×2 5-Point Finite-to-Infinite 2-Adic Rigidity IFF)**:
For ANY integer weights `(1, w1, w2, w3)`, matching `ExactVal2 (f2 w1 w2 w3 n) (phi3 n)` on
ALL `n : Nat` is equivalent to matching on just the 5 points `{1, 2, 3, 7, 8}`, and equivalent
to the exact mod-8 congruence `w1 % 4 = 3 ∧ w2 % 4 = 3 ∧ w3 % 4 = 1 ∧ (w1 + w2 + w3) % 8 = 7`.
-/
theorem thm_2x2_5point_rigidity (w1 w2 w3 : Int) :
    ((∀ n : Nat, ExactVal2 (f2 w1 w2 w3 n) (phi3 n)) ↔
     (ExactVal2 (f2 w1 w2 w3 1) (phi3 1) ∧
      ExactVal2 (f2 w1 w2 w3 2) (phi3 2) ∧
      ExactVal2 (f2 w1 w2 w3 3) (phi3 3) ∧
      ExactVal2 (f2 w1 w2 w3 7) (phi3 7) ∧
      ExactVal2 (f2 w1 w2 w3 8) (phi3 8)))
    ∧
    ((ExactVal2 (f2 w1 w2 w3 1) (phi3 1) ∧
      ExactVal2 (f2 w1 w2 w3 2) (phi3 2) ∧
      ExactVal2 (f2 w1 w2 w3 3) (phi3 3) ∧
      ExactVal2 (f2 w1 w2 w3 7) (phi3 7) ∧
      ExactVal2 (f2 w1 w2 w3 8) (phi3 8)) ↔
     (w1 % 4 = 3 ∧ w2 % 4 = 3 ∧ w3 % 4 = 1 ∧ (w1 + w2 + w3) % 8 = 7)) := by
  have h5_to_cong :
      (ExactVal2 (f2 w1 w2 w3 1) (phi3 1) ∧
       ExactVal2 (f2 w1 w2 w3 2) (phi3 2) ∧
       ExactVal2 (f2 w1 w2 w3 3) (phi3 3) ∧
       ExactVal2 (f2 w1 w2 w3 7) (phi3 7) ∧
       ExactVal2 (f2 w1 w2 w3 8) (phi3 8)) →
      (w1 % 4 = 3 ∧ w2 % 4 = 3 ∧ w3 % 4 = 1 ∧ (w1 + w2 + w3) % 8 = 7) := by
    intro ⟨hv1, hv2, hv3, hv7, hv8⟩
    have hp1 : phi3 1 = 0 := rfl
    have hp2 : phi3 2 = 1 := rfl
    have hp3 : phi3 3 = 1 := rfl
    have hp7 : phi3 7 = 2 := rfl
    have hp8 : phi3 8 = 1 := rfl
    rcases f2_eval_12378 w1 w2 w3 with ⟨e1, e2, e3, e7, e8⟩
    rw [hp1, e1, exactVal2_zero_iff] at hv1
    rw [hp2, e2, exactVal2_one_iff] at hv2
    rw [hp3, e3, exactVal2_one_iff] at hv3
    rw [hp7, e7, exactVal2_two_iff] at hv7
    rw [hp8, e8, exactVal2_one_iff] at hv8
    let r1 : Fin 8 := ⟨(w1 % 8).toNat, by omega⟩
    let r2 : Fin 8 := ⟨(w2 % 8).toNat, by omega⟩
    let r3 : Fin 8 := ⟨(w3 % 8).toNat, by omega⟩
    have hr1 : w1 % 8 = (r1.val : Int) % 8 := by dsimp [r1]; omega
    have hr2 : w2 % 8 = (r2.val : Int) % 8 := by dsimp [r2]; omega
    have hr3 : w3 % 8 = (r3.val : Int) % 8 := by dsimp [r3]; omega
    have hsq := mod8_mul hr1 hr1
    have h12 := mod8_add hr1 hr2
    have hsq3 := mod8_add hsq hr3
    have h7eq := mod8_add (mod8_mul hr1 hsq3) (mod8_mul hr3 h12)
    have h8eq := mod8_add (mod8_add h12 (mod8_mul hr2 hr1)) (mod8_mul hr2 hsq)
    have htab := rigidity2_mod8_table r1 r2 r3
      (by omega) (by omega) (by omega) (by omega) (by omega)
    omega
  constructor
  · constructor
    · intro hall; exact ⟨hall 1, hall 2, hall 3, hall 7, hall 8⟩
    · intro h5
      rcases h5_to_cong h5 with ⟨c1, c2, c3, cs⟩
      exact thm_2x2_exact_v2 w1 w2 w3 c1 c2 c3 cs
  · constructor
    · exact h5_to_cong
    · rintro ⟨c1, c2, c3, cs⟩
      have hall := thm_2x2_exact_v2 w1 w2 w3 c1 c2 c3 cs
      exact ⟨hall 1, hall 2, hall 3, hall 7, hall 8⟩

theorem choose_one (k : Nat) : choose k 1 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [choose, ih]; omega

theorem choose_two_mul2 (k : Nat) : 2 * choose k 2 = k * (k - 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [choose, choose_one, Nat.add_sub_cancel]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [Nat.add_sub_cancel] at ih
      rw [Nat.mul_add, ih, Nat.mul_comm (k + 1 + 1) (k + 1), Nat.mul_add (k + 1) (k + 1) 1,
          Nat.mul_add (k + 1) k 1, Nat.mul_one]
      omega

theorem choose_three_mul6 (k : Nat) : 6 * choose k 3 = k * (k - 1) * (k - 2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [choose, Nat.add_sub_cancel]
    have h2 := choose_two_mul2 k
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        have hstep : 6 * (choose (k + 1 + 1) 2 + choose (k + 1 + 1) 3) =
            3 * (2 * choose (k + 1 + 1) 2) + 6 * choose (k + 1 + 1) 3 := by omega
        rw [hstep, h2, ih]
        have hs1 : k + 1 + 1 - 1 = k + 1 := by omega
        have hs2 : k + 1 + 1 - 2 = k := by omega
        have hs3 : k + 1 + 1 + 1 - 2 = k + 1 := by omega
        rw [hs1, hs2, hs3]
        have h1 : (k + 1 + 1 + 1) * (k + 1 + 1) * (k + 1) = (k + 1 + 1) * (k + 1) * (k + 3) := by ac_rfl
        have h2' : (k + 1 + 1) * (k + 1) * (k + 3) = (k + 1 + 1) * (k + 1) * k + 3 * ((k + 1 + 1) * (k + 1)) := by
          rw [Nat.mul_add, Nat.mul_comm ((k + 1 + 1) * (k + 1)) 3]
        rw [h1, h2']
        omega

/--
**Infinite Theorem A5 (Binomial Specialization for ALL `k = 8*t + 3`, `k`-way 1-Bit-Carry Addition)**.
-/
theorem thm_2x2_k_equiv_3_mod_8 (t : Nat) :
    let k := 8 * t + 3
    ∀ n : Nat, ExactVal2 (f2 (choose k 1 : Int) (choose k 2 : Int) (choose k 3 : Int) n) (phi3 n) := by
  intro k
  have hk1 : choose k 1 = 8 * t + 3 := choose_one k
  have hk2_eq : 2 * choose k 2 = (8 * t + 3) * (8 * t + 2) := by
    have h := choose_two_mul2 k
    have hs1 : k - 1 = 8 * t + 2 := by omega
    rw [hs1] at h; exact h
  have hk2 : choose k 2 = (8 * t + 3) * (4 * t + 1) := by
    have h : (8 * t + 3) * (8 * t + 2) = 2 * ((8 * t + 3) * (4 * t + 1)) := by
      have : 8 * t + 2 = 2 * (4 * t + 1) := by omega
      rw [this]; ac_rfl
    omega
  have hk3_eq : 6 * choose k 3 = (8 * t + 3) * (8 * t + 2) * (8 * t + 1) := by
    have h := choose_three_mul6 k
    have hs1 : k - 1 = 8 * t + 2 := by omega
    have hs2 : k - 2 = 8 * t + 1 := by omega
    rw [hs1, hs2] at h; exact h
  have h3_mul : 3 * choose k 3 = (8 * t + 3) * (4 * t + 1) * (8 * t + 1) := by
    have h : (8 * t + 3) * (8 * t + 2) * (8 * t + 1) =
        2 * ((8 * t + 3) * (4 * t + 1) * (8 * t + 1)) := by
      have : 8 * t + 2 = 2 * (4 * t + 1) := by omega
      rw [this]; ac_rfl
    omega
  have hprod2 : ((8 * t + 3) * (4 * t + 1)) % 8 = (4 * t + 3) % 8 := by
    have hexp : (8 * t + 3) * (4 * t + 1) = 8 * (4 * t * t + 2 * t) + (4 * t + 3) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one]
      have h1 : 8 * t * (4 * t) = 8 * (4 * t * t) := by ac_rfl
      have h2 : 8 * (4 * t * t + 2 * t) = 8 * (4 * t * t) + 8 * (2 * t) := Nat.mul_add 8 _ _
      omega
    omega
  have hprod3 : ((8 * t + 3) * (4 * t + 1) * (8 * t + 1)) % 8 = (4 * t + 3) % 8 := by
    rw [Nat.mul_mod, hprod2]
    have h81 : (8 * t + 1) % 8 = 1 := by omega
    rw [h81, Nat.mul_one, Nat.mod_mod]
  have hw2_mod8 : choose k 2 % 8 = (4 * t + 3) % 8 := by rw [hk2]; exact hprod2
  have hw3_mod8 : choose k 3 % 8 = (4 * t + 1) % 8 := by
    have h3m : (3 * choose k 3) % 8 = (4 * t + 3) % 8 := by rw [h3_mul]; exact hprod3
    omega
  apply thm_2x2_exact_v2
  · omega
  · omega
  · omega
  · omega

/-- **Unboundedness Witness for `Φ_3`**: `∀ m, phi3 (2^(m+1) - 1) = m`. -/
theorem thm_phi3_unbounded : ∀ m : Nat, phi3 (2 ^ (m + 1) - 1) = m := by
  have haux : ∀ m : Nat, runQ3 (2 ^ (m + 1) - 1) = ⟨1, by decide⟩ ∧ runE3 (2 ^ (m + 1) - 1) = m := by
    intro m
    induction m with
    | zero => exact ⟨rfl, rfl⟩
    | succ m ih =>
      rcases ih with ⟨ihq, ihe⟩
      have hpos : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow (m + 1) 2 (by decide)
      have hpow : 2 ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 := Nat.pow_succ 2 (m + 1)
      have heq : 2 ^ (m + 1 + 1) - 1 = 2 * (2 ^ (m + 1) - 1) + (if true then 1 else 0) := by
        simp only [↓reduceIte]; omega
      rw [heq, runQ3_step, runE3_step, ihq, ihe]
      exact ⟨rfl, rfl⟩
  intro m
  rcases haux m with ⟨hq, he⟩
  simp [phi3, hq, he, aOff2]

-- ============================================================================
-- Section 6: Infinite Theorem B — Mod-3 Even-1-Runs Dichotomy for `f_{3,1}(n)`
-- ============================================================================

theorem allOneRunsEvenFuel_eq :
    ∀ fuel1 fuel2 n c, n ≤ fuel1 → n ≤ fuel2 →
      allOneRunsEvenFuel fuel1 n c = allOneRunsEvenFuel fuel2 n c := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 n c h1 _
    have hn : n = 0 := by omega
    subst hn; cases fuel2 <;> simp [allOneRunsEvenFuel]
  | succ fuel1 ih =>
    intro fuel2 n c h1 h2
    cases fuel2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [allOneRunsEvenFuel]
    | succ fuel2 =>
      simp only [allOneRunsEvenFuel]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        have hq1 : n / 2 ≤ fuel1 := by omega
        have hq2 : n / 2 ≤ fuel2 := by omega
        by_cases hpar : n % 2 = 1
        · simp only [hpar, ↓reduceIte]; exact ih fuel2 (n / 2) (!c) hq1 hq2
        · simp only [hpar, ↓reduceIte]
          cases c
          · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih fuel2 (n / 2) false hq1 hq2
          · rfl

theorem allOneRunsEvenAux_zero (c : Bool) : allOneRunsEvenAux 0 c = !c := rfl

theorem allOneRunsEvenAux_step_odd (n : Nat) (c : Bool) :
    allOneRunsEvenAux (2 * n + 1) c = allOneRunsEvenAux n (!c) := by
  unfold allOneRunsEvenAux
  have hne : 2 * n + 1 ≠ 0 := by omega
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp only [allOneRunsEvenFuel, hne, hmod, hdiv, ↓reduceIte]
  exact allOneRunsEvenFuel_eq (2 * n) n n (!c) (by omega) (Nat.le_refl n)

theorem allOneRunsEvenAux_step_even (n : Nat) (c : Bool) :
    allOneRunsEvenAux (2 * n) c = if c then false else allOneRunsEvenAux n false := by
  by_cases hn : n = 0
  · subst hn; cases c <;> rfl
  · have hne : 2 * n ≠ 0 := by omega
    have hfuel : allOneRunsEvenAux (2 * n) c = allOneRunsEvenFuel (2 * n - 1 + 1) (2 * n) c := by
      unfold allOneRunsEvenAux
      have heq : 2 * n - 1 + 1 = 2 * n := by omega
      rw [heq]
    rw [hfuel]
    have hmod : (2 * n) % 2 ≠ 1 := by omega
    have hdiv : (2 * n) / 2 = n := by omega
    simp only [allOneRunsEvenFuel, hne, hmod, hdiv, ↓reduceIte]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact allOneRunsEvenFuel_eq (2 * n - 1) n n false (by omega) (Nat.le_refl n)
    · rfl

theorem certK3Mod3_state_iff :
    ∀ n : Nat,
      (certK3Mod3.runQ n = ⟨0, by decide⟩ ↔ allOneRunsEvenAux n false = true) ∧
      (certK3Mod3.runQ n = ⟨1, by decide⟩ ↔ allOneRunsEvenAux n true = true) := by
  have hd00 : ∀ s : Fin 3, deltaMod3 s false = ⟨0, by decide⟩ ↔ s = ⟨0, by decide⟩ := by decide
  have hd01 : ∀ s : Fin 3, deltaMod3 s false ≠ ⟨1, by decide⟩ := by decide
  have hd10 : ∀ s : Fin 3, deltaMod3 s true = ⟨0, by decide⟩ ↔ s = ⟨1, by decide⟩ := by decide
  have hd11 : ∀ s : Fin 3, deltaMod3 s true = ⟨1, by decide⟩ ↔ s = ⟨0, by decide⟩ := by decide
  apply nat_bit_ind
  · simp [ModQuotientCert.runQ_zero, certK3Mod3, allOneRunsEvenAux_zero]
  · intro n b ⟨ih0, ih1⟩
    cases b with
    | false =>
      have hq := certK3Mod3.runQ_step n false
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hq ⊢
      rw [hq, allOneRunsEvenAux_step_even, allOneRunsEvenAux_step_even]
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · exact Iff.trans (hd00 (certK3Mod3.runQ n)) ih0
      · constructor
        · intro h; exact absurd h (hd01 (certK3Mod3.runQ n))
        · intro h; exact False.elim h
    | true =>
      have hq := certK3Mod3.runQ_step n true
      simp only [↓reduceIte] at hq ⊢
      rw [hq, allOneRunsEvenAux_step_odd, allOneRunsEvenAux_step_odd]
      simp only [Bool.not_false, Bool.not_true]
      constructor
      · exact Iff.trans (hd10 (certK3Mod3.runQ n)) ih1
      · exact Iff.trans (hd11 (certK3Mod3.runQ n)) ih0

/--
**Infinite Theorem B1 (Mod-3 Even-1-Runs Dichotomy for 3-Way 1-Bit-Carry Addition `f_{3,1}(n)`)**:
`f_{3,1}(n) % 3 = 1` if every maximal run of `1`-bits in binary `n` has even length, and `0` otherwise.
-/
theorem thm_k3_c1_mod3_even_one_runs (n : Nat) :
    f2 3 3 1 n % 3 = if allOneRunsEven n then 1 else 0 := by
  have hs := certK3Mod3.sound n ⟨0, by decide⟩
  have hiff := (certK3Mod3_state_iff n).1
  have hzero : ∀ s : Fin 3, s ≠ ⟨0, by decide⟩ → phiMod3 s ⟨0, by decide⟩ % 3 = 0 := by decide
  simp only [f2, allOneRunsEven]
  rw [hs]
  by_cases he : allOneRunsEvenAux n false = true
  · have hq : certK3Mod3.runQ n = ⟨0, by decide⟩ := hiff.mpr he
    simp only [he, ↓reduceIte]
    rw [hq]; decide
  · have hq : certK3Mod3.runQ n ≠ ⟨0, by decide⟩ := fun h => he (hiff.mp h)
    have hfalse : allOneRunsEvenAux n false = false := by cases h : allOneRunsEvenAux n false <;> simp_all
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
    exact hzero (certK3Mod3.runQ n) hq

/-- **Infinite Theorem B2**: `f_{3,1}(n)` is NEVER congruent to `2 (mod 3)`. -/
theorem thm_k3_c1_never_2_mod3 (n : Nat) : f2 3 3 1 n % 3 ≠ 2 := by
  rw [thm_k3_c1_mod3_even_one_runs]
  cases allOneRunsEven n <;> decide

-- ============================================================================
-- Section 7: Infinite Theorem Family C (3×3, C = 2, Digits {0,1,2,3,4,5})
-- ============================================================================

theorem carryMat_eq_M3 (w1 w2 w3 w4 w5 : Int) :
    carryMat (w3Fun w1 w2 w3 w4 w5) 2 false = M3_0 w1 w2 w3 w4 ∧
    carryMat (w3Fun w1 w2 w3 w4 w5) 2 true = M3_1 w1 w2 w3 w4 w5 ∧
    e0Vec 2 = v3_0 := by
  refine ⟨?_, ?_, ?_⟩
  · funext i j; revert i j; apply fin3_all <;> (apply fin3_all <;> rfl)
  · funext i j; revert i j; apply fin3_all <;> (apply fin3_all <;> rfl)
  · funext i; revert i; apply fin3_all <;> rfl

/-- Direct combinatorial identity for 2-bit-carry weighted `{0,1,2,3,4,5}`-representations. -/
theorem carryCount_eq_f3 (w1 w2 w3 w4 w5 : Int) (width n : Nat) (hn : n < 2 ^ width) :
    carryCount (w3Fun w1 w2 w3 w4 w5) 2 width n 0 = f3 w1 w2 w3 w4 w5 n := by
  have h := carryCount_eq_evalMat (w3Fun w1 w2 w3 w4 w5) rfl 2 width n hn ⟨0, by decide⟩
  rcases carryMat_eq_M3 w1 w2 w3 w4 w5 with ⟨h0, h1, hv⟩
  rw [h0, h1, hv] at h
  exact h

theorem runQE4_step (n : Nat) (b : Bool) :
    runQE4 (2 * n + if b then 1 else 0) = (delta3 (runQ4 n) b, runE4 n + eGain3 (runQ4 n) b) :=
  bitFold_step (⟨0, by decide⟩, 0) (fun (q, e) b => (delta3 q b, e + eGain3 q b)) rfl n b

theorem runQ4_step (n : Nat) (b : Bool) :
    runQ4 (2 * n + if b then 1 else 0) = delta3 (runQ4 n) b := by
  simp [runQ4, runQE4_step]

theorem runE4_step (n : Nat) (b : Bool) :
    runE4 (2 * n + if b then 1 else 0) = runE4 n + eGain3 (runQ4 n) b := by
  simp [runE4, runQE4_step]

theorem cert3Param_runQE_eq (a1 a2 a3 a4 a5 : Int) :
    ∀ n : Nat,
      ((cert3Param a1 a2 a3 a4 a5).runQ n, (cert3Param a1 a2 a3 a4 a5).runE n) = runQE4 n := by
  apply nat_bit_ind
  · rfl
  · intro n b ih
    have ihq : (cert3Param a1 a2 a3 a4 a5).runQ n = runQ4 n := congrArg Prod.fst ih
    have ihe : (cert3Param a1 a2 a3 a4 a5).runE n = runE4 n := congrArg Prod.snd ih
    rw [(cert3Param a1 a2 a3 a4 a5).runQ_step, (cert3Param a1 a2 a3 a4 a5).runE_step,
        runQE4_step, ihq, ihe]
    rfl

theorem cert3Param_totalVal_eq (a1 a2 a3 a4 a5 : Int) (n : Nat) :
    (cert3Param a1 a2 a3 a4 a5).totalVal n = phi4 n := by
  have h := cert3Param_runQE_eq a1 a2 a3 a4 a5 n
  have hq : (cert3Param a1 a2 a3 a4 a5).runQ n = runQ4 n := congrArg Prod.fst h
  have he : (cert3Param a1 a2 a3 a4 a5).runE n = runE4 n := congrArg Prod.snd h
  rw [LatticeGaugeCert.totalVal, phi4, hq, he]
  rfl

/--
**Infinite Theorem C1 (3×3 Exact Unbounded 2-Adic Valuation Law)**:
For ALL `(w1, w2, w3, w4, w5) ∈ ℤ⁵` with
`w1 % 8 = 4 ∧ w2 % 4 = 2 ∧ w3 % 8 = 4 ∧ w4 % 2 = 1 ∧ w5 % 16 = 0`,
and ALL `n : Nat`, `ExactVal2 (f3 w1 w2 w3 w4 w5 n) (phi4 n)`.
-/
theorem thm_3x3_exact_v2 (w1 w2 w3 w4 w5 : Int)
    (h1 : w1 % 8 = 4) (h2 : w2 % 4 = 2) (h3 : w3 % 8 = 4)
    (h4 : w4 % 2 = 1) (h5 : w5 % 16 = 0) :
    ∀ n : Nat, ExactVal2 (f3 w1 w2 w3 w4 w5 n) (phi4 n) := by
  have hw1 : w1 = 8 * (w1 / 8) + 4 := by omega
  have hw2 : w2 = 4 * (w2 / 4) + 2 := by omega
  have hw3 : w3 = 8 * (w3 / 8) + 4 := by omega
  have hw4 : w4 = 2 * (w4 / 2) + 1 := by omega
  have hw5 : w5 = 16 * (w5 / 16) := by omega
  intro n
  have h := (cert3Param (w1 / 8) (w2 / 4) (w3 / 8) (w4 / 2) (w5 / 16)).exact_v2 n
  rw [cert3Param_totalVal_eq] at h
  rw [f3, hw1, hw2, hw3, hw4, hw5]
  exact h

private theorem f3_eval_12345 (w1 w2 w3 w4 w5 : Int) :
    f3 w1 w2 w3 w4 w5 1 = w1 ∧
    f3 w1 w2 w3 w4 w5 2 = w1 + w2 ∧
    f3 w1 w2 w3 w4 w5 3 = w1 * w1 + w3 ∧
    f3 w1 w2 w3 w4 w5 4 = w1 + w2 + w2 * w1 + w4 ∧
    f3 w1 w2 w3 w4 w5 5 = w1 * (w1 + w2) + w3 * w1 + w5 := by
  have hfix : matVec (M3_0 w1 w2 w3 w4) v3_0 = v3_0 := by
    funext i; revert i; apply fin3_all <;> simp [matVec, sumFin, M3_0, v3_0]
  have h0 : evalMat (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 0 = v3_0 := evalMat_zero _ _ _
  have h1 : evalMat (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 1 =
      matVec (M3_1 w1 w2 w3 w4 w5) v3_0 := by
    simpa [h0] using evalMat_step (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 hfix 0 true
  have h2 : evalMat (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 2 =
      matVec (M3_0 w1 w2 w3 w4) (evalMat (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 1) := by
    simpa using evalMat_step (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 hfix 1 false
  have h3 : evalMat (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 3 =
      matVec (M3_1 w1 w2 w3 w4 w5) (evalMat (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 1) := by
    simpa using evalMat_step (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 hfix 1 true
  have h4 : evalMat (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 4 =
      matVec (M3_0 w1 w2 w3 w4) (evalMat (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 2) := by
    simpa using evalMat_step (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 hfix 2 false
  have h5 : evalMat (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 5 =
      matVec (M3_1 w1 w2 w3 w4 w5) (evalMat (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 2) := by
    simpa using evalMat_step (M3_0 w1 w2 w3 w4) (M3_1 w1 w2 w3 w4 w5) v3_0 hfix 2 true
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [f3, h1, matVec, sumFin, M3_1, v3_0]
  · simp [f3, h2, h1, matVec, sumFin, M3_0, M3_1, v3_0]
  · simp [f3, h3, h1, matVec, sumFin, M3_1, v3_0]
  · simp [f3, h4, h2, h1, matVec, sumFin, M3_0, M3_1, v3_0]
  · simp [f3, h5, h2, h1, matVec, sumFin, M3_0, M3_1, v3_0]

/--
**Infinite Theorem C2 (3×3 5-Point Finite-to-Infinite 2-Adic Rigidity IFF)**:
For ANY integer weights `(1, w1, w2, w3, w4, w5)` with carry cap `C = 2`, matching `ExactVal2 (f3 ... n) (phi4 n)`
for ALL `n : Nat` is equivalent to matching on JUST the first 5 positive integers `{1, 2, 3, 4, 5}`,
and equivalent to `w1 % 8 = 4 ∧ w2 % 4 = 2 ∧ w3 % 8 = 4 ∧ w4 % 2 = 1 ∧ w5 % 16 = 0`!
-/
theorem thm_3x3_5point_rigidity (w1 w2 w3 w4 w5 : Int) :
    ((∀ n : Nat, ExactVal2 (f3 w1 w2 w3 w4 w5 n) (phi4 n)) ↔
     (ExactVal2 (f3 w1 w2 w3 w4 w5 1) (phi4 1) ∧
      ExactVal2 (f3 w1 w2 w3 w4 w5 2) (phi4 2) ∧
      ExactVal2 (f3 w1 w2 w3 w4 w5 3) (phi4 3) ∧
      ExactVal2 (f3 w1 w2 w3 w4 w5 4) (phi4 4) ∧
      ExactVal2 (f3 w1 w2 w3 w4 w5 5) (phi4 5)))
    ∧
    ((ExactVal2 (f3 w1 w2 w3 w4 w5 1) (phi4 1) ∧
      ExactVal2 (f3 w1 w2 w3 w4 w5 2) (phi4 2) ∧
      ExactVal2 (f3 w1 w2 w3 w4 w5 3) (phi4 3) ∧
      ExactVal2 (f3 w1 w2 w3 w4 w5 4) (phi4 4) ∧
      ExactVal2 (f3 w1 w2 w3 w4 w5 5) (phi4 5)) ↔
     (w1 % 8 = 4 ∧ w2 % 4 = 2 ∧ w3 % 8 = 4 ∧ w4 % 2 = 1 ∧ w5 % 16 = 0)) := by
  have h5_to_cong :
      (ExactVal2 (f3 w1 w2 w3 w4 w5 1) (phi4 1) ∧
       ExactVal2 (f3 w1 w2 w3 w4 w5 2) (phi4 2) ∧
       ExactVal2 (f3 w1 w2 w3 w4 w5 3) (phi4 3) ∧
       ExactVal2 (f3 w1 w2 w3 w4 w5 4) (phi4 4) ∧
       ExactVal2 (f3 w1 w2 w3 w4 w5 5) (phi4 5)) →
      (w1 % 8 = 4 ∧ w2 % 4 = 2 ∧ w3 % 8 = 4 ∧ w4 % 2 = 1 ∧ w5 % 16 = 0) := by
    intro ⟨hv1, hv2, hv3, hv4, hv5⟩
    have hp1 : phi4 1 = 2 := rfl
    have hp2 : phi4 2 = 1 := rfl
    have hp3 : phi4 3 = 2 := rfl
    have hp4 : phi4 4 = 0 := rfl
    have hp5 : phi4 5 = 3 := rfl
    rcases f3_eval_12345 w1 w2 w3 w4 w5 with ⟨e1, e2, e3, e4, e5⟩
    rw [hp1, e1, exactVal2_two_iff] at hv1
    rw [hp2, e2, exactVal2_one_iff] at hv2
    rw [hp3, e3, exactVal2_two_iff] at hv3
    rw [hp4, e4, exactVal2_zero_iff] at hv4
    rw [hp5, e5, exactVal2_three_iff] at hv5
    have hw1 : w1 % 8 = 4 := hv1
    have hw2 : w2 % 4 = 2 := by omega
    have hw1sq : (w1 * w1) % 16 = 0 := by
      have h1 : w1 = 4 * (w1 / 4) := by omega
      have h2 : w1 * w1 = 16 * ((w1 / 4) * (w1 / 4)) := by
        conv => lhs; rw [h1]
        rw [Int.mul_assoc, Int.mul_left_comm (w1 / 4) 4 (w1 / 4), ← Int.mul_assoc]
        rfl
      omega
    have hw3 : w3 % 8 = 4 := by omega
    have hw21 : (w2 * w1) % 2 = 0 := by
      rw [Int.mul_emod]
      have : w1 % 2 = 0 := by omega
      rw [this]; simp
    have hw4 : w4 % 2 = 1 := by omega
    have hw1w2 : (w1 * (w1 + w2)) % 16 = 8 := by
      rw [Int.mul_emod]
      have hm1 : w1 % 16 = 4 ∨ w1 % 16 = 12 := by omega
      have hm2 : (w1 + w2) % 16 = 2 ∨ (w1 + w2) % 16 = 6 ∨ (w1 + w2) % 16 = 10 ∨ (w1 + w2) % 16 = 14 := by omega
      rcases hm1 with h1' | h1' <;> rcases hm2 with h2' | h2' | h2' | h2' <;> rw [h1', h2'] <;> decide
    have hw3w1 : (w3 * w1) % 16 = 0 := by
      have h1 : w1 = 4 * (w1 / 4) := by omega
      have h3 : w3 = 4 * (w3 / 4) := by omega
      have h31 : w3 * w1 = 16 * ((w3 / 4) * (w1 / 4)) := by
        conv => lhs; rw [h3, h1]
        rw [Int.mul_assoc, Int.mul_left_comm (w3 / 4) 4 (w1 / 4), ← Int.mul_assoc]
        rfl
      omega
    have hw5 : w5 % 16 = 0 := by omega
    exact ⟨hw1, hw2, hw3, hw4, hw5⟩
  constructor
  · constructor
    · intro hall; exact ⟨hall 1, hall 2, hall 3, hall 4, hall 5⟩
    · intro h5
      rcases h5_to_cong h5 with ⟨c1, c2, c3, c4, c5⟩
      exact thm_3x3_exact_v2 w1 w2 w3 w4 w5 c1 c2 c3 c4 c5
  · constructor
    · exact h5_to_cong
    · rintro ⟨c1, c2, c3, c4, c5⟩
      have hall := thm_3x3_exact_v2 w1 w2 w3 w4 w5 c1 c2 c3 c4 c5
      exact ⟨hall 1, hall 2, hall 3, hall 4, hall 5⟩

theorem choose_four_mul24 (k : Nat) : 24 * choose k 4 = k * (k - 1) * (k - 2) * (k - 3) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [choose, Nat.add_sub_cancel]
    have h3 := choose_three_mul6 k
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        cases k with
        | zero => rfl
        | succ k =>
          have hstep : 24 * (choose (k + 1 + 1 + 1) 3 + choose (k + 1 + 1 + 1) 4) =
              4 * (6 * choose (k + 1 + 1 + 1) 3) + 24 * choose (k + 1 + 1 + 1) 4 := by omega
          rw [hstep, h3, ih]
          have hs1 : k + 1 + 1 + 1 - 1 = k + 2 := by omega
          have hs2 : k + 1 + 1 + 1 - 2 = k + 1 := by omega
          have hs3 : k + 1 + 1 + 1 - 3 = k := by omega
          have ht2 : k + 1 + 1 + 1 + 1 - 2 = k + 2 := by omega
          have ht3 : k + 1 + 1 + 1 + 1 - 3 = k + 1 := by omega
          rw [hs1, hs2, hs3, ht2, ht3]
          have hcomm : (k + 1 + 1 + 1 + 1) * (k + 1 + 1 + 1) * (k + 2) * (k + 1) =
              (k + 1 + 1 + 1) * (k + 2) * (k + 1) * (k + 4) := by ac_rfl
          rw [hcomm, Nat.mul_add ((k + 1 + 1 + 1) * (k + 2) * (k + 1)) k 4,
              Nat.mul_comm ((k + 1 + 1 + 1) * (k + 2) * (k + 1)) 4]
          omega

theorem choose_five_mul120 (k : Nat) :
    120 * choose k 5 = k * (k - 1) * (k - 2) * (k - 3) * (k - 4) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [choose, Nat.add_sub_cancel]
    have h4 := choose_four_mul24 k
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        cases k with
        | zero => rfl
        | succ k =>
          cases k with
          | zero => rfl
          | succ k =>
            have hstep : 120 * (choose (k + 1 + 1 + 1 + 1) 4 + choose (k + 1 + 1 + 1 + 1) 5) =
                5 * (24 * choose (k + 1 + 1 + 1 + 1) 4) + 120 * choose (k + 1 + 1 + 1 + 1) 5 := by omega
            rw [hstep, h4, ih]
            have hs1 : k + 1 + 1 + 1 + 1 - 1 = k + 3 := by omega
            have hs2 : k + 1 + 1 + 1 + 1 - 2 = k + 2 := by omega
            have hs3 : k + 1 + 1 + 1 + 1 - 3 = k + 1 := by omega
            have hs4 : k + 1 + 1 + 1 + 1 - 4 = k := by omega
            have ht2 : k + 1 + 1 + 1 + 1 + 1 - 2 = k + 3 := by omega
            have ht3 : k + 1 + 1 + 1 + 1 + 1 - 3 = k + 2 := by omega
            have ht4 : k + 1 + 1 + 1 + 1 + 1 - 4 = k + 1 := by omega
            rw [hs1, hs2, hs3, hs4, ht2, ht3, ht4]
            have hcomm : (k + 1 + 1 + 1 + 1 + 1) * (k + 1 + 1 + 1 + 1) * (k + 3) * (k + 2) * (k + 1) =
                (k + 1 + 1 + 1 + 1) * (k + 3) * (k + 2) * (k + 1) * (k + 5) := by ac_rfl
            rw [hcomm, Nat.mul_add ((k + 1 + 1 + 1 + 1) * (k + 3) * (k + 2) * (k + 1)) k 5,
                Nat.mul_comm ((k + 1 + 1 + 1 + 1) * (k + 3) * (k + 2) * (k + 1)) 5]
            omega

/--
**Infinite Theorem C3 (Binomial Specialization for ALL `k = 16*t + 4`, `k`-way 2-Bit-Carry Addition)**.
-/
theorem thm_3x3_k_equiv_4_mod_16 (t : Nat) :
    let k := 16 * t + 4
    ∀ n : Nat,
      ExactVal2
        (f3 (choose k 1 : Int) (choose k 2 : Int) (choose k 3 : Int)
            (choose k 4 : Int) (choose k 5 : Int) n)
        (phi4 n) := by
  intro k
  have hk1 : choose k 1 = 16 * t + 4 := choose_one k
  have hk2_eq : 2 * choose k 2 = (16 * t + 4) * (16 * t + 3) := by
    have h := choose_two_mul2 k; have hs1 : k - 1 = 16 * t + 3 := by omega
    rw [hs1] at h; exact h
  have hk2 : choose k 2 = (8 * t + 2) * (16 * t + 3) := by
    have h : (16 * t + 4) * (16 * t + 3) = 2 * ((8 * t + 2) * (16 * t + 3)) := by
      have : 16 * t + 4 = 2 * (8 * t + 2) := by omega
      rw [this]; ac_rfl
    omega
  have hk2_mod4 : choose k 2 % 4 = 2 := by
    rw [hk2, Nat.mul_mod]
    have ha : (8 * t + 2) % 4 = 2 := by omega
    have hb : (16 * t + 3) % 4 = 3 := by omega
    rw [ha, hb]
  have hk3_eq : 6 * choose k 3 = (16 * t + 4) * (16 * t + 3) * (16 * t + 2) := by
    have h := choose_three_mul6 k
    have hs1 : k - 1 = 16 * t + 3 := by omega
    have hs2 : k - 2 = 16 * t + 2 := by omega
    rw [hs1, hs2] at h; exact h
  have hk3_mul3 : 3 * choose k 3 = (16 * t + 4) * (16 * t + 3) * (8 * t + 1) := by
    have h : (16 * t + 4) * (16 * t + 3) * (16 * t + 2) =
        2 * ((16 * t + 4) * (16 * t + 3) * (8 * t + 1)) := by
      have : 16 * t + 2 = 2 * (8 * t + 1) := by omega
      rw [this]; ac_rfl
    omega
  have hk3_mod8 : choose k 3 % 8 = 4 := by
    have h3m : (3 * choose k 3) % 8 = 4 := by
      rw [hk3_mul3, Nat.mul_mod, Nat.mul_mod (16 * t + 4)]
      have h1 : (16 * t + 4) % 8 = 4 := by omega
      have h2 : (16 * t + 3) % 8 = 3 := by omega
      have h3 : (8 * t + 1) % 8 = 1 := by omega
      rw [h1, h2, h3]
    omega
  have hk4_eq : 24 * choose k 4 = (16 * t + 4) * (16 * t + 3) * (16 * t + 2) * (16 * t + 1) := by
    have h := choose_four_mul24 k
    have hs1 : k - 1 = 16 * t + 3 := by omega
    have hs2 : k - 2 = 16 * t + 2 := by omega
    have hs3 : k - 3 = 16 * t + 1 := by omega
    rw [hs1, hs2, hs3] at h; exact h
  have hk4_mul3 : 3 * choose k 4 = (4 * t + 1) * (16 * t + 3) * (8 * t + 1) * (16 * t + 1) := by
    have h : (16 * t + 4) * (16 * t + 3) * (16 * t + 2) * (16 * t + 1) =
        8 * ((4 * t + 1) * (16 * t + 3) * (8 * t + 1) * (16 * t + 1)) := by
      have ha : 16 * t + 4 = 4 * (4 * t + 1) := by omega
      have hb : 16 * t + 2 = 2 * (8 * t + 1) := by omega
      have h8 : (8 : Nat) = 4 * 2 := rfl
      rw [ha, hb, h8]; ac_rfl
    omega
  have hk4_mod2 : choose k 4 % 2 = 1 := by
    have h3m : (3 * choose k 4) % 2 = 1 := by
      rw [hk4_mul3, Nat.mul_mod, Nat.mul_mod ((4 * t + 1) * (16 * t + 3)), Nat.mul_mod (4 * t + 1)]
      have h1 : (4 * t + 1) % 2 = 1 := by omega
      have h2 : (16 * t + 3) % 2 = 1 := by omega
      have h3 : (8 * t + 1) % 2 = 1 := by omega
      have h4 : (16 * t + 1) % 2 = 1 := by omega
      rw [h1, h2, h3, h4]
    omega
  have hk5_eq : 120 * choose k 5 =
      (16 * t + 4) * (16 * t + 3) * (16 * t + 2) * (16 * t + 1) * (16 * t) := by
    have h := choose_five_mul120 k
    have hs1 : k - 1 = 16 * t + 3 := by omega
    have hs2 : k - 2 = 16 * t + 2 := by omega
    have hs3 : k - 3 = 16 * t + 1 := by omega
    have hs4 : k - 4 = 16 * t := by omega
    rw [hs1, hs2, hs3, hs4] at h; exact h
  have hk5_mul15 : 15 * choose k 5 =
      16 * ((4 * t + 1) * (16 * t + 3) * (8 * t + 1) * (16 * t + 1) * t) := by
    have h : (16 * t + 4) * (16 * t + 3) * (16 * t + 2) * (16 * t + 1) * (16 * t) =
        8 * (16 * ((4 * t + 1) * (16 * t + 3) * (8 * t + 1) * (16 * t + 1) * t)) := by
      have ha : 16 * t + 4 = 4 * (4 * t + 1) := by omega
      have hb : 16 * t + 2 = 2 * (8 * t + 1) := by omega
      have h8 : (8 : Nat) = 4 * 2 := rfl
      rw [ha, hb, h8]; ac_rfl
    omega
  have hk5_mod16 : choose k 5 % 16 = 0 := by
    have h15 : (15 * choose k 5) % 16 = 0 := by rw [hk5_mul15]; omega
    omega
  apply thm_3x3_exact_v2
  · omega
  · omega
  · omega
  · omega
  · omega

/-- **Unboundedness Witness for `Φ_4`**: `∀ m, phi4 (2^(m+2) - 1) = m + 2`. -/
theorem thm_phi4_unbounded : ∀ m : Nat, phi4 (2 ^ (m + 2) - 1) = m + 2 := by
  have haux : ∀ m : Nat, runQ4 (2 ^ (m + 2) - 1) = ⟨3, by decide⟩ ∧ runE4 (2 ^ (m + 2) - 1) = m + 1 := by
    intro m
    induction m with
    | zero => exact ⟨rfl, rfl⟩
    | succ m ih =>
      rcases ih with ⟨ihq, ihe⟩
      have hpos : 1 ≤ 2 ^ (m + 2) := Nat.one_le_pow (m + 2) 2 (by decide)
      have hpow : 2 ^ (m + 1 + 2) = 2 ^ (m + 2) * 2 := Nat.pow_succ 2 (m + 2)
      have heq : 2 ^ (m + 1 + 2) - 1 = 2 * (2 ^ (m + 2) - 1) + (if true then 1 else 0) := by
        simp only [↓reduceIte]; omega
      rw [heq, runQ4_step, runE4_step, ihq, ihe]
      exact ⟨rfl, rfl⟩
  intro m
  rcases haux m with ⟨hq, he⟩
  rw [phi4, hq, he]
  rfl

-- ============================================================================
-- Section 8: Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples
-- ============================================================================

/-- Non-vacuity witness 1: `k = 3, C = 1` inhabits `LatticeGaugeCert` (2×2). -/
theorem nonvacuous_2x2_k3 :
    Nonempty (LatticeGaugeCert 2 3 (by decide) (M2_0 3 3) (M2_1 3 3 1) v2_0) :=
  ⟨cert2Param 0 0 0⟩

/-- Non-vacuity witness 2: `k = 11, C = 1` (`(11, 55, 165)`) inhabits `LatticeGaugeCert` (2×2). -/
theorem nonvacuous_2x2_k11 :
    Nonempty (LatticeGaugeCert 2 3 (by decide) (M2_0 11 55) (M2_1 11 55 165) v2_0) :=
  ⟨cert2Param 2 13 28⟩

/-- Non-vacuity witness 3: `k = 4, C = 2` inhabits `LatticeGaugeCert` (3×3). -/
theorem nonvacuous_3x3_k4 :
    Nonempty (LatticeGaugeCert 3 6 (by decide) (M3_0 4 6 4 1) (M3_1 4 6 4 1 0) v3_0) :=
  ⟨cert3Param 0 1 0 0 0⟩

/-- Non-vacuity witness 4: `k = 20, C = 2` (`(20, 190, 1140, 4845, 15504)`) inhabits `LatticeGaugeCert` (3×3). -/
theorem nonvacuous_3x3_k20 :
    Nonempty (LatticeGaugeCert 3 6 (by decide) (M3_0 20 190 1140 4845) (M3_1 20 190 1140 4845 15504) v3_0) :=
  ⟨cert3Param 2 47 142 2422 969⟩

/-- Non-vacuity witness 5: Mod-3 quotient automaton for `f_{3,1}(n)` is inhabited. -/
theorem nonvacuous_mod3_k3 :
    Nonempty (ModQuotientCert 2 3 3 (M2_0 3 3) (M2_1 3 3 1) v2_0) :=
  ⟨certK3Mod3⟩

/-- Concrete combinatorial replay witness: `carryCount` matches `f2 3 3 1 15 = 136` and `f3 4 6 4 1 0 12 = 454`. -/
theorem concrete_combinatorial_witness :
    carryCount (w2Fun 3 3 1) 1 4 15 0 = 136 ∧
    f2 3 3 1 15 = 136 ∧
    carryCount (w3Fun 4 6 4 1 0) 2 4 12 0 = 454 ∧
    f3 4 6 4 1 0 12 = 454 := by
  decide

/--
**Sharpness Counterexample 1 (Carry-Cap Sharpness `C = 1` vs `C = 2` for `k = 3`)**.
-/
theorem sharpness_k3_carry_cap :
    ¬ ExactVal2 (f3 3 3 1 0 0 8) (phi3 8) ∧
    (f3 3 3 1 0 0 9 % 3 ≠ if allOneRunsEven 9 then 1 else 0) := by
  constructor
  · have hv : f3 3 3 1 0 0 8 = 45 := rfl
    have hp : phi3 8 = 1 := rfl
    rw [hv, hp, exactVal2_one_iff]; decide
  · decide

/--
**Sharpness Counterexample 2 (Congruence Sharpness `k = 7 ≡ 7 mod 8`, `C = 1`)**.
-/
theorem sharpness_2x2_k7 :
    f2 7 21 35 3 = 84 ∧ phi3 3 = 1 ∧ ¬ ExactVal2 (f2 7 21 35 3) (phi3 3) := by
  refine ⟨rfl, rfl, ?_⟩
  have hv : f2 7 21 35 3 = 84 := rfl
  have hp : phi3 3 = 1 := rfl
  rw [hv, hp, exactVal2_one_iff]; decide

/--
**Sharpness Counterexample 3 (Individual Mod-8 Weight Sharpness `(3, 3, 5)`, `C = 1`)**:
breaks ONLY `(w1+w2+w3)%8 = 7`, failing both `Φ_3` at `n = 6` and sibling valuation symmetry (`5 ≠ 3`).
-/
theorem sharpness_2x2_mod8_sum :
    f2 3 3 5 6 = 32 ∧ f2 3 3 5 7 = 72 ∧
    ¬ ExactVal2 (f2 3 3 5 6) (phi3 6) ∧
    ExactVal2 (f2 3 3 5 6) 5 ∧ ExactVal2 (f2 3 3 5 7) 3 := by
  refine ⟨rfl, rfl, ?_, ⟨1, rfl, rfl⟩, ⟨9, rfl, rfl⟩⟩
  have hv : f2 3 3 5 6 = 32 := rfl
  have hp : phi3 6 = 2 := rfl
  rw [hv, hp, exactVal2_two_iff]; decide

/--
**Sharpness Counterexample 4 (Unweighted Hyperbinary `(1, 1, 1)`, `C = 1`)**:
matches `Φ_3(n)` for ALL `0 ≤ n ≤ 7`, then breaks precisely at `n = 8`, proving the 5th rigidity point is essential.
-/
theorem sharpness_2x2_unweighted_n8 :
    (∀ n : Fin 8, ExactVal2 (f2 1 1 1 n.val) (phi3 n.val)) ∧
    ¬ ExactVal2 (f2 1 1 1 8) (phi3 8) := by
  constructor
  · apply fin8_all
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨3, rfl, rfl⟩
    · exact ⟨3, rfl, rfl⟩
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨1, rfl, rfl⟩
  · have hv : f2 1 1 1 8 = 4 := rfl
    have hp : phi3 8 = 1 := rfl
    rw [hv, hp, exactVal2_one_iff]; decide

/--
**Sharpness Counterexample 5 (Carry-Cap Sharpness `C = 2` vs Unconstrained `C = 3` for `k = 4`)**.
-/
theorem sharpness_k4_carry_cap :
    carryCount (w3Fun 4 6 4 1 0) 3 4 12 0 = 455 ∧
    ¬ ExactVal2 (carryCount (w3Fun 4 6 4 1 0) 3 4 12 0) (phi4 12) := by
  constructor
  · decide
  · have hv : carryCount (w3Fun 4 6 4 1 0) 3 4 12 0 = 455 := by decide
    have hp : phi4 12 = 1 := rfl
    rw [hv, hp, exactVal2_one_iff]; decide

/--
**Sharpness Counterexample 6 (Congruence Sharpness `k = 12 ≡ 12 mod 16`, `C = 2`)**.
-/
theorem sharpness_3x3_k12 :
    f3 12 66 220 495 792 5 = 4368 ∧ phi4 5 = 3 ∧ ¬ ExactVal2 (f3 12 66 220 495 792 5) (phi4 5) := by
  refine ⟨rfl, rfl, ?_⟩
  have hv : f3 12 66 220 495 792 5 = 4368 := rfl
  have hp : phi4 5 = 3 := rfl
  rw [hv, hp, exactVal2_three_iff]; decide

/--
**Sharpness Counterexample 7 (All 5 Individual Weight Moduli in 3×3 Family, failing at `n = 1, 2, 3, 4, 5`)**.
-/
theorem sharpness_3x3_all_five_weights :
    ¬ ExactVal2 (f3 8 6 4 1 0 1) (phi4 1) ∧
    ¬ ExactVal2 (f3 4 0 4 1 0 2) (phi4 2) ∧
    ¬ ExactVal2 (f3 4 6 8 1 0 3) (phi4 3) ∧
    ¬ ExactVal2 (f3 4 6 4 2 0 4) (phi4 4) ∧
    ¬ ExactVal2 (f3 4 6 4 1 8 5) (phi4 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : f3 8 6 4 1 0 1 = 8 := rfl
    have p1 : phi4 1 = 2 := rfl
    rw [h1, p1, exactVal2_two_iff]; decide
  · have h2 : f3 4 0 4 1 0 2 = 4 := rfl
    have p2 : phi4 2 = 1 := rfl
    rw [h2, p2, exactVal2_one_iff]; decide
  · have h3 : f3 4 6 8 1 0 3 = 24 := rfl
    have p3 : phi4 3 = 2 := rfl
    rw [h3, p3, exactVal2_two_iff]; decide
  · have h4 : f3 4 6 4 2 0 4 = 36 := rfl
    have p4 : phi4 4 = 0 := rfl
    rw [h4, p4, exactVal2_zero_iff]; decide
  · have h5 : f3 4 6 4 1 8 5 = 64 := rfl
    have p5 : phi4 5 = 3 := rfl
    rw [h5, p5, exactVal2_three_iff]; decide

end BruhatTitsCarryEngine
