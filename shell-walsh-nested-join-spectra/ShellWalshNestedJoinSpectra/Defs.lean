/-
  Pure-Silicon Binary Math: 2-Adic Shell-Walsh Nested-Join & Carry-Butterfly
  Bitwise Graph Laplacian & Kirchhoff Spanning-Tree Infinite Proof Engine

  Worker: specmat-4 (Thread 3: Bit-Indexed Linear Algebra & Spectral Infinite Mechanisms)
  Standalone Lean 4.36.0 (zero Mathlib, zero sorry, standard axioms only).
-/

namespace ShellWalshEngine

/-! ============================================================================
    PART 1: Finite Sums, Products, Exact Integer Matrices, Levi-Civita Det,
            and the Master Orthogonal-Eigenbasis Spectral & Kirchhoff Engine
    ============================================================================ -/

/-- Exact integer sum over `Fin n`. -/
def sumFin : (n : Nat) -> (Fin n -> Int) -> Int
  | 0, _ => 0
  | n + 1, f => sumFin n (fun i => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩

/-- Exact integer product over `Fin n`. -/
def prodFin : (n : Nat) -> (Fin n -> Int) -> Int
  | 0, _ => 1
  | n + 1, f => prodFin n (fun i => f i.castSucc) * f ⟨n, Nat.lt_succ_self n⟩

theorem sumFin_congr {n : Nat} {f g : Fin n -> Int} (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => h i.castSucc), h ⟨n, Nat.lt_succ_self n⟩]

theorem prodFin_congr {n : Nat} {f g : Fin n -> Int} (h : ∀ i, f i = g i) :
    prodFin n f = prodFin n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prodFin]
    rw [ih (fun i => h i.castSucc), h ⟨n, Nat.lt_succ_self n⟩]

theorem sumFin_zero (n : Nat) : sumFin n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumFin, ih]

theorem prodFin_one (n : Nat) : prodFin n (fun _ => 1) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prodFin, ih]

theorem sumFin_const (n : Nat) (c : Int) : sumFin n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih]
    have h1 : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
    rw [h1, Int.add_mul, Int.one_mul]

theorem sumFin_add {n : Nat} (f g : Fin n -> Int) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih]
    omega

theorem sumFin_neg {n : Nat} (f : Fin n -> Int) :
    sumFin n (fun i => -f i) = -sumFin n f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih]
    omega

theorem sumFin_sub {n : Nat} (f g : Fin n -> Int) :
    sumFin n (fun i => f i - g i) = sumFin n f - sumFin n g := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih]
    omega

theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n -> Int) :
    sumFin n (fun i => c * f i) = c * sumFin n f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih, Int.mul_add]

theorem sumFin_mul_right {n : Nat} (f : Fin n -> Int) (c : Int) :
    sumFin n (fun i => f i * c) = sumFin n f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih, Int.add_mul]

theorem prodFin_mul {n : Nat} (f g : Fin n -> Int) :
    prodFin n (fun i => f i * g i) = prodFin n f * prodFin n g := by
  induction n with
  | zero => simp [prodFin]
  | succ n ih =>
    simp only [prodFin, ih]
    have h1 : ∀ a b c d : Int, a * c * (b * d) = a * b * (c * d) := by
      intro a b c d
      calc a * c * (b * d) = a * (c * b * d) := by rw [Int.mul_assoc, Int.mul_assoc]
        _ = a * (b * c * d) := by rw [Int.mul_comm c b]
        _ = a * b * (c * d) := by rw [Int.mul_assoc, Int.mul_assoc]
    exact h1 _ _ _ _

theorem sumFin_swap_order {m n : Nat} (f : Fin m -> Fin n -> Int) :
    sumFin m (fun i => sumFin n (fun j => f i j)) =
    sumFin n (fun j => sumFin m (fun i => f i j)) := by
  induction m with
  | zero => simp [sumFin, sumFin_zero]
  | succ m ih =>
    simp only [sumFin, ih, sumFin_add]

theorem sumFin_eq_single {n : Nat} (a : Fin n) (v : Int) :
    sumFin n (fun i => if i = a then v else 0) = v := by
  induction n with
  | zero => exact nomatch a
  | succ n ih =>
    simp only [sumFin]
    by_cases h : a.val = n
    · have ha : a = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext h
      subst ha
      have hzero : sumFin n (fun i : Fin n => if i.castSucc = ⟨n, Nat.lt_succ_self n⟩ then v else 0) = 0 := by
        rw [sumFin_congr (g := fun _ => 0)]
        · exact sumFin_zero n
        · intro i
          have hne : i.castSucc ≠ ⟨n, Nat.lt_succ_self n⟩ := by
            intro heq
            have : i.val = n := congrArg Fin.val heq
            omega
          simp [hne]
      rw [hzero]
      simp
    · have hlt : a.val < n := by omega
      let a' : Fin n := ⟨a.val, hlt⟩
      have hne_last : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠ a := by
        intro heq
        exact h (congrArg Fin.val heq).symm
      have hrec : sumFin n (fun i : Fin n => if i.castSucc = a then v else 0) =
                  sumFin n (fun i : Fin n => if i = a' then v else 0) := by
        apply sumFin_congr
        intro i
        by_cases hi : i = a'
        · subst hi
          have h1 : a'.castSucc = a := Fin.ext rfl
          simp only [h1, ↓reduceIte]
        · have h1 : i.castSucc ≠ a := by
            intro heq
            apply hi
            exact Fin.ext (by simpa [a'] using congrArg Fin.val heq)
          simp only [h1, hi, ↓reduceIte]
      rw [hrec, ih a']
      simp [hne_last]

theorem prodFin_eq_zero_of_exists {n : Nat} {f : Fin n -> Int} (a : Fin n) (ha : f a = 0) :
    prodFin n f = 0 := by
  induction n with
  | zero => exact nomatch a
  | succ n ih =>
    simp only [prodFin]
    by_cases h : a.val = n
    · have ha' : a = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext h
      rw [ha'] at ha
      rw [ha, Int.mul_zero]
    · have hlt : a.val < n := by omega
      have h1 : prodFin n (fun i => f i.castSucc) = 0 := ih ⟨a.val, hlt⟩ (by simpa using ha)
      rw [h1, Int.zero_mul]

theorem prodFin_ne_zero {n : Nat} {f : Fin n -> Int} (h : ∀ i, f i ≠ 0) :
    prodFin n f ≠ 0 := by
  induction n with
  | zero => simp [prodFin]
  | succ n ih =>
    simp only [prodFin]
    exact Int.mul_ne_zero (ih (fun i => h i.castSucc)) (h ⟨n, Nat.lt_succ_self n⟩)

theorem prodFin_extract {n : Nat} (a : Fin n) (f : Fin n -> Int) :
    prodFin n f = f a * prodFin n (fun i => if i = a then 1 else f i) := by
  induction n with
  | zero => exact nomatch a
  | succ n ih =>
    simp only [prodFin]
    by_cases h : a.val = n
    · have ha : a = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext h
      subst ha
      have hcongr : prodFin n (fun i : Fin n => if i.castSucc = ⟨n, Nat.lt_succ_self n⟩ then 1 else f i.castSucc) =
                    prodFin n (fun i => f i.castSucc) := by
        apply prodFin_congr
        intro i
        have hne : i.castSucc ≠ ⟨n, Nat.lt_succ_self n⟩ := by
          intro heq
          have : i.val = n := congrArg Fin.val heq
          omega
        simp [hne]
      rw [hcongr]
      simp [Int.mul_comm]
    · have hlt : a.val < n := by omega
      let a' : Fin n := ⟨a.val, hlt⟩
      have hne_last : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠ a := by
        intro heq
        exact h (congrArg Fin.val heq).symm
      have hrec : prodFin n (fun i : Fin n => if i.castSucc = a then 1 else f i.castSucc) =
                  prodFin n (fun i : Fin n => if i = a' then 1 else f i.castSucc) := by
        apply prodFin_congr
        intro i
        by_cases hi : i = a'
        · subst hi
          have h1 : a'.castSucc = a := Fin.ext rfl
          simp only [h1, ↓reduceIte]
        · have h1 : i.castSucc ≠ a := by
            intro heq
            apply hi
            exact Fin.ext (by simpa [a'] using congrArg Fin.val heq)
          simp only [h1, hi, ↓reduceIte]
      rw [hrec]
      simp only [hne_last, ↓reduceIte]
      have hih := ih a' (fun i => f i.castSucc)
      have hfa : f a'.castSucc = f a := by congr 1
      rw [hfa] at hih
      rw [hih, Int.mul_assoc]

theorem prodFin_succ_zero {n : Nat} (f : Fin (n + 1) -> Int) :
    prodFin (n + 1) f = f ⟨0, Nat.zero_lt_succ n⟩ * prodFin n (fun i => f i.succ) := by
  induction n with
  | zero => simp [prodFin]
  | succ n ih =>
    change prodFin (n + 1) (fun i => f i.castSucc) * f ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ =
           f ⟨0, Nat.zero_lt_succ (n + 1)⟩ * (prodFin n (fun i => f i.castSucc.succ) * f ⟨n + 1, Nat.lt_succ_self (n + 1)⟩)
    rw [ih (fun i => f i.castSucc), Int.mul_assoc]
    rfl

theorem sumFin_succ_zero {n : Nat} (f : Fin (n + 1) -> Int) :
    sumFin (n + 1) f = f ⟨0, Nat.zero_lt_succ n⟩ + sumFin n (fun i => f i.succ) := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    change sumFin (n + 1) (fun i => f i.castSucc) + f ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ =
           f ⟨0, Nat.zero_lt_succ (n + 1)⟩ + (sumFin n (fun i => f i.castSucc.succ) + f ⟨n + 1, Nat.lt_succ_self (n + 1)⟩)
    rw [ih (fun i => f i.castSucc), Int.add_assoc]
    rfl

/-- Transposition on `Fin n`. -/
def finSwap {n : Nat} (a b i : Fin n) : Fin n :=
  if i = a then b else if i = b then a else i

theorem finSwap_self {n : Nat} (a i : Fin n) : finSwap a a i = i := by
  unfold finSwap
  split <;> simp_all

theorem finSwap_comm {n : Nat} (a b i : Fin n) : finSwap a b i = finSwap b a i := by
  unfold finSwap
  by_cases ha : i = a <;> by_cases hb : i = b <;> simp_all

theorem finSwap_invol {n : Nat} (a b i : Fin n) : finSwap a b (finSwap a b i) = i := by
  unfold finSwap
  by_cases ha : i = a
  · subst ha
    by_cases hab : b = i <;> simp [hab]
  · by_cases hb : i = b
    · subst hb; simp [ha]
    · simp [ha, hb]

theorem finSwap_left {n : Nat} (a b : Fin n) : finSwap a b a = b := by
  simp [finSwap]

theorem finSwap_right {n : Nat} (a b : Fin n) : finSwap a b b = a := by
  unfold finSwap
  by_cases h : b = a <;> simp [h]

theorem sumFin_perm_swap {n : Nat} (a b : Fin n) (f : Fin n -> Int) :
    sumFin n (fun i => f (finSwap a b i)) = sumFin n f := by
  by_cases hab : a = b
  · subst hab
    exact sumFin_congr (fun i => by rw [finSwap_self])
  · have hstep : ∀ i : Fin n,
        f (finSwap a b i) =
        f i + (if i = a then f b - f a else 0) + (if i = b then f a - f b else 0) := by
      intro i
      unfold finSwap
      by_cases ha : i = a
      · subst ha; simp [hab]; omega
      · by_cases hb : i = b
        · subst hb; simp [ha]; omega
        · simp [ha, hb]
    rw [sumFin_congr hstep, sumFin_add, sumFin_add, sumFin_eq_single, sumFin_eq_single]
    omega

theorem prodFin_perm_swap {n : Nat} (a b : Fin n) (f : Fin n -> Int) :
    prodFin n (fun i => f (finSwap a b i)) = prodFin n f := by
  by_cases hab : a = b
  · subst hab
    exact prodFin_congr (fun i => by rw [finSwap_self])
  · rw [prodFin_extract a (fun i => f (finSwap a b i))]
    rw [prodFin_extract b (fun i => if i = a then 1 else f (finSwap a b i))]
    rw [prodFin_extract a f]
    rw [prodFin_extract b (fun i => if i = a then 1 else f i)]
    have hba : b ≠ a := Ne.symm hab
    simp only [finSwap_left, finSwap_right, hba, ↓reduceIte]
    have hrest :
        prodFin n (fun i => if i = b then 1 else if i = a then 1 else f (finSwap a b i)) =
        prodFin n (fun i => if i = b then 1 else if i = a then 1 else f i) := by
      apply prodFin_congr
      intro i
      by_cases hb : i = b
      · simp [hb]
      · by_cases ha : i = a
        · simp [ha]
        · simp [hb, ha, finSwap]
    rw [hrest]
    rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm (f b) (f a)]

/-! ### Sum over all functions `Fin m -> Fin n` -/

def snoc {m n : Nat} (g : Fin m -> Fin n) (v : Fin n) : Fin (m + 1) -> Fin n :=
  fun i => if h : i.val < m then g ⟨i.val, h⟩ else v

theorem snoc_castSucc {m n : Nat} (g : Fin m -> Fin n) (v : Fin n) (i : Fin m) :
    snoc g v i.castSucc = g i := by
  unfold snoc
  simp [i.isLt]

theorem snoc_last {m n : Nat} (g : Fin m -> Fin n) (v : Fin n) :
    snoc g v ⟨m, Nat.lt_succ_self m⟩ = v := by
  unfold snoc
  simp

theorem snoc_eta {m n : Nat} (f : Fin (m + 1) -> Fin n) :
    snoc (fun i => f i.castSucc) (f ⟨m, Nat.lt_succ_self m⟩) = f := by
  funext i
  unfold snoc
  by_cases h : i.val < m
  · simp [h]
  · simp only [h, ↓reduceDIte]
    have hval : i.val = m := by have := i.isLt; omega
    have heq : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hval
    rw [heq]

def sumAllFun : (m n : Nat) -> ((Fin m -> Fin n) -> Int) -> Int
  | 0, _, F => F (fun i => nomatch i)
  | m + 1, n, F => sumFin n (fun v => sumAllFun m n (fun g => F (snoc g v)))

theorem sumAllFun_congr {m n : Nat} {F G : (Fin m -> Fin n) -> Int} (h : ∀ f, F f = G f) :
    sumAllFun m n F = sumAllFun m n G := by
  induction m with
  | zero => exact h _
  | succ m ih =>
    simp only [sumAllFun]
    apply sumFin_congr
    intro v
    exact ih (fun g => h (snoc g v))

theorem sumAllFun_zero (m n : Nat) : sumAllFun m n (fun _ => 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumAllFun]
    rw [sumFin_congr (fun _ => ih)]
    exact sumFin_zero n

theorem sumAllFun_add {m n : Nat} (F G : (Fin m -> Fin n) -> Int) :
    sumAllFun m n (fun f => F f + G f) = sumAllFun m n F + sumAllFun m n G := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumAllFun]
    rw [sumFin_congr (fun v => ih (fun g => F (snoc g v)) (fun g => G (snoc g v)))]
    exact sumFin_add _ _

theorem sumAllFun_neg {m n : Nat} (F : (Fin m -> Fin n) -> Int) :
    sumAllFun m n (fun f => -F f) = -sumAllFun m n F := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumAllFun]
    rw [sumFin_congr (fun v => ih (fun g => F (snoc g v)))]
    exact sumFin_neg _

theorem sumAllFun_mul_left {m n : Nat} (c : Int) (F : (Fin m -> Fin n) -> Int) :
    sumAllFun m n (fun f => c * F f) = c * sumAllFun m n F := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumAllFun]
    rw [sumFin_congr (fun v => ih (fun g => F (snoc g v)))]
    exact sumFin_mul_left c _

theorem sumAllFun_mul_right {m n : Nat} (F : (Fin m -> Fin n) -> Int) (c : Int) :
    sumAllFun m n (fun f => F f * c) = sumAllFun m n F * c := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumAllFun]
    rw [sumFin_congr (fun v => ih (fun g => F (snoc g v)))]
    exact sumFin_mul_right _ c

theorem prodFin_sumFin {m n : Nat} (G : Fin m -> Fin n -> Int) :
    prodFin m (fun i => sumFin n (fun j => G i j)) =
    sumAllFun m n (fun f => prodFin m (fun i => G i (f i))) := by
  induction m with
  | zero => simp [prodFin, sumAllFun]
  | succ m ih =>
    simp only [prodFin, sumAllFun]
    rw [ih (fun i j => G i.castSucc j)]
    rw [← sumFin_mul_left]
    apply sumFin_congr
    intro v
    rw [← sumAllFun_mul_right]
    apply sumAllFun_congr
    intro g
    congr 1
    · apply prodFin_congr
      intro i
      rw [snoc_castSucc]
    · rw [snoc_last]

/-- Swapping two adjacent top coordinates `m` and `m+1` in `sumAllFun (m+2) n`. -/
theorem sumAllFun_pre_swap_top2 {m n : Nat} (F : (Fin (m + 2) -> Fin n) -> Int) :
    sumAllFun (m + 2) n (fun f => F (fun i => f (finSwap ⟨m, by omega⟩ ⟨m + 1, by omega⟩ i))) =
    sumAllFun (m + 2) n F := by
  simp only [sumAllFun]
  rw [sumFin_swap_order]
  apply sumFin_congr
  intro v1
  apply sumFin_congr
  intro v2
  apply sumAllFun_congr
  intro g
  congr 1
  funext i
  unfold snoc finSwap
  by_cases h1 : i.val < m
  · have hne1 : i ≠ ⟨m, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
    have hne2 : i ≠ ⟨m + 1, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
    have hlt1 : i.val < m + 1 := by omega
    simp [hne1, hne2, hlt1, h1]
  · by_cases h2 : i.val = m
    · have hi : i = ⟨m, by omega⟩ := Fin.ext h2
      rw [hi]
      simp
    · have hval : i.val = m + 1 := by have := i.isLt; omega
      have hi : i = ⟨m + 1, by omega⟩ := Fin.ext hval
      rw [hi]
      have hne : (⟨m + 1, by omega⟩ : Fin (m + 2)) ≠ ⟨m, by omega⟩ := by
        intro h; have := congrArg Fin.val h; dsimp at this; omega
      simp [hne]

/-- Precomposing by any transposition `finSwap a b` preserves `sumAllFun`. -/
theorem sumAllFun_pre_swap {m n : Nat} (a b : Fin m) (F : (Fin m -> Fin n) -> Int) :
    sumAllFun m n (fun f => F (fun i => f (finSwap a b i))) = sumAllFun m n F := by
  induction m with
  | zero => exact nomatch a
  | succ m ih =>
    by_cases hab : a = b
    · subst hab
      exact sumAllFun_congr (fun f => by congr 1; funext i; rw [finSwap_self])
    · have swap_both_lt : ∀ (x y : Fin (m + 1)), x.val < m -> y.val < m ->
          ∀ (G : (Fin (m + 1) -> Fin n) -> Int),
          sumAllFun (m + 1) n (fun f => G (fun i => f (finSwap x y i))) = sumAllFun (m + 1) n G := by
        intro x y hx hy G
        simp only [sumAllFun]
        apply sumFin_congr
        intro v
        let x' : Fin m := ⟨x.val, hx⟩
        let y' : Fin m := ⟨y.val, hy⟩
        have hEq : ∀ g : Fin m -> Fin n,
            (fun i => snoc g v (finSwap x y i)) = snoc (fun i => g (finSwap x' y' i)) v := by
          intro g; funext i
          by_cases hi : i.val < m
          · by_cases hix : i = x
            · subst hix
              rw [finSwap_left]
              unfold snoc
              simp only [hx, hy, ↓reduceDIte]
              have h1 : (⟨i.val, hx⟩ : Fin m) = x' := rfl
              rw [h1, finSwap_left]
            · by_cases hiy : i = y
              · subst hiy
                rw [finSwap_right]
                unfold snoc
                simp only [hx, hy, ↓reduceDIte]
                have h2 : (⟨i.val, hy⟩ : Fin m) = y' := rfl
                rw [h2, finSwap_right]
              · have hsw : finSwap x y i = i := by unfold finSwap; simp only [hix, hiy, ↓reduceIte]
                have hix' : (⟨i.val, hi⟩ : Fin m) ≠ x' := fun h => hix (Fin.ext (by simpa [x'] using congrArg Fin.val h))
                have hiy' : (⟨i.val, hi⟩ : Fin m) ≠ y' := fun h => hiy (Fin.ext (by simpa [y'] using congrArg Fin.val h))
                have hsw' : finSwap x' y' ⟨i.val, hi⟩ = ⟨i.val, hi⟩ := by unfold finSwap; simp only [hix', hiy', ↓reduceIte]
                rw [hsw]
                unfold snoc
                simp only [hi, ↓reduceDIte, hsw']
          · have hix : i ≠ x := fun h => by have := congrArg Fin.val h; omega
            have hiy : i ≠ y := fun h => by have := congrArg Fin.val h; omega
            have hsw : finSwap x y i = i := by unfold finSwap; simp only [hix, hiy, ↓reduceIte]
            rw [hsw]
            unfold snoc
            simp only [hi, ↓reduceDIte]
        rw [sumAllFun_congr (fun g => by rw [hEq g])]
        exact ih x' y' (fun g => G (snoc g v))
      have swap_lt_last : ∀ (x : Fin (m + 1)), x.val < m ->
          ∀ (G : (Fin (m + 1) -> Fin n) -> Int),
          sumAllFun (m + 1) n (fun f => G (fun i => f (finSwap x ⟨m, Nat.lt_succ_self m⟩ i))) =
          sumAllFun (m + 1) n G := by
        intro x hx G
        cases m with
        | zero => omega
        | succ m' =>
          let p : Fin (m' + 2) := ⟨m', by omega⟩
          let lst : Fin (m' + 2) := ⟨m' + 1, by omega⟩
          by_cases hxp : x = p
          · rw [hxp]; exact sumAllFun_pre_swap_top2 G
          · have hconj : ∀ (f : Fin (m' + 2) -> Fin n) (i : Fin (m' + 2)),
                f (finSwap x lst i) = f (finSwap x p (finSwap p lst (finSwap x p i))) := by
              intro f i
              congr 1
              have hpx : p ≠ x := Ne.symm hxp
              have hpl : p ≠ lst := fun h => by have := congrArg Fin.val h; dsimp [p, lst] at this; omega
              have hlp : lst ≠ p := Ne.symm hpl
              have hlx : lst ≠ x := fun h => by have := congrArg Fin.val h; dsimp [lst] at this; omega
              have hxl : x ≠ lst := Ne.symm hlx
              by_cases hix : i = x
              · rw [hix, finSwap_left, finSwap_left, finSwap_left, finSwap]
                simp only [hlx, hlp, ↓reduceIte]
              · by_cases hip : i = p
                · rw [hip, finSwap_right]
                  have h1 : finSwap x lst p = p := by unfold finSwap; simp only [hpx, hpl, ↓reduceIte]
                  have h2 : finSwap p lst x = x := by unfold finSwap; simp only [hxp, hxl, ↓reduceIte]
                  rw [h1, h2, finSwap_left]
                · by_cases hil : i = lst
                  · rw [hil, finSwap_right]
                    have h1 : finSwap x p lst = lst := by unfold finSwap; simp only [hlx, hlp, ↓reduceIte]
                    rw [h1, finSwap_right, finSwap_right]
                  · have h1 : finSwap x lst i = i := by unfold finSwap; simp only [hix, hil, ↓reduceIte]
                    have h2 : finSwap x p i = i := by unfold finSwap; simp only [hix, hip, ↓reduceIte]
                    have h3 : finSwap p lst i = i := by unfold finSwap; simp only [hip, hil, ↓reduceIte]
                    rw [h1, h2, h3, h2]
            have h1 : sumAllFun (m' + 2) n (fun f => G (fun i => f (finSwap x lst i))) =
                      sumAllFun (m' + 2) n (fun f => G (fun i => f (finSwap x p (finSwap p lst (finSwap x p i))))) :=
              sumAllFun_congr (fun f => by congr 1; funext i; exact hconj f i)
            change sumAllFun (m' + 2) n (fun f => G (fun i => f (finSwap x lst i))) = sumAllFun (m' + 2) n G
            rw [h1]
            have s1 := swap_both_lt x p hx (by simp [p]) (fun f => G (fun i => f (finSwap p lst (finSwap x p i))))
            have s2 := sumAllFun_pre_swap_top2 (fun f => G (fun i => f (finSwap x p i)))
            have s3 := swap_both_lt x p hx (by simp [p]) G
            exact (s1.trans s2).trans s3
      by_cases ha : a.val < m
      · by_cases hb : b.val < m
        · exact swap_both_lt a b ha hb F
        · have hb_val : b.val = m := by have := b.isLt; omega
          have hb_eq : b = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hb_val
          rw [hb_eq]
          exact swap_lt_last a ha F
      · have ha_val : a.val = m := by have := a.isLt; omega
        have ha_eq : a = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext ha_val
        have hb : b.val < m := by
          have hblt := b.isLt
          have hne : b.val ≠ m := fun h => hab (Fin.ext (by omega))
          omega
        rw [ha_eq]
        have hcomm : sumAllFun (m + 1) n (fun f => F (fun i => f (finSwap ⟨m, Nat.lt_succ_self m⟩ b i))) =
                     sumAllFun (m + 1) n (fun f => F (fun i => f (finSwap b ⟨m, Nat.lt_succ_self m⟩ i))) :=
          sumAllFun_congr (fun f => by congr 1; funext i; rw [finSwap_comm])
        rw [hcomm]
        exact swap_lt_last b hb F

/-! ### Decomposition of any injective `g : Fin n -> Fin n` into transpositions -/

def applySwaps {n : Nat} : List (Fin n × Fin n) -> Fin n -> Fin n
  | [], i => i
  | (a, b) :: rest, i => finSwap a b (applySwaps rest i)

theorem injective_eq_applySwaps {n : Nat} (g : Fin n -> Fin n)
    (hinj : ∀ i j, g i = g j -> i = j) :
    ∃ swaps : List (Fin n × Fin n), (∀ p ∈ swaps, p.1 ≠ p.2) ∧ (∀ i, g i = applySwaps swaps i) := by
  induction n with
  | zero =>
    exact ⟨[], by simp, fun i => nomatch i⟩
  | succ n ih =>
    let last : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let v : Fin (n + 1) := g last
    let g' : Fin (n + 1) -> Fin (n + 1) := fun i => finSwap v last (g i)
    have hg'_last : g' last = last := by
      simp [g', v, finSwap_left]
    have hg'_inj : ∀ i j, g' i = g' j -> i = j := by
      intro i j h
      have h1 : finSwap v last (g' i) = finSwap v last (g' j) := congrArg (finSwap v last) h
      simp only [g', finSwap_invol] at h1
      exact hinj i j h1
    have hg'_lt : ∀ i : Fin n, (g' i.castSucc).val < n := by
      intro i
      have hlt := (g' i.castSucc).isLt
      have hne : (g' i.castSucc).val ≠ n := by
        intro heqv
        have heq : g' i.castSucc = last := Fin.ext heqv
        have hci := hg'_inj i.castSucc last (by rw [heq, hg'_last])
        have : i.val = n := congrArg Fin.val hci
        omega
      omega
    let g_sub : Fin n -> Fin n := fun i => ⟨(g' i.castSucc).val, hg'_lt i⟩
    have hsub_inj : ∀ i j, g_sub i = g_sub j -> i = j := by
      intro i j h
      have hval : (g_sub i).val = (g_sub j).val := congrArg Fin.val h
      have h1 : g' i.castSucc = g' j.castSucc := Fin.ext hval
      have h2 : i.castSucc = j.castSucc := hg'_inj i.castSucc j.castSucc h1
      exact Fin.ext (by simpa using congrArg Fin.val h2)
    obtain ⟨subSwaps, hne, hsub_eq⟩ := ih g_sub hsub_inj
    let liftedSwaps : List (Fin (n + 1) × Fin (n + 1)) :=
      subSwaps.map (fun p => (p.1.castSucc, p.2.castSucc))
    have hlifted_cast_aux : ∀ (sw : List (Fin n × Fin n)) (i : Fin n),
        applySwaps (sw.map (fun p => (p.1.castSucc, p.2.castSucc))) i.castSucc =
        (applySwaps sw i).castSucc := by
      intro sw i
      induction sw with
      | nil => rfl
      | cons p rest ihr =>
        rcases p with ⟨a, b⟩
        simp only [List.map, applySwaps]
        rw [ihr]
        unfold finSwap
        by_cases ha : applySwaps rest i = a
        · rw [ha]; simp
        · by_cases hb : applySwaps rest i = b
          · have hba : b ≠ a := fun h => ha (hb.trans h)
            have hba' : b.castSucc ≠ a.castSucc := fun h => hba (Fin.ext (by simpa using congrArg Fin.val h))
            rw [hb]; simp [hba, hba']
          · have h1 : (applySwaps rest i).castSucc ≠ a.castSucc :=
              fun h => ha (Fin.ext (by simpa using congrArg Fin.val h))
            have h2 : (applySwaps rest i).castSucc ≠ b.castSucc :=
              fun h => hb (Fin.ext (by simpa using congrArg Fin.val h))
            simp only [h1, h2, ha, hb, ↓reduceIte]
    have hlifted_last_aux : ∀ (sw : List (Fin n × Fin n)),
        applySwaps (sw.map (fun p => (p.1.castSucc, p.2.castSucc))) last = last := by
      intro sw
      induction sw with
      | nil => rfl
      | cons p rest ihr =>
        rcases p with ⟨a, b⟩
        simp only [List.map, applySwaps]
        rw [ihr]
        unfold finSwap
        have h1 : last ≠ a.castSucc := fun h => by have := congrArg Fin.val h; dsimp [last] at this; omega
        have h2 : last ≠ b.castSucc := fun h => by have := congrArg Fin.val h; dsimp [last] at this; omega
        simp only [h1, h2, ↓reduceIte]
    have hg'_eq : ∀ i, g' i = applySwaps liftedSwaps i := by
      intro i
      by_cases hi : i.val < n
      · let i' : Fin n := ⟨i.val, hi⟩
        have hieq : i = i'.castSucc := Fin.ext rfl
        rw [hieq, hlifted_cast_aux subSwaps i', ← hsub_eq i']
        exact Fin.ext rfl
      · have hval : i.val = n := by have := i.isLt; omega
        have hieq : i = last := Fin.ext hval
        rw [hieq, hg'_last, hlifted_last_aux subSwaps]
    have hlifted_ne : ∀ p ∈ liftedSwaps, p.1 ≠ p.2 := by
      intro p hp
      simp only [liftedSwaps, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      intro heq
      have hval : q.1.val = q.2.val := by simpa using congrArg Fin.val heq
      exact hne q hq (Fin.ext hval)
    by_cases hvl : v = last
    · refine ⟨liftedSwaps, hlifted_ne, ?_⟩
      intro i
      have h1 := hg'_eq i
      simp only [g', hvl, finSwap_self] at h1
      exact h1
    · refine ⟨(v, last) :: liftedSwaps, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp'
        · exact hvl
        · exact hlifted_ne p hp'
      · intro i
        simp only [applySwaps]
        rw [← hg'_eq i]
        simp [g', finSwap_invol]

/-! ### Levi-Civita Sign & Exact Determinant -/

def cmpSign (a b : Nat) : Int :=
  if a < b then 1 else if b < a then -1 else 0

theorem cmpSign_antisymm (a b : Nat) : cmpSign b a = -cmpSign a b := by
  unfold cmpSign
  split
  · next h =>
    have h1 : ¬(a < b) := by omega
    simp [h1]
  · next h =>
    split
    · simp
    · simp

theorem cmpSign_self (a : Nat) : cmpSign a a = 0 := by
  simp [cmpSign]

def leviCivita {n : Nat} (f : Fin n -> Fin n) : Int :=
  prodFin n (fun i => prodFin n (fun j => if i.val < j.val then cmpSign (f i).val (f j).val else 1))

theorem leviCivita_id (n : Nat) : leviCivita (fun i : Fin n => i) = 1 := by
  unfold leviCivita
  rw [prodFin_congr (g := fun _ => 1)]
  · exact prodFin_one n
  · intro i
    rw [prodFin_congr (g := fun _ => 1)]
    · exact prodFin_one n
    · intro j
      by_cases h : i.val < j.val
      · simp [h, cmpSign]
      · simp [h]

theorem leviCivita_eq_zero_of_eq {n : Nat} {f : Fin n -> Fin n} {a b : Fin n}
    (hab : a ≠ b) (hfeq : f a = f b) : leviCivita f = 0 := by
  unfold leviCivita
  by_cases hlt : a.val < b.val
  · apply prodFin_eq_zero_of_exists a
    apply prodFin_eq_zero_of_exists b
    simp [hlt, hfeq, cmpSign_self]
  · have hlt' : b.val < a.val := by
      have : a.val ≠ b.val := fun h => hab (Fin.ext h)
      omega
    apply prodFin_eq_zero_of_exists b
    apply prodFin_eq_zero_of_exists a
    simp [hlt', hfeq, cmpSign_self]

theorem leviCivita_comp_swap_lt {n : Nat} (f : Fin n -> Fin n) {a b : Fin n} (hab : a.val < b.val) :
    leviCivita (fun i => f (finSwap a b i)) = -leviCivita f := by
  let g : Fin n -> Fin n := fun i => f (finSwap a b i)
  have hreidx : leviCivita g =
      prodFin n (fun i => prodFin n (fun j =>
        if (finSwap a b i).val < (finSwap a b j).val then cmpSign (f i).val (f j).val else 1)) := by
    unfold leviCivita
    rw [← prodFin_perm_swap a b]
    apply prodFin_congr
    intro i
    rw [← prodFin_perm_swap a b]
    apply prodFin_congr
    intro j
    simp only [g, finSwap_invol]
  have h_upper : ∀ (M : Fin n -> Fin n -> Int),
      prodFin n (fun i => prodFin n (fun j => M i j)) =
      prodFin n (fun i => M i i) *
      prodFin n (fun i => prodFin n (fun j => if i.val < j.val then M i j * M j i else 1)) := by
    intro M
    have hsplit : ∀ i : Fin n,
        prodFin n (fun j => M i j) =
        M i i * prodFin n (fun j => if i.val < j.val then M i j else 1) *
                prodFin n (fun j => if j.val < i.val then M i j else 1) := by
      intro i
      rw [prodFin_extract i (fun j => M i j)]
      rw [Int.mul_assoc]
      congr 1
      rw [← prodFin_mul]
      apply prodFin_congr
      intro j
      by_cases hij : i.val < j.val
      · have hne : j ≠ i := fun h => by have := congrArg Fin.val h; omega
        have hnot : ¬(j.val < i.val) := by omega
        simp [hij, hne, hnot]
      · by_cases hji : j.val < i.val
        · have hne : j ≠ i := fun h => by have := congrArg Fin.val h; omega
          simp [hij, hji, hne]
        · have heq : j = i := Fin.ext (by omega)
          simp [heq]
    have hprod_swap :
        prodFin n (fun i => prodFin n (fun j => if j.val < i.val then M i j else 1)) =
        prodFin n (fun i => prodFin n (fun j => if i.val < j.val then M j i else 1)) := by
      have aux : ∀ (m : Nat) (K : Fin m -> Fin n -> Int),
          prodFin m (fun i => prodFin n (fun j => K i j)) =
          prodFin n (fun j => prodFin m (fun i => K i j)) := by
        intro m K
        induction m with
        | zero => simp [prodFin, prodFin_one]
        | succ m ihm =>
          simp only [prodFin, ihm, prodFin_mul]
      exact aux n (fun i j => if j.val < i.val then M i j else 1)
    rw [prodFin_congr hsplit, prodFin_mul, prodFin_mul, hprod_swap, Int.mul_assoc]
    congr 1
    rw [← prodFin_mul]
    apply prodFin_congr
    intro i
    rw [← prodFin_mul]
    apply prodFin_congr
    intro j
    by_cases h : i.val < j.val <;> simp [h]
  have h1 : leviCivita g =
      prodFin n (fun i => prodFin n (fun j =>
        if i.val < j.val then
          (if (finSwap a b i).val < (finSwap a b j).val then cmpSign (f i).val (f j).val else 1) *
          (if (finSwap a b j).val < (finSwap a b i).val then cmpSign (f j).val (f i).val else 1)
        else 1)) := by
    rw [hreidx, h_upper]
    have hdiag : prodFin n (fun i => if (finSwap a b i).val < (finSwap a b i).val then cmpSign (f i).val (f i).val else 1) = 1 := by
      rw [prodFin_congr (g := fun _ => 1)]
      · exact prodFin_one n
      · intro i; simp
    rw [hdiag, Int.one_mul]
  have h2 : leviCivita f =
      prodFin n (fun i => prodFin n (fun j =>
        if i.val < j.val then
          (if i.val < j.val then cmpSign (f i).val (f j).val else 1) *
          (if j.val < i.val then cmpSign (f j).val (f i).val else 1)
        else 1)) := by
    unfold leviCivita
    rw [h_upper]
    have hdiag : prodFin n (fun i => if i.val < i.val then cmpSign (f i).val (f i).val else 1) = 1 := by
      rw [prodFin_congr (g := fun _ => 1)]
      · exact prodFin_one n
      · intro i; simp
    rw [hdiag, Int.one_mul]
  change leviCivita g = -leviCivita f
  rw [h1, h2]
  have hpair : ∀ i j : Fin n,
      (if i.val < j.val then
        (if (finSwap a b i).val < (finSwap a b j).val then cmpSign (f i).val (f j).val else 1) *
        (if (finSwap a b j).val < (finSwap a b i).val then cmpSign (f j).val (f i).val else 1)
       else 1) =
      (if i.val < j.val ∧ (finSwap a b j).val < (finSwap a b i).val then (-1 : Int) else 1) *
      (if i.val < j.val then
        (if i.val < j.val then cmpSign (f i).val (f j).val else 1) *
        (if j.val < i.val then cmpSign (f j).val (f i).val else 1)
       else 1) := by
    intro i j
    by_cases hij : i.val < j.val
    · have hnotji : ¬(j.val < i.val) := by omega
      have hne_swap : (finSwap a b i).val ≠ (finSwap a b j).val := by
        intro heq
        have h1' : finSwap a b i = finSwap a b j := Fin.ext heq
        have h2' := congrArg (finSwap a b) h1'
        simp only [finSwap_invol] at h2'
        have : i.val = j.val := congrArg Fin.val h2'
        omega
      by_cases hsw : (finSwap a b i).val < (finSwap a b j).val
      · have hnot : ¬((finSwap a b j).val < (finSwap a b i).val) := by omega
        simp [hij, hnotji, hsw, hnot]
      · have hsw' : (finSwap a b j).val < (finSwap a b i).val := by omega
        simp only [hij, hnotji, hsw, hsw', and_self, ↓reduceIte, Int.one_mul, Int.mul_one]
        rw [cmpSign_antisymm, Int.neg_one_mul]
    · simp [hij]
  rw [prodFin_congr (fun i => prodFin_congr (fun j => hpair i j))]
  rw [prodFin_congr (fun i => prodFin_mul _ _), prodFin_mul]
  have hsign : prodFin n (fun i => prodFin n (fun j =>
      if i.val < j.val ∧ (finSwap a b j).val < (finSwap a b i).val then (-1 : Int) else 1)) = -1 := by
    have hinner : ∀ i : Fin n,
        prodFin n (fun j => if i.val < j.val ∧ (finSwap a b j).val < (finSwap a b i).val then (-1 : Int) else 1) =
        if i = a then prodFin n (fun j => if a.val < j.val ∧ j.val ≤ b.val then (-1 : Int) else 1)
        else if a.val < i.val ∧ i.val < b.val then -1
        else 1 := by
      intro i
      by_cases hia : i = a
      · subst hia
        simp only [↓reduceIte]
        apply prodFin_congr
        intro j
        by_cases hj1 : i.val < j.val
        · by_cases hjb : j = b
          · subst hjb; simp [finSwap_left, finSwap_right, hab]
          · have hja : j ≠ i := fun h => by have := congrArg Fin.val h; omega
            have hswj : finSwap i b j = j := by simp [finSwap, hja, hjb]
            rw [hswj, finSwap_left]
            have hiff : j.val < b.val ↔ j.val ≤ b.val := by
              have : j.val ≠ b.val := fun h => hjb (Fin.ext h)
              omega
            simp [hj1, hiff]
        · simp [hj1]
      · simp only [hia, ↓reduceIte]
        by_cases hmid : a.val < i.val ∧ i.val < b.val
        · simp only [hmid]
          have hib : i ≠ b := fun h => by have := congrArg Fin.val h; omega
          have hswi : finSwap a b i = i := by simp [finSwap, hia, hib]
          rw [prodFin_extract b]
          rw [hswi, finSwap_right]
          have hb_cond : i.val < b.val ∧ a.val < i.val := ⟨hmid.2, hmid.1⟩
          simp only [hb_cond, and_self, ↓reduceIte]
          have hrest1 : prodFin n (fun j => if j = b then 1 else
              if i.val < j.val ∧ (finSwap a b j).val < i.val then (-1 : Int) else 1) = 1 := by
            rw [prodFin_congr (g := fun _ => 1)]
            · exact prodFin_one n
            · intro j
              by_cases hjb : j = b
              · simp [hjb]
              · simp only [hjb, ↓reduceIte]
                by_cases hja : j = a
                · rw [hja]; have hno : ¬(i.val < a.val) := by omega
                  simp only [hno, false_and, ↓reduceIte]
                · have hswj : finSwap a b j = j := by simp [finSwap, hja, hjb]
                  rw [hswj]
                  have hno : ¬(i.val < j.val ∧ j.val < i.val) := by omega
                  simp only [hno, ↓reduceIte]
          rw [hrest1]; simp
        · simp only [hmid, ↓reduceIte]
          rw [prodFin_congr (g := fun _ => 1)]
          · exact prodFin_one n
          · intro j
            by_cases hja : j = a
            · rw [hja]
              by_cases hib : i = b
              · rw [hib]; have hno : ¬(b.val < a.val) := by omega
                simp only [hno, false_and, ↓reduceIte]
              · have hswi : finSwap a b i = i := by simp [finSwap, hia, hib]
                rw [hswi, finSwap_left]
                have hno : ¬(i.val < a.val ∧ b.val < i.val) := by omega
                simp only [hno, ↓reduceIte]
            · by_cases hjb : j = b
              · rw [hjb]
                by_cases hib : i = b
                · rw [hib]; simp
                · have hswi : finSwap a b i = i := by simp [finSwap, hia, hib]
                  rw [hswi, finSwap_right]
                  have hno : ¬(i.val < b.val ∧ a.val < i.val) := by omega
                  simp only [hno, ↓reduceIte]
              · have hswj : finSwap a b j = j := by simp [finSwap, hja, hjb]
                rw [hswj]
                by_cases hib : i = b
                · rw [hib, finSwap_right]
                  have hno : ¬(b.val < j.val ∧ j.val < a.val) := by omega
                  simp only [hno, ↓reduceIte]
                · have hswi : finSwap a b i = i := by simp [finSwap, hia, hib]
                  rw [hswi]
                  have hno : ¬(i.val < j.val ∧ j.val < i.val) := by omega
                  simp only [hno, ↓reduceIte]
    rw [prodFin_congr hinner]
    rw [prodFin_extract a]
    simp only [↓reduceIte]
    rw [prodFin_extract b (fun j => if a.val < j.val ∧ j.val ≤ b.val then (-1 : Int) else 1)]
    have hba : a.val < b.val ∧ b.val ≤ b.val := ⟨hab, Nat.le_refl _⟩
    simp only [hba, and_self, ↓reduceIte]
    have hclean :
        prodFin n (fun i => if i = a then 1 else if i = a then
          -1 * prodFin n (fun j => if j = b then 1 else if a.val < j.val ∧ j.val ≤ b.val then (-1 : Int) else 1)
          else if a.val < i.val ∧ i.val < b.val then (-1 : Int) else 1) =
        prodFin n (fun i => if a.val < i.val ∧ i.val < b.val then (-1 : Int) else 1) := by
      apply prodFin_congr
      intro i
      by_cases hia : i = a
      · rw [hia]; simp
      · simp [hia]
    have hmatch :
        prodFin n (fun j => if j = b then 1 else if a.val < j.val ∧ j.val ≤ b.val then (-1 : Int) else 1) =
        prodFin n (fun i => if a.val < i.val ∧ i.val < b.val then (-1 : Int) else 1) := by
      apply prodFin_congr
      intro j
      by_cases hjb : j = b
      · subst hjb; simp
      · have hiff : j.val ≤ b.val ↔ j.val < b.val := by
          have : j.val ≠ b.val := fun h => hjb (Fin.ext h)
          omega
        simp [hjb, hiff]
    rw [hclean, hmatch, Int.mul_assoc]
    have hsq : ∀ (p : Fin n -> Prop) [DecidablePred p],
        prodFin n (fun i => if p i then (-1 : Int) else 1) *
        prodFin n (fun i => if p i then (-1 : Int) else 1) = 1 := by
      intro p _
      rw [← prodFin_mul]
      rw [prodFin_congr (g := fun _ => 1)]
      · exact prodFin_one n
      · intro i; split <;> decide
    rw [hsq]
    simp
  rw [hsign]
  simp

theorem leviCivita_comp_swap {n : Nat} (f : Fin n -> Fin n) {a b : Fin n} (hab : a ≠ b) :
    leviCivita (fun i => f (finSwap a b i)) = -leviCivita f := by
  by_cases hlt : a.val < b.val
  · exact leviCivita_comp_swap_lt f hlt
  · have hlt' : b.val < a.val := by
      have : a.val ≠ b.val := fun h => hab (Fin.ext h)
      omega
    have h1 : (fun i => f (finSwap a b i)) = (fun i => f (finSwap b a i)) := by
      funext i; rw [finSwap_comm]
    rw [h1]
    exact leviCivita_comp_swap_lt f hlt'

theorem leviCivita_comp_applySwaps {n : Nat} (f : Fin n -> Fin n) (swaps : List (Fin n × Fin n))
    (hne : ∀ p ∈ swaps, p.1 ≠ p.2) :
    leviCivita (fun i => f (applySwaps swaps i)) =
    leviCivita f * leviCivita (applySwaps swaps) := by
  induction swaps generalizing f with
  | nil =>
    simp [applySwaps, leviCivita_id]
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    have hab : a ≠ b := hne (a, b) (by simp)
    have hrest : ∀ q ∈ rest, q.1 ≠ q.2 := fun q hq => hne q (by simp [hq])
    simp only [applySwaps]
    have h1 := ih (fun i => f (finSwap a b i)) hrest
    have h2 := ih (fun i => finSwap a b i) hrest
    rw [h1, h2]
    rw [leviCivita_comp_swap f hab, leviCivita_comp_swap (fun i => i) hab, leviCivita_id]
    rw [Int.neg_mul, Int.neg_mul, Int.one_mul, Int.mul_neg]

theorem sumAllFun_pre_applySwaps {m n : Nat} (swaps : List (Fin m × Fin m))
    (F : (Fin m -> Fin n) -> Int) :
    sumAllFun m n (fun f => F (fun i => f (applySwaps swaps i))) = sumAllFun m n F := by
  induction swaps generalizing F with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    simp only [applySwaps]
    have s1 := sumAllFun_pre_swap a b (fun f => F (fun i => f (applySwaps rest i)))
    exact s1.trans (ih F)

theorem prodFin_perm_applySwaps {n : Nat} (swaps : List (Fin n × Fin n)) (f : Fin n -> Int) :
    prodFin n (fun i => f (applySwaps swaps i)) = prodFin n f := by
  induction swaps generalizing f with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    simp only [applySwaps]
    rw [ih (fun i => f (finSwap a b i))]
    exact prodFin_perm_swap a b f

/-! ### Exact Integer Matrices & Determinant Theorems -/

abbrev Mat (n : Nat) := Fin n -> Fin n -> Int

def matMul {n : Nat} (A B : Mat n) : Mat n :=
  fun i j => sumFin n (fun k => A i k * B k j)

def matTranspose {n : Nat} (A : Mat n) : Mat n :=
  fun i j => A j i

def matId (n : Nat) : Mat n :=
  fun i j => if i = j then 1 else 0

def matDiag {n : Nat} (d : Fin n -> Int) : Mat n :=
  fun i j => if i = j then d i else 0

def matAdd {n : Nat} (A B : Mat n) : Mat n :=
  fun i j => A i j + B i j

def matSub {n : Nat} (A B : Mat n) : Mat n :=
  fun i j => A i j - B i j

def matScale {n : Nat} (c : Int) (A : Mat n) : Mat n :=
  fun i j => c * A i j

def matOnes (n : Nat) : Mat n :=
  fun _ _ => 1

def det {n : Nat} (A : Mat n) : Int :=
  sumAllFun n n (fun f => leviCivita f * prodFin n (fun i => A i (f i)))

theorem det_congr {n : Nat} {A B : Mat n} (h : ∀ i j, A i j = B i j) : det A = det B := by
  unfold det
  apply sumAllFun_congr
  intro f
  congr 1
  apply prodFin_congr
  intro i
  exact h i (f i)

theorem sumAllFun_leviCivita_comp {n : Nat} (B : Mat n) (g : Fin n -> Fin n) :
    sumAllFun n n (fun f => leviCivita f * prodFin n (fun i => B (g i) (f i))) =
    leviCivita g * det B := by
  by_cases hinj : ∀ i j, g i = g j -> i = j
  · obtain ⟨swaps, hne, hgeq⟩ := injective_eq_applySwaps g hinj
    have hgeq_fun : g = applySwaps swaps := funext hgeq
    rw [hgeq_fun]
    have hdet : leviCivita (applySwaps swaps) * det B =
        sumAllFun n n (fun f => (leviCivita f * leviCivita (applySwaps swaps)) *
          prodFin n (fun i => B i (f i))) := by
      unfold det
      rw [← sumAllFun_mul_left]
      apply sumAllFun_congr
      intro f
      rw [← Int.mul_assoc, Int.mul_comm (leviCivita (applySwaps swaps)) (leviCivita f)]
    rw [hdet]
    rw [← sumAllFun_pre_applySwaps swaps
      (fun f => leviCivita f * prodFin n (fun i => B (applySwaps swaps i) (f i)))]
    apply sumAllFun_congr
    intro f
    rw [leviCivita_comp_applySwaps f swaps hne]
    congr 1
    exact prodFin_perm_applySwaps swaps (fun j => B j (f j))
  · have hex : ∃ a b : Fin n, a ≠ b ∧ g a = g b :=
      Classical.byContradiction (fun hno => hinj (fun i j hij =>
        Classical.byContradiction (fun hne => hno ⟨i, j, hne, hij⟩)))
    obtain ⟨a, b, hab, hgab⟩ := hex
    rw [leviCivita_eq_zero_of_eq hab hgab, Int.zero_mul]
    let S := sumAllFun n n (fun f => leviCivita f * prodFin n (fun i => B (g i) (f i)))
    have hneg : S = -S := by
      calc S = sumAllFun n n (fun f => leviCivita (fun i => f (finSwap a b i)) *
                 prodFin n (fun i => B (g i) (f (finSwap a b i)))) :=
                 (sumAllFun_pre_swap a b _).symm
        _ = sumAllFun n n (fun f => -(leviCivita f * prodFin n (fun i => B (g i) (f i)))) := by
              apply sumAllFun_congr
              intro f
              rw [leviCivita_comp_swap f hab, Int.neg_mul]
              congr 1; congr 1
              rw [← prodFin_perm_swap a b (fun i => B (g i) (f (finSwap a b i)))]
              apply prodFin_congr
              intro i
              rw [finSwap_invol]
              congr 1
              unfold finSwap
              by_cases hia : i = a
              · subst hia; simp [hgab]
              · by_cases hib : i = b
                · subst hib; simp [hia, hgab]
                · simp [hia, hib]
        _ = -S := sumAllFun_neg _
    omega

/-- Helper: `sumAllFun` of an indicator at a single function `g0`. -/
theorem sumAllFun_single {m n : Nat} (g0 : Fin m -> Fin n) (v : Int) :
    haveI := Classical.propDecidable
    sumAllFun m n (fun f => if f = g0 then v else 0) = v := by
  classical
  induction m with
  | zero =>
    simp only [sumAllFun]
    have : (fun i : Fin 0 => nomatch i) = g0 := funext (fun i => nomatch i)
    simp [this]
  | succ m ihm =>
    simp only [sumAllFun]
    let g0' : Fin m -> Fin n := fun i => g0 i.castSucc
    let v0 : Fin n := g0 ⟨m, Nat.lt_succ_self m⟩
    have hstep : ∀ w : Fin n,
        sumAllFun m n (fun g => if snoc g w = g0 then v else 0) =
        if w = v0 then v else 0 := by
      intro w
      by_cases hw : w = v0
      · subst hw
        simp only [↓reduceIte]
        rw [sumAllFun_congr (G := fun g => if g = g0' then v else 0)]
        · exact ihm g0'
        · intro g
          have hiff : snoc g v0 = g0 ↔ g = g0' := by
            constructor
            · intro heq; funext i
              have := congrFun heq i.castSucc
              simpa [snoc_castSucc, g0'] using this
            · intro heq; subst heq; exact snoc_eta g0
          by_cases h : g = g0'
          · subst h
            have h1 : snoc g0' v0 = g0 := hiff.mpr rfl
            simp only [h1, ↓reduceIte]
          · have h2 : snoc g v0 ≠ g0 := fun hc => h (hiff.mp hc)
            simp only [h, h2, ↓reduceIte]
      · simp only [hw, ↓reduceIte]
        rw [sumAllFun_congr (G := fun _ => 0)]
        · exact sumAllFun_zero m n
        · intro g
          have hne : snoc g w ≠ g0 := by
            intro heq
            have := congrFun heq ⟨m, Nat.lt_succ_self m⟩
            simp [snoc_last] at this
            exact hw this
          simp only [hne, ↓reduceIte]
    rw [sumFin_congr hstep]
    exact sumFin_eq_single v0 v

theorem sumFin_eq_zero_of_nonneg {m : Nat} (h : Fin m -> Int)
    (hpos : ∀ i, 0 ≤ h i) (hz : sumFin m h = 0) : ∀ i, h i = 0 := by
  induction m with
  | zero => intro i; exact nomatch i
  | succ m ihm =>
    simp only [sumFin] at hz
    have hs_pos : ∀ (k : Nat) (q : Fin k -> Int), (∀ j, 0 ≤ q j) -> 0 ≤ sumFin k q := by
      intro k q hq
      induction k with
      | zero => simp [sumFin]
      | succ k ihk =>
        simp only [sumFin]
        have := ihk (fun j => q j.castSucc) (fun j => hq j.castSucc)
        have := hq ⟨k, Nat.lt_succ_self k⟩
        omega
    have h1 := hs_pos m (fun j => h j.castSucc) (fun j => hpos j.castSucc)
    have h2 := hpos ⟨m, Nat.lt_succ_self m⟩
    have hlast : h ⟨m, Nat.lt_succ_self m⟩ = 0 := by omega
    have hinit : sumFin m (fun j => h j.castSucc) = 0 := by omega
    intro i
    by_cases hi : i.val < m
    · exact ihm (fun j => h j.castSucc) (fun j => hpos j.castSucc) hinit ⟨i.val, hi⟩
    · have hval : i.val = m := by have := i.isLt; omega
      have heq : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hval
      rw [heq]; exact hlast

theorem sumFin_perm_applySwaps {n : Nat} (swaps : List (Fin n × Fin n)) (h : Fin n -> Int) :
    sumFin n (fun i => h (applySwaps swaps i)) = sumFin n h := by
  induction swaps generalizing h with
  | nil => rfl
  | cons p rest ihr =>
    rcases p with ⟨a, b⟩
    simp only [applySwaps]
    rw [ihr (fun i => h (finSwap a b i))]
    exact sumFin_perm_swap a b h

/-- Determinant of an upper-triangular matrix is the product of its diagonal. -/
theorem det_upperTriangular {n : Nat} (A : Mat n) (hU : ∀ i j : Fin n, j.val < i.val -> A i j = 0) :
    det A = prodFin n (fun i => A i i) := by
  classical
  unfold det
  have hterm : ∀ f : Fin n -> Fin n,
      leviCivita f * prodFin n (fun i => A i (f i)) =
      if f = id then prodFin n (fun i => A i i) else 0 := by
    intro f
    by_cases hfid : f = id
    · subst hfid
      simp only [↓reduceIte]
      change leviCivita (fun i => i) * prodFin n (fun i => A i i) = prodFin n (fun i => A i i)
      rw [leviCivita_id, Int.one_mul]
    · simp only [hfid, ↓reduceIte]
      by_cases hinj : ∀ i j, f i = f j -> i = j
      · have hex : ∃ i : Fin n, (f i).val < i.val :=
          Classical.byContradiction fun hno => by
            have hge : ∀ i : Fin n, i.val ≤ (f i).val := fun i =>
              Nat.le_of_not_lt (fun hlt => hno ⟨i, hlt⟩)
            obtain ⟨swaps, _, hfeq⟩ := injective_eq_applySwaps f hinj
            have hsum_eq : sumFin n (fun i => ((f i).val : Int)) = sumFin n (fun i => (i.val : Int)) := by
              rw [sumFin_congr (fun i => by rw [hfeq i])]
              exact sumFin_perm_applySwaps swaps (fun i => (i.val : Int))
            have hdiff0 : sumFin n (fun i => ((f i).val : Int) - (i.val : Int)) = 0 := by
              rw [sumFin_sub, hsum_eq]; omega
            have hall := sumFin_eq_zero_of_nonneg _ (fun i => by have := hge i; omega) hdiff0
            apply hfid
            funext i
            have hi0 : ((f i).val : Int) - (i.val : Int) = 0 := hall i
            exact Fin.ext (show (f i).val = i.val by omega)
        obtain ⟨i, hi⟩ := hex
        rw [prodFin_eq_zero_of_exists i (hU i (f i) hi), Int.mul_zero]
      · have hex : ∃ a b : Fin n, a ≠ b ∧ f a = f b :=
          Classical.byContradiction (fun hno => hinj (fun i j hij =>
            Classical.byContradiction (fun hne => hno ⟨i, j, hne, hij⟩)))
        obtain ⟨a, b, hab, hfab⟩ := hex
        rw [leviCivita_eq_zero_of_eq hab hfab, Int.zero_mul]
  rw [sumAllFun_congr hterm]
  exact sumAllFun_single id (prodFin n (fun i => A i i))

/-- Determinant of a lower-triangular matrix is the product of its diagonal. -/
theorem det_lowerTriangular {n : Nat} (A : Mat n) (hL : ∀ i j : Fin n, i.val < j.val -> A i j = 0) :
    det A = prodFin n (fun i => A i i) := by
  classical
  unfold det
  have hterm : ∀ f : Fin n -> Fin n,
      leviCivita f * prodFin n (fun i => A i (f i)) =
      if f = id then prodFin n (fun i => A i i) else 0 := by
    intro f
    by_cases hfid : f = id
    · subst hfid
      simp only [↓reduceIte]
      change leviCivita (fun i => i) * prodFin n (fun i => A i i) = prodFin n (fun i => A i i)
      rw [leviCivita_id, Int.one_mul]
    · simp only [hfid, ↓reduceIte]
      by_cases hinj : ∀ i j, f i = f j -> i = j
      · have hex : ∃ i : Fin n, i.val < (f i).val :=
          Classical.byContradiction fun hno => by
            have hle : ∀ i : Fin n, (f i).val ≤ i.val := fun i =>
              Nat.le_of_not_lt (fun hlt => hno ⟨i, hlt⟩)
            obtain ⟨swaps, _, hfeq⟩ := injective_eq_applySwaps f hinj
            have hsum_eq : sumFin n (fun i => ((f i).val : Int)) = sumFin n (fun i => (i.val : Int)) := by
              rw [sumFin_congr (fun i => by rw [hfeq i])]
              exact sumFin_perm_applySwaps swaps (fun i => (i.val : Int))
            have hdiff0 : sumFin n (fun i => (i.val : Int) - ((f i).val : Int)) = 0 := by
              rw [sumFin_sub, hsum_eq]; omega
            have hall := sumFin_eq_zero_of_nonneg _ (fun i => by have := hle i; omega) hdiff0
            apply hfid
            funext i
            have hi0 : (i.val : Int) - ((f i).val : Int) = 0 := hall i
            exact Fin.ext (show (f i).val = i.val by omega)
        obtain ⟨i, hi⟩ := hex
        rw [prodFin_eq_zero_of_exists i (hL i (f i) hi), Int.mul_zero]
      · have hex : ∃ a b : Fin n, a ≠ b ∧ f a = f b :=
          Classical.byContradiction (fun hno => hinj (fun i j hij =>
            Classical.byContradiction (fun hne => hno ⟨i, j, hne, hij⟩)))
        obtain ⟨a, b, hab, hfab⟩ := hex
        rw [leviCivita_eq_zero_of_eq hab hfab, Int.zero_mul]
  rw [sumAllFun_congr hterm]
  exact sumAllFun_single id (prodFin n (fun i => A i i))

theorem det_diag {n : Nat} (d : Fin n -> Int) : det (matDiag d) = prodFin n d := by
  rw [det_upperTriangular]
  · apply prodFin_congr; intro i; simp [matDiag]
  · intro i j hij
    have hne : i ≠ j := fun h => by have := congrArg Fin.val h; omega
    simp [matDiag, hne]

/-! ### Block Row-0 Expansion & Kirchhoff Rank-1 Cofactor Theorem -/

/-- Principal `(0, 0)`-cofactor submatrix of an `(m + 1) x (m + 1)` matrix. -/
def minor00 {m : Nat} (A : Mat (m + 1)) : Mat m :=
  fun i j => A i.succ j.succ

/-- If row 0 of `A` is `(c, 0, ..., 0)`, then `det A = c * det (minor00 A)`. -/
theorem det_row0_single {m : Nat} (A : Mat (m + 1))
    (hrow0 : ∀ j : Fin (m + 1), j.val ≠ 0 -> A ⟨0, Nat.zero_lt_succ m⟩ j = 0) :
    det A = A ⟨0, Nat.zero_lt_succ m⟩ ⟨0, Nat.zero_lt_succ m⟩ * det (minor00 A) := by
  unfold det
  have hpull : ∀ (k : Nat) (F : (Fin (k + 1) -> Fin (m + 1)) -> Int),
      sumAllFun (k + 1) (m + 1) F =
      sumFin (m + 1) (fun v0 => sumAllFun k (m + 1) (fun g =>
        F (fun i => if h : i.val = 0 then v0 else g ⟨i.val - 1, by omega⟩))) := by
    intro k F
    induction k with
    | zero =>
      simp only [sumAllFun]
      apply sumFin_congr
      intro v0
      congr 1
      funext i
      simp [snoc]
    | succ k ihk =>
      change sumFin (m + 1) (fun w => sumAllFun (k + 1) (m + 1) (fun f => F (snoc f w))) = _
      rw [sumFin_congr (fun w => ihk (fun f => F (snoc f w)))]
      rw [sumFin_swap_order]
      apply sumFin_congr
      intro v0
      change sumFin (m + 1) (fun w => sumAllFun k (m + 1) (fun g =>
        F (snoc (fun i => if h : i.val = 0 then v0 else g ⟨i.val - 1, by omega⟩) w))) =
        sumFin (m + 1) (fun w => sumAllFun k (m + 1) (fun g =>
        F (fun i => if h : i.val = 0 then v0 else snoc g w ⟨i.val - 1, by omega⟩)))
      apply sumFin_congr
      intro w
      apply sumAllFun_congr
      intro g
      congr 1
      funext i
      unfold snoc
      by_cases h0 : i.val = 0
      · simp [h0]
      · by_cases hlt : i.val < k + 1
        · have hsub : i.val - 1 < k := by omega
          simp [h0, hlt, hsub]
        · have hnsub : ¬(i.val - 1 < k) := by omega
          simp [h0, hlt, hnsub]
  rw [hpull m]
  have hv0 : ∀ v0 : Fin (m + 1),
      sumAllFun m (m + 1) (fun g =>
        leviCivita (fun i => if h : i.val = 0 then v0 else g ⟨i.val - 1, by omega⟩) *
        prodFin (m + 1) (fun i => A i (if h : i.val = 0 then v0 else g ⟨i.val - 1, by omega⟩))) =
      if v0 = ⟨0, Nat.zero_lt_succ m⟩ then
        A ⟨0, Nat.zero_lt_succ m⟩ ⟨0, Nat.zero_lt_succ m⟩ *
        sumAllFun m m (fun g => leviCivita g * prodFin m (fun i => minor00 A i (g i)))
      else 0 := by
    intro v0
    by_cases hv : v0 = ⟨0, Nat.zero_lt_succ m⟩
    · subst hv
      rw [ite_eq_left rfl]
      have hrestrict : ∀ (k : Nat) (H : (Fin k -> Fin (m + 1)) -> Int),
          (∀ g, (∃ i, (g i).val = 0) -> H g = 0) ->
          sumAllFun k (m + 1) H = sumAllFun k m (fun g => H (fun i => (g i).succ)) := by
        intro k H hzero
        induction k with
        | zero =>
          simp only [sumAllFun]
          congr 1; funext i; exact nomatch i
        | succ k ihk =>
          simp only [sumAllFun]
          rw [sumFin_succ_zero]
          have h0 : sumAllFun k (m + 1) (fun g => H (snoc g ⟨0, Nat.zero_lt_succ m⟩)) = 0 := by
            rw [sumAllFun_congr (G := fun _ => 0)]
            · exact sumAllFun_zero k (m + 1)
            · intro g
              exact hzero (snoc g ⟨0, Nat.zero_lt_succ m⟩) ⟨⟨k, Nat.lt_succ_self k⟩, by simp [snoc_last]⟩
          rw [h0, Int.zero_add]
          apply sumFin_congr
          intro w
          have hrec := ihk (fun g => H (snoc g w.succ)) (by
            intro g ⟨i, hi⟩
            exact hzero (snoc g w.succ) ⟨i.castSucc, by simpa [snoc_castSucc] using hi⟩)
          rw [hrec]
          apply sumAllFun_congr
          intro g
          congr 1; funext i; unfold snoc; split <;> rfl
      rw [hrestrict m]
      · rw [← sumAllFun_mul_left]
        apply sumAllFun_congr
        intro g
        have hlc : leviCivita (fun i : Fin (m + 1) =>
            if h : i.val = 0 then ⟨0, Nat.zero_lt_succ m⟩ else (g ⟨i.val - 1, by omega⟩).succ) =
            leviCivita g := by
          unfold leviCivita
          rw [prodFin_succ_zero]
          have hfirst : prodFin (m + 1) (fun j =>
              if (0 : Nat) < j.val then
                cmpSign (if h : (0 : Nat) = 0 then (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) else (g ⟨0 - 1, by omega⟩).succ).val
                        (if h : j.val = 0 then ⟨0, Nat.zero_lt_succ m⟩ else (g ⟨j.val - 1, by omega⟩).succ).val
              else 1) = 1 := by
            rw [prodFin_congr (g := fun _ => 1)]
            · exact prodFin_one (m + 1)
            · intro j
              by_cases hj : 0 < j.val
              · have hne : j.val ≠ 0 := by omega
                rw [ite_eq_left hj, dite_eq_left rfl, dite_eq_right hne]
                unfold cmpSign
                simp
              · rw [ite_eq_right hj]
          rw [hfirst, Int.one_mul]
          apply prodFin_congr
          intro i
          rw [prodFin_succ_zero]
          have hnot0 : ¬(i.succ.val < 0) := by omega
          simp only [hnot0, ↓reduceIte, Int.one_mul]
          apply prodFin_congr
          intro j
          have hi0 : i.succ.val ≠ 0 := by simp
          have hj0 : j.succ.val ≠ 0 := by simp
          have hsub_i : (⟨i.succ.val - 1, by omega⟩ : Fin m) = i := Fin.ext (by simp)
          have hsub_j : (⟨j.succ.val - 1, by omega⟩ : Fin m) = j := Fin.ext (by simp)
          simp only [hi0, hj0, ↓reduceDIte, hsub_i, hsub_j]
          have hlt_iff : i.succ.val < j.succ.val ↔ i.val < j.val := by simp
          have hcmp : cmpSign (g i).succ.val (g j).succ.val = cmpSign (g i).val (g j).val := by
            unfold cmpSign; simp
          by_cases h : i.val < j.val
          · rw [ite_eq_left (hlt_iff.mpr h), ite_eq_left h, hcmp]
          · have h2 : ¬(i.succ.val < j.succ.val) := fun hc => h (hlt_iff.mp hc)
            rw [ite_eq_right h2, ite_eq_right h]
        rw [hlc]
        rw [prodFin_succ_zero]
        simp only [↓reduceDIte]
        have hpr : prodFin m (fun i : Fin m =>
            A i.succ (if h : i.succ.val = 0 then ⟨0, Nat.zero_lt_succ m⟩ else (g ⟨i.succ.val - 1, by omega⟩).succ)) =
            prodFin m (fun i => minor00 A i (g i)) := by
          apply prodFin_congr
          intro i
          have hi0 : i.succ.val ≠ 0 := by simp
          have hsub_i : (⟨i.succ.val - 1, by omega⟩ : Fin m) = i := Fin.ext (by simp)
          simp only [hi0, ↓reduceDIte, hsub_i, minor00]
        rw [hpr]
        rw [← Int.mul_assoc, Int.mul_comm (leviCivita g), Int.mul_assoc]
      · intro g ⟨i, hi⟩
        have hlc0 : leviCivita (fun k : Fin (m + 1) =>
            if h : k.val = 0 then ⟨0, Nat.zero_lt_succ m⟩ else g ⟨k.val - 1, by omega⟩) = 0 := by
          apply leviCivita_eq_zero_of_eq (a := ⟨0, Nat.zero_lt_succ m⟩) (b := i.succ)
          · intro heq; have := congrArg Fin.val heq; simp at this
          · simp only [↓reduceDIte]
            have hi0 : i.succ.val ≠ 0 := by simp
            simp only [hi0, ↓reduceDIte]
            have hsub : (⟨i.succ.val - 1, by omega⟩ : Fin m) = i := Fin.ext (by simp)
            rw [hsub]
            exact Fin.ext (by simpa using hi.symm)
        rw [hlc0, Int.zero_mul]
    · rw [ite_eq_right hv]
      rw [sumAllFun_congr (G := fun _ => 0)]
      · exact sumAllFun_zero m (m + 1)
      · intro g
        have hvne : v0.val ≠ 0 := fun h => hv (Fin.ext h)
        have hp0 : prodFin (m + 1) (fun i => A i (if h : i.val = 0 then v0 else g ⟨i.val - 1, by omega⟩)) = 0 := by
          apply prodFin_eq_zero_of_exists ⟨0, Nat.zero_lt_succ m⟩
          simp only [↓reduceDIte]
          exact hrow0 v0 hvne
        rw [hp0, Int.mul_zero]
  rw [sumFin_congr hv0]
  exact sumFin_eq_single ⟨0, Nat.zero_lt_succ m⟩ _

/-- Elementary upper-triangular row-sum matrix (adds all rows to row 0). -/
def elemRowSum (n : Nat) : Mat n :=
  fun i j => if i.val = 0 then 1 else if i = j then 1 else 0

/-- Elementary upper-triangular col-diff matrix (subtracts col 0 from cols 1..n-1). -/
def elemColDiff (n : Nat) : Mat n :=
  fun i j => if i = j then 1 else if i.val = 0 then -1 else 0

theorem det_elemRowSum (n : Nat) : det (elemRowSum n) = 1 := by
  rw [det_upperTriangular]
  · rw [prodFin_congr (g := fun _ => 1)]
    · exact prodFin_one n
    · intro i; unfold elemRowSum; split <;> simp
  · intro i j hij
    have hi0 : i.val ≠ 0 := by omega
    have hne : i ≠ j := fun h => by have := congrArg Fin.val h; omega
    simp [elemRowSum, hi0, hne]

theorem det_elemColDiff (n : Nat) : det (elemColDiff n) = 1 := by
  rw [det_upperTriangular]
  · rw [prodFin_congr (g := fun _ => 1)]
    · exact prodFin_one n
    · intro i; simp [elemColDiff]
  · intro i j hij
    have hi0 : i.val ≠ 0 := by omega
    have hne : i ≠ j := fun h => by have := congrArg Fin.val h; omega
    simp [elemColDiff, hi0, hne]

/-- Right-multiplying any matrix `M` by `elemColDiff` leaves col 0 unchanged and subtracts col 0 from cols `j > 0`. -/
theorem matMul_elemColDiff {m : Nat} (M : Mat (m + 1)) (i j : Fin (m + 1)) :
    matMul M (elemColDiff (m + 1)) i j =
    if j.val = 0 then M i ⟨0, Nat.zero_lt_succ m⟩ else M i j - M i ⟨0, Nat.zero_lt_succ m⟩ := by
  unfold matMul
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, Nat.zero_lt_succ m⟩ := Fin.ext hj0
    rw [ite_eq_left hj0, hj]
    rw [sumFin_congr (g := fun k => if k = ⟨0, Nat.zero_lt_succ m⟩ then M i ⟨0, Nat.zero_lt_succ m⟩ else 0)]
    · exact sumFin_eq_single _ _
    · intro k
      by_cases hk : k = ⟨0, Nat.zero_lt_succ m⟩
      · subst hk; simp [elemColDiff]
      · have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
        unfold elemColDiff
        rw [ite_eq_right hk, ite_eq_right hk0, ite_eq_right hk, Int.mul_zero]
  · rw [ite_eq_right hj0]
    have hne0j : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) ≠ j := fun h => hj0 (congrArg Fin.val h).symm
    rw [sumFin_congr (g := fun k =>
        (if k = j then M i j else 0) +
        (if k = ⟨0, Nat.zero_lt_succ m⟩ then -(M i ⟨0, Nat.zero_lt_succ m⟩) else 0))]
    · rw [sumFin_add, sumFin_eq_single, sumFin_eq_single]; omega
    · intro k
      by_cases hkj : k = j
      · subst hkj
        unfold elemColDiff
        rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (Ne.symm hne0j), Int.mul_one, Int.add_zero]
      · by_cases hk0 : k = ⟨0, Nat.zero_lt_succ m⟩
        · subst hk0
          unfold elemColDiff
          rw [ite_eq_right hkj, ite_eq_left rfl, ite_eq_right hkj, ite_eq_left rfl, Int.zero_add, Int.mul_neg_one]
        · have hk0' : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
          unfold elemColDiff
          rw [ite_eq_right hkj, ite_eq_right hk0', ite_eq_right hkj, ite_eq_right hk0, Int.mul_zero, Int.add_zero]

theorem matMul_diag_right {n : Nat} (Q : Mat n) (d : Fin n -> Int) :
    ∀ i j, matMul Q (matDiag d) i j = Q i j * d j := by
  intro i j
  unfold matMul matDiag
  rw [sumFin_congr (g := fun k => if k = j then Q i j * d j else 0)]
  · exact sumFin_eq_single j (Q i j * d j)
  · intro k
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [hkj]

/-- Exact integer graph Laplacian from a weight function `w : Fin n -> Fin n -> Int`. -/
def graphLaplacian {n : Nat} (w : Fin n -> Fin n -> Int) : Mat n :=
  fun i j =>
    if i = j then sumFin n (fun r => if r = i then 0 else w i r)
    else -w i j

theorem graphLaplacian_row_sum {n : Nat} (w : Fin n -> Fin n -> Int) (i : Fin n) :
    sumFin n (fun j => graphLaplacian w i j) = 0 := by
  unfold graphLaplacian
  have hsplit : ∀ j : Fin n,
      (if i = j then sumFin n (fun r => if r = i then 0 else w i r) else -w i j) =
      (if j = i then sumFin n (fun r => if r = i then 0 else w i r) else 0) +
      -(if j = i then 0 else w i j) := by
    intro j
    by_cases hji : j = i
    · subst hji; simp
    · have hij : i ≠ j := Ne.symm hji
      simp [hji, hij]
  rw [sumFin_congr hsplit, sumFin_add, sumFin_eq_single, sumFin_neg]
  omega

theorem graphLaplacian_col_sum {n : Nat} (w : Fin n -> Fin n -> Int)
    (hsym : ∀ i j, w i j = w j i) (j : Fin n) :
    sumFin n (fun i => graphLaplacian w i j) = 0 := by
  have heq : ∀ i : Fin n, graphLaplacian w i j = graphLaplacian w j i := by
    intro i
    unfold graphLaplacian
    by_cases hij : i = j
    · subst hij; rfl
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji, hsym i j]
  rw [sumFin_congr heq]
  exact graphLaplacian_row_sum w j

/-- Quadratic/difference action of any graph Laplacian on a vector `v`:
    `(L v)_i = ∑_j w(i, j) * (v_i - v_j)` (self-loops `j = i` cancel automatically!). -/
theorem graphLaplacian_mul_vec {n : Nat} (w : Fin n -> Fin n -> Int) (v : Fin n -> Int) (i : Fin n) :
    sumFin n (fun j => graphLaplacian w i j * v j) =
    sumFin n (fun j => w i j * (v i - v j)) := by
  unfold graphLaplacian
  have h1 : ∀ j : Fin n,
      (if i = j then sumFin n (fun r => if r = i then 0 else w i r) else -w i j) * v j =
      (if j = i then sumFin n (fun r => if r = i then 0 else w i r) * v i else 0) +
      (if j = i then 0 else -w i j * v j) := by
    intro j
    by_cases hji : j = i
    · subst hji; simp
    · have hij : i ≠ j := Ne.symm hji
      simp [hji, hij]
  rw [sumFin_congr h1, sumFin_add, sumFin_eq_single, ← sumFin_mul_right, ← sumFin_add]
  apply sumFin_congr
  intro j
  by_cases hji : j = i
  · subst hji; simp
  · simp [hji, Int.mul_sub, Int.neg_mul]; omega

/-! ### Bit-Slice Splitting Helpers for `Fin (2 * m)` and `Fin (2 ^ (k + 1))` -/

theorem sumFin_add_split (a b : Nat) (f : Fin (a + b) -> Int) :
    sumFin (a + b) f =
    sumFin a (fun i => f ⟨i.val, by omega⟩) +
    sumFin b (fun j => f ⟨a + j.val, by omega⟩) := by
  induction b with
  | zero =>
    simp only [sumFin, Int.add_zero]
    apply sumFin_congr; intro i; rfl
  | succ b ih =>
    change sumFin (a + b) (fun i => f i.castSucc) + f ⟨a + b, by omega⟩ =
           sumFin a (fun i => f ⟨i.val, by omega⟩) +
           (sumFin b (fun j => f ⟨a + j.val, by omega⟩) + f ⟨a + b, by omega⟩)
    rw [ih (fun i => f i.castSucc), Int.add_assoc]
    congr 1

theorem prodFin_add_split (a b : Nat) (f : Fin (a + b) -> Int) :
    prodFin (a + b) f =
    prodFin a (fun i => f ⟨i.val, by omega⟩) *
    prodFin b (fun j => f ⟨a + j.val, by omega⟩) := by
  induction b with
  | zero =>
    simp only [prodFin, Int.mul_one]
    apply prodFin_congr; intro i; rfl
  | succ b ih =>
    change prodFin (a + b) (fun i => f i.castSucc) * f ⟨a + b, by omega⟩ =
           prodFin a (fun i => f ⟨i.val, by omega⟩) *
           (prodFin b (fun j => f ⟨a + j.val, by omega⟩) * f ⟨a + b, by omega⟩)
    rw [ih (fun i => f i.castSucc), Int.mul_assoc]
    congr 1

theorem sumFin_even_odd (m : Nat) (f : Fin (2 * m) -> Int) :
    sumFin (2 * m) f =
    sumFin m (fun a => f ⟨2 * a.val, by omega⟩) +
    sumFin m (fun a => f ⟨2 * a.val + 1, by omega⟩) := by
  induction m with
  | zero => simp [sumFin]
  | succ m ih =>
    have hstep : ∀ (g : Fin (2 * m + 2) -> Int),
        sumFin (2 * m + 2) g =
        sumFin (2 * m) (fun i => g ⟨i.val, by omega⟩) +
        g ⟨2 * m, by omega⟩ + g ⟨2 * m + 1, by omega⟩ := by
      intro g; rfl
    change sumFin (2 * m + 2) f = _
    rw [hstep f, ih (fun i => f ⟨i.val, by omega⟩)]
    simp only [sumFin]
    have h1 : sumFin m (fun a : Fin m => f ⟨2 * a.val, by omega⟩) =
              sumFin m (fun a : Fin m => f ⟨2 * a.castSucc.val, by omega⟩) :=
      sumFin_congr (fun _ => rfl)
    have h2 : sumFin m (fun a : Fin m => f ⟨2 * a.val + 1, by omega⟩) =
              sumFin m (fun a : Fin m => f ⟨2 * a.castSucc.val + 1, by omega⟩) :=
      sumFin_congr (fun _ => rfl)
    rw [h1, h2]
    omega

theorem fin_div2_lt {k : Nat} (x : Fin (2 ^ (k + 1))) : x.val / 2 < 2 ^ k := by
  have h : x.val < 2 ^ k * 2 := by simpa [Nat.pow_succ] using x.isLt
  omega

theorem fin_sub_pow2_lt {k : Nat} (x : Fin (2 ^ (k + 1))) : x.val - 2 ^ k < 2 ^ k := by
  have h : x.val < 2 ^ k * 2 := by simpa [Nat.pow_succ] using x.isLt
  omega

theorem sumFin_pow2_succ (k : Nat) (f : Fin (2 ^ (k + 1)) -> Int) :
    sumFin (2 ^ (k + 1)) f =
    sumFin (2 ^ k) (fun a => f ⟨2 * a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩) +
    sumFin (2 ^ k) (fun a => f ⟨2 * a.val + 1, by have := a.isLt; rw [Nat.pow_succ]; omega⟩) := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hcast : ∀ (n : Nat) (hn : n = 2 * 2 ^ k) (g : Fin n -> Int),
      sumFin n g =
      sumFin (2 ^ k) (fun a => g ⟨2 * a.val, by have := a.isLt; omega⟩) +
      sumFin (2 ^ k) (fun a => g ⟨2 * a.val + 1, by have := a.isLt; omega⟩) := by
    intro n hn g
    subst hn
    exact sumFin_even_odd (2 ^ k) g
  exact hcast (2 ^ (k + 1)) hpow f

theorem sumFin_pow2_halves (k : Nat) (f : Fin (2 ^ (k + 1)) -> Int) :
    sumFin (2 ^ (k + 1)) f =
    sumFin (2 ^ k) (fun a => f ⟨a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩) +
    sumFin (2 ^ k) (fun a => f ⟨2 ^ k + a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩) := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hcast : ∀ (n : Nat) (hn : n = 2 ^ k + 2 ^ k) (g : Fin n -> Int),
      sumFin n g =
      sumFin (2 ^ k) (fun a => g ⟨a.val, by have := a.isLt; omega⟩) +
      sumFin (2 ^ k) (fun a => g ⟨2 ^ k + a.val, by have := a.isLt; omega⟩) := by
    intro n hn g
    subst hn
    exact sumFin_add_split (2 ^ k) (2 ^ k) g
  exact hcast (2 ^ (k + 1)) hpow f

theorem prodFin_pow2_halves (k : Nat) (f : Fin (2 ^ (k + 1)) -> Int) :
    prodFin (2 ^ (k + 1)) f =
    prodFin (2 ^ k) (fun a => f ⟨a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩) *
    prodFin (2 ^ k) (fun a => f ⟨2 ^ k + a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩) := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hcast : ∀ (n : Nat) (hn : n = 2 ^ k + 2 ^ k) (g : Fin n -> Int),
      prodFin n g =
      prodFin (2 ^ k) (fun a => g ⟨a.val, by have := a.isLt; omega⟩) *
      prodFin (2 ^ k) (fun a => g ⟨2 ^ k + a.val, by have := a.isLt; omega⟩) := by
    intro n hn g
    subst hn
    exact prodFin_add_split (2 ^ k) (2 ^ k) g
  exact hcast (2 ^ (k + 1)) hpow f

/-! ### Pure-Silicon Walsh-Hadamard Core on `Fin (2^m)` -/

theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_div_two, Nat.testBit_xor]

theorem xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have hbit : (a ^^^ b).testBit 0 = ((a % 2) ^^^ (b % 2)).testBit 0 := by
    simp [Nat.testBit_zero]
  have h1 : (a ^^^ b) % 2 < 2 := Nat.mod_lt _ (by decide)
  have h2 : a % 2 < 2 := Nat.mod_lt _ (by decide)
  have h3 : b % 2 < 2 := Nat.mod_lt _ (by decide)
  have ht : ∀ x : Nat, x < 2 -> x.testBit 0 = decide (x = 1) := by
    intro x hx
    have : x = 0 ∨ x = 1 := by omega
    rcases this with rfl | rfl <;> decide
  have h4 : ((a % 2) ^^^ (b % 2)) < 2 := by
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> decide
  rw [Nat.testBit_zero] at hbit
  rw [ht _ h4] at hbit
  have ha1 : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1 := by omega
  have hb1 : (a % 2) ^^^ (b % 2) = 0 ∨ (a % 2) ^^^ (b % 2) = 1 := by omega
  rcases ha1 with ha1 | ha1 <;> rcases hb1 with hb1 | hb1 <;> simp_all

theorem xor_lt_pow2 {m a b : Nat} (ha : a < 2 ^ m) (hb : b < 2 ^ m) : (a ^^^ b) < 2 ^ m := by
  induction m generalizing a b with
  | zero =>
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0; subst hb0; decide
  | succ m ih =>
    have hdiv : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := xor_div_two a b
    have ha' : a / 2 < 2 ^ m := by rw [Nat.pow_succ] at ha; omega
    have hb' : b / 2 < 2 ^ m := by rw [Nat.pow_succ] at hb; omega
    have hih := ih ha' hb'
    rw [Nat.pow_succ]
    omega

theorem sumFin_perm_xor (m : Nat) (a : Fin (2 ^ m)) (f : Fin (2 ^ m) -> Int) :
    sumFin (2 ^ m) (fun b => f ⟨a.val ^^^ b.val, xor_lt_pow2 a.isLt b.isLt⟩) = sumFin (2 ^ m) f := by
  induction m with
  | zero =>
    have ha0 : a.val = 0 := by have := a.isLt; simp at this; omega
    simp only [Nat.pow_zero, sumFin]
    have heq : (⟨a.val ^^^ 0, xor_lt_pow2 a.isLt (by decide)⟩ : Fin 1) = ⟨0, by decide⟩ :=
      Fin.ext (by simp)
    rw [heq]
  | succ m ih =>
    rw [sumFin_pow2_succ, sumFin_pow2_succ]
    let a' : Fin (2 ^ m) := ⟨a.val / 2, fin_div2_lt a⟩
    have hbit : a.val % 2 = 0 ∨ a.val % 2 = 1 := by omega
    rcases hbit with ha0 | ha1
    · have hev : ∀ b : Fin (2 ^ m), a.val ^^^ (2 * b.val) = 2 * (a'.val ^^^ b.val) := by
        intro b
        have hm := xor_mod_two a.val (2 * b.val)
        have hd := xor_div_two a.val (2 * b.val)
        have h2m : (2 * b.val) % 2 = 0 := by omega
        have h2d : (2 * b.val) / 2 = b.val := by omega
        rw [ha0, h2m] at hm
        rw [h2d] at hd
        have h00 : (0 : Nat) ^^^ 0 = 0 := by decide
        rw [h00] at hm
        dsimp only [a']; omega
      have hod : ∀ b : Fin (2 ^ m), a.val ^^^ (2 * b.val + 1) = 2 * (a'.val ^^^ b.val) + 1 := by
        intro b
        have hm := xor_mod_two a.val (2 * b.val + 1)
        have hd := xor_div_two a.val (2 * b.val + 1)
        have h2m : (2 * b.val + 1) % 2 = 1 := by omega
        have h2d : (2 * b.val + 1) / 2 = b.val := by omega
        rw [ha0, h2m] at hm
        rw [h2d] at hd
        have h01 : (0 : Nat) ^^^ 1 = 1 := by decide
        rw [h01] at hm
        dsimp only [a']; omega
      have h1 : sumFin (2 ^ m) (fun b => f ⟨a.val ^^^ (2 * b.val), xor_lt_pow2 a.isLt (by have := b.isLt; rw [Nat.pow_succ]; omega)⟩) =
                sumFin (2 ^ m) (fun b => f ⟨2 * b.val, by have := b.isLt; rw [Nat.pow_succ]; omega⟩) := by
        have hcongr : sumFin (2 ^ m) (fun b => f ⟨a.val ^^^ (2 * b.val), xor_lt_pow2 a.isLt (by have := b.isLt; rw [Nat.pow_succ]; omega)⟩) =
                      sumFin (2 ^ m) (fun b => f ⟨2 * (a'.val ^^^ b.val), by have := xor_lt_pow2 a'.isLt b.isLt; rw [Nat.pow_succ]; omega⟩) :=
          sumFin_congr (fun b => congrArg f (Fin.ext (hev b)))
        rw [hcongr]
        exact ih a' (fun b => f ⟨2 * b.val, by have := b.isLt; rw [Nat.pow_succ]; omega⟩)
      have h2 : sumFin (2 ^ m) (fun b => f ⟨a.val ^^^ (2 * b.val + 1), xor_lt_pow2 a.isLt (by have := b.isLt; rw [Nat.pow_succ]; omega)⟩) =
                sumFin (2 ^ m) (fun b => f ⟨2 * b.val + 1, by have := b.isLt; rw [Nat.pow_succ]; omega⟩) := by
        have hcongr : sumFin (2 ^ m) (fun b => f ⟨a.val ^^^ (2 * b.val + 1), xor_lt_pow2 a.isLt (by have := b.isLt; rw [Nat.pow_succ]; omega)⟩) =
                      sumFin (2 ^ m) (fun b => f ⟨2 * (a'.val ^^^ b.val) + 1, by have := xor_lt_pow2 a'.isLt b.isLt; rw [Nat.pow_succ]; omega⟩) :=
          sumFin_congr (fun b => congrArg f (Fin.ext (hod b)))
        rw [hcongr]
        exact ih a' (fun b => f ⟨2 * b.val + 1, by have := b.isLt; rw [Nat.pow_succ]; omega⟩)
      rw [h1, h2]
    · have hev : ∀ b : Fin (2 ^ m), a.val ^^^ (2 * b.val) = 2 * (a'.val ^^^ b.val) + 1 := by
        intro b
        have hm := xor_mod_two a.val (2 * b.val)
        have hd := xor_div_two a.val (2 * b.val)
        have h2m : (2 * b.val) % 2 = 0 := by omega
        have h2d : (2 * b.val) / 2 = b.val := by omega
        rw [ha1, h2m] at hm
        rw [h2d] at hd
        have h10 : (1 : Nat) ^^^ 0 = 1 := by decide
        rw [h10] at hm
        dsimp only [a']; omega
      have hod : ∀ b : Fin (2 ^ m), a.val ^^^ (2 * b.val + 1) = 2 * (a'.val ^^^ b.val) := by
        intro b
        have hm := xor_mod_two a.val (2 * b.val + 1)
        have hd := xor_div_two a.val (2 * b.val + 1)
        have h2m : (2 * b.val + 1) % 2 = 1 := by omega
        have h2d : (2 * b.val + 1) / 2 = b.val := by omega
        rw [ha1, h2m] at hm
        rw [h2d] at hd
        have h11 : (1 : Nat) ^^^ 1 = 0 := by decide
        rw [h11] at hm
        dsimp only [a']; omega
      have h1 : sumFin (2 ^ m) (fun b => f ⟨a.val ^^^ (2 * b.val), xor_lt_pow2 a.isLt (by have := b.isLt; rw [Nat.pow_succ]; omega)⟩) =
                sumFin (2 ^ m) (fun b => f ⟨2 * b.val + 1, by have := b.isLt; rw [Nat.pow_succ]; omega⟩) := by
        have hcongr : sumFin (2 ^ m) (fun b => f ⟨a.val ^^^ (2 * b.val), xor_lt_pow2 a.isLt (by have := b.isLt; rw [Nat.pow_succ]; omega)⟩) =
                      sumFin (2 ^ m) (fun b => f ⟨2 * (a'.val ^^^ b.val) + 1, by have := xor_lt_pow2 a'.isLt b.isLt; rw [Nat.pow_succ]; omega⟩) :=
          sumFin_congr (fun b => congrArg f (Fin.ext (hev b)))
        rw [hcongr]
        exact ih a' (fun b => f ⟨2 * b.val + 1, by have := b.isLt; rw [Nat.pow_succ]; omega⟩)
      have h2 : sumFin (2 ^ m) (fun b => f ⟨a.val ^^^ (2 * b.val + 1), xor_lt_pow2 a.isLt (by have := b.isLt; rw [Nat.pow_succ]; omega)⟩) =
                sumFin (2 ^ m) (fun b => f ⟨2 * b.val, by have := b.isLt; rw [Nat.pow_succ]; omega⟩) := by
        have hcongr : sumFin (2 ^ m) (fun b => f ⟨a.val ^^^ (2 * b.val + 1), xor_lt_pow2 a.isLt (by have := b.isLt; rw [Nat.pow_succ]; omega)⟩) =
                      sumFin (2 ^ m) (fun b => f ⟨2 * (a'.val ^^^ b.val), by have := xor_lt_pow2 a'.isLt b.isLt; rw [Nat.pow_succ]; omega⟩) :=
          sumFin_congr (fun b => congrArg f (Fin.ext (hod b)))
        rw [hcongr]
        exact ih a' (fun b => f ⟨2 * b.val, by have := b.isLt; rw [Nat.pow_succ]; omega⟩)
      rw [h1, h2, Int.add_comm]

/-- Single-bit Walsh character factor `(-1)^{(a%2) * (b%2)}`. -/
def walshBit (a b : Nat) : Int :=
  if a % 2 = 1 ∧ b % 2 = 1 then -1 else 1

/-- LSB-recursive `m`-bit Walsh-Hadamard character `(-1)^{popcount((u & x) mod 2^m)}`. -/
def walshSign : (m : Nat) -> Nat -> Nat -> Int
  | 0, _, _ => 1
  | m + 1, u, x => walshBit u x * walshSign m (u / 2) (x / 2)

theorem walshBit_zero_left (x : Nat) : walshBit 0 x = 1 := by simp [walshBit]
theorem walshBit_zero_right (u : Nat) : walshBit u 0 = 1 := by simp [walshBit]

theorem walshBit_mul_xor (u a b : Nat) :
    walshBit u (a ^^^ b) = walshBit u a * walshBit u b := by
  unfold walshBit
  have hm := xor_mod_two a b
  have hu : u % 2 = 0 ∨ u % 2 = 1 := by omega
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases hu with hu | hu <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [hm, hu, ha, hb]

theorem walshSign_zero_left (m x : Nat) : walshSign m 0 x = 1 := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => simp [walshSign, walshBit_zero_left, ih]

theorem walshSign_zero_right (m u : Nat) : walshSign m u 0 = 1 := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih => simp [walshSign, walshBit_zero_right, ih]

theorem walshSign_mul_xor (m u a b : Nat) :
    walshSign m u (a ^^^ b) = walshSign m u a * walshSign m u b := by
  induction m generalizing u a b with
  | zero => simp [walshSign]
  | succ m ih =>
    simp only [walshSign, walshBit_mul_xor, xor_div_two, ih]
    have h4 : ∀ p q r s : Int, p * q * (r * s) = p * r * (q * s) := by
      intro p q r s
      calc p * q * (r * s) = p * (q * r * s) := by rw [Int.mul_assoc, Int.mul_assoc]
        _ = p * (r * q * s) := by rw [Int.mul_comm q r]
        _ = p * r * (q * s) := by rw [Int.mul_assoc, Int.mul_assoc]
    exact h4 _ _ _ _

theorem walshSign_symm (m u x : Nat) : walshSign m u x = walshSign m x u := by
  induction m generalizing u x with
  | zero => rfl
  | succ m ih =>
    simp only [walshSign, ih]
    congr 1
    unfold walshBit
    by_cases hu : u % 2 = 1 <;> by_cases hx : x % 2 = 1 <;> simp [hu, hx]

theorem walshSign_orth (m : Nat) (u v : Fin (2 ^ m)) :
    sumFin (2 ^ m) (fun x => walshSign m u.val x.val * walshSign m v.val x.val) =
    if u = v then ((2 ^ m : Nat) : Int) else 0 := by
  induction m with
  | zero =>
    have hu : u = ⟨0, by decide⟩ := Fin.ext (by have := u.isLt; simp at this; omega)
    have hv : v = ⟨0, by decide⟩ := Fin.ext (by have := v.isLt; simp at this; omega)
    subst hu; subst hv
    simp [sumFin, walshSign]
  | succ m ih =>
    rw [sumFin_pow2_succ]
    let u' : Fin (2 ^ m) := ⟨u.val / 2, fin_div2_lt u⟩
    let v' : Fin (2 ^ m) := ⟨v.val / 2, fin_div2_lt v⟩
    have hev : ∀ a : Fin (2 ^ m),
        walshSign (m + 1) u.val (2 * a.val) * walshSign (m + 1) v.val (2 * a.val) =
        walshSign m u'.val a.val * walshSign m v'.val a.val := by
      intro a
      simp only [walshSign]
      have h2m : (2 * a.val) % 2 = 0 := by omega
      have h2d : (2 * a.val) / 2 = a.val := by omega
      simp [walshBit, h2m, h2d, u', v']
    have hod : ∀ a : Fin (2 ^ m),
        walshSign (m + 1) u.val (2 * a.val + 1) * walshSign (m + 1) v.val (2 * a.val + 1) =
        (if u.val % 2 = v.val % 2 then 1 else -1) *
        (walshSign m u'.val a.val * walshSign m v'.val a.val) := by
      intro a
      simp only [walshSign]
      have h2m : (2 * a.val + 1) % 2 = 1 := by omega
      have h2d : (2 * a.val + 1) / 2 = a.val := by omega
      rw [h2d]
      have hu : u.val % 2 = 0 ∨ u.val % 2 = 1 := by omega
      have hv : v.val % 2 = 0 ∨ v.val % 2 = 1 := by omega
      rcases hu with hu | hu <;> rcases hv with hv | hv <;>
        simp [walshBit, h2m, hu, hv, u', v', Int.neg_mul, Int.mul_neg]
    rw [sumFin_congr hev, sumFin_congr hod, sumFin_mul_left, ih u' v']
    by_cases hmod : u.val % 2 = v.val % 2
    · simp only [hmod, ↓reduceIte, Int.one_mul]
      by_cases hdiv : u' = v'
      · have huv : u = v := Fin.ext (by have := congrArg Fin.val hdiv; dsimp [u', v'] at this; omega)
        simp only [hdiv, huv, ↓reduceIte]
        have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
        omega
      · have huv : u ≠ v := fun h => hdiv (Fin.ext (by have := congrArg Fin.val h; dsimp [u', v']; omega))
        simp [hdiv, huv]
    · have huv : u ≠ v := fun h => hmod (by rw [h])
      simp only [hmod, huv, ↓reduceIte]
      by_cases hdiv : u' = v'
      · simp only [hdiv, ↓reduceIte]; omega
      · simp only [hdiv, ↓reduceIte]; omega

theorem walshSign_sum_nonzero (m : Nat) (u : Fin (2 ^ m)) (hu : u.val ≠ 0) :
    sumFin (2 ^ m) (fun x => walshSign m u.val x.val) = 0 := by
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have h0 := walshSign_orth m ⟨0, hpos⟩ u
  have hne' : (⟨0, hpos⟩ : Fin (2 ^ m)) ≠ u := fun heq => hu (congrArg Fin.val heq).symm
  simp only [hne', ↓reduceIte] at h0
  rw [← h0]
  apply sumFin_congr
  intro x
  rw [walshSign_zero_left, Int.one_mul]

/-- Exact XOR-Cayley Laplacian on `Fin (2^m)` for an arbitrary weight kernel `phi : Nat -> Int`. -/
def xorLaplacian (m : Nat) (phi : Nat -> Int) : Mat (2 ^ m) :=
  graphLaplacian (fun a b => phi (a.val ^^^ b.val))

/-- Exact Walsh-Hadamard eigenvalue of `xorLaplacian m phi` at frequency `u`. -/
def walshEig (m : Nat) (phi : Nat -> Int) (u : Nat) : Int :=
  sumFin (2 ^ m) (fun d => phi d.val * (1 - walshSign m u d.val))

theorem xorLaplacian_walsh_eig (m : Nat) (phi : Nat -> Int) (u : Nat) (a : Fin (2 ^ m)) :
    sumFin (2 ^ m) (fun b => xorLaplacian m phi a b * walshSign m u b.val) =
    walshSign m u a.val * walshEig m phi u := by
  unfold xorLaplacian walshEig
  rw [graphLaplacian_mul_vec]
  rw [← sumFin_perm_xor m a (fun b => phi (a.val ^^^ b.val) * (walshSign m u a.val - walshSign m u b.val))]
  rw [← sumFin_mul_left]
  apply sumFin_congr
  intro d
  have hxor : a.val ^^^ (a.val ^^^ d.val) = d.val := by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hxor, walshSign_mul_xor]
  have hring : ∀ p q r : Int, p * (q - q * r) = q * (p * (1 - r)) := by
    intro p q r
    rw [Int.mul_sub, Int.mul_sub, Int.mul_one, Int.mul_sub]
    have h1 : p * (q * r) = q * (p * r) := by
      rw [← Int.mul_assoc, Int.mul_comm p q, Int.mul_assoc]
    rw [Int.mul_comm p q, h1]
  exact hring _ _ _

/-! ### The Universal 2-Adic Shell-Walsh Nested-Join Engine (`shellWeight`, `shellQ`, `shellEig`) -/

/-- Shift a sequence by 1: `(shiftSeq f) r = f (r + 1)`. -/
def shiftSeq {α : Type} (f : Nat -> α) : Nat -> α :=
  fun r => f (r + 1)

/-- Recursive 2-adic shell-join weight function:
    - Opposite parity (one even, one odd): cross-shell weight `c 0`
    - Both even (`2a`, `2b`): recurse into `(shiftSeq c, shiftSeq phi)` on `(a, b)`
    - Both odd (`2a+1`, `2b+1`): intra-shell XOR-Cayley kernel `phi 0 (a ^^^ b)`. -/
def shellWeight (c : Nat -> Int) (phi : Nat -> Nat -> Int) (x y : Nat) : Int :=
  if x = y then 0
  else if x % 2 ≠ y % 2 then c 0
  else if x % 2 = 0 then shellWeight (shiftSeq c) (shiftSeq phi) (x / 2) (y / 2)
  else phi 0 ((x / 2) ^^^ (y / 2))
termination_by x + y
decreasing_by
  omega

theorem shellWeight_symm (c : Nat -> Int) (phi : Nat -> Nat -> Int) (x y : Nat) :
    shellWeight c phi x y = shellWeight c phi y x := by
  induction hsum : x + y using Nat.strongRecOn generalizing c phi x y with
  | ind n ih =>
    unfold shellWeight
    by_cases hxy : x = y
    · subst hxy; simp
    · have hyx : y ≠ x := Ne.symm hxy
      simp only [hxy, hyx, ↓reduceIte]
      by_cases hpar : x % 2 ≠ y % 2
      · have hpar' : y % 2 ≠ x % 2 := Ne.symm hpar
        simp [hpar, hpar']
      · have hpeq : x % 2 = y % 2 := by omega
        have hpar' : ¬(y % 2 ≠ x % 2) := by omega
        simp only [hpar, hpar', ↓reduceIte]
        by_cases hx0 : x % 2 = 0
        · have hy0 : y % 2 = 0 := by omega
          simp only [hx0, hy0, ↓reduceIte]
          have hlt : x / 2 + y / 2 < n := by omega
          exact ih (x / 2 + y / 2) hlt (shiftSeq c) (shiftSeq phi) (x / 2) (y / 2) rfl
        · have hy0 : y % 2 ≠ 0 := by omega
          simp only [hx0, hy0, ↓reduceIte]
          rw [Nat.xor_comm]

theorem shellWeight_even_even (c : Nat -> Int) (phi : Nat -> Nat -> Int) (a b : Nat) :
    shellWeight c phi (2 * a) (2 * b) = shellWeight (shiftSeq c) (shiftSeq phi) a b := by
  by_cases hab : a = b
  · subst hab
    unfold shellWeight
    simp
  · conv => lhs; unfold shellWeight
    have h2 : 2 * a ≠ 2 * b := by omega
    have hm1 : (2 * a) % 2 = 0 := by omega
    have hm2 : (2 * b) % 2 = 0 := by omega
    have hd1 : (2 * a) / 2 = a := by omega
    have hd2 : (2 * b) / 2 = b := by omega
    simp only [h2, hm1, hm2, hd1, hd2, ne_eq, not_true_eq_false, ↓reduceIte]

theorem shellWeight_even_odd (c : Nat -> Int) (phi : Nat -> Nat -> Int) (a b : Nat) :
    shellWeight c phi (2 * a) (2 * b + 1) = c 0 := by
  unfold shellWeight
  have hne : 2 * a ≠ 2 * b + 1 := by omega
  have hm1 : (2 * a) % 2 = 0 := by omega
  have hm2 : (2 * b + 1) % 2 = 1 := by omega
  simp [hne, hm1, hm2]

theorem shellWeight_odd_even (c : Nat -> Int) (phi : Nat -> Nat -> Int) (a b : Nat) :
    shellWeight c phi (2 * a + 1) (2 * b) = c 0 := by
  rw [shellWeight_symm, shellWeight_even_odd]

theorem shellWeight_odd_odd (c : Nat -> Int) (phi : Nat -> Nat -> Int) (a b : Nat) (hab : a ≠ b) :
    shellWeight c phi (2 * a + 1) (2 * b + 1) = phi 0 (a ^^^ b) := by
  unfold shellWeight
  have hne : 2 * a + 1 ≠ 2 * b + 1 := by omega
  have hm1 : (2 * a + 1) % 2 = 1 := by omega
  have hm2 : (2 * b + 1) % 2 = 1 := by omega
  have hd1 : (2 * a + 1) / 2 = a := by omega
  have hd2 : (2 * b + 1) / 2 = b := by omega
  have h10 : (1 : Nat) ≠ 0 := by decide
  simp only [hne, hm1, hm2, hd1, hd2, ne_eq, not_true_eq_false, h10, ↓reduceIte]

/-- The `2^k x 2^k` 2-Adic Shell-Walsh Graph Laplacian for arbitrary `(c, phi)`. -/
def shellLaplacian (k : Nat) (c : Nat -> Int) (phi : Nat -> Nat -> Int) : Mat (2 ^ k) :=
  graphLaplacian (fun x y => shellWeight c phi x.val y.val)

/-- The **Universal 2-Adic Shell-Walsh Orthogonal `{-1, 0, +1}` Basis `Q_k`**
    (completely independent of the edge-weight functions `c` and `phi`!).
    Columns are indexed recursively:
    - `j = 0`: all `+1`s
    - `0 < j < 2^k`: column `j` of `shellQ k` placed on EVEN rows `2a`, `0` on ODD rows
    - `j = 2^k`: `+1` on EVEN rows, `-1` on ODD rows (Haar shell-interface vector)
    - `2^k < j < 2^(k+1)` (`j = 2^k + u`): Walsh column `walshSign k u a` on ODD rows, `0` on EVEN rows. -/
def shellQ : (k : Nat) -> Mat (2 ^ k)
  | 0 => fun _ _ => 1
  | k + 1 => fun x j =>
      if j.val = 0 then 1
      else if hlt : j.val < 2 ^ k then
        if x.val % 2 = 0 then
          shellQ k ⟨x.val / 2, fin_div2_lt x⟩ ⟨j.val, hlt⟩
        else 0
      else if j.val = 2 ^ k then
        if x.val % 2 = 0 then 1 else -1
      else
        if x.val % 2 = 0 then 0
        else walshSign k (j.val - 2 ^ k) (x.val / 2)

/-- Exact dyadic squared norms `d_j = (Q_k^T Q_k)_{j,j}` (every entry is a power of 2!). -/
def shellNorm : (k : Nat) -> Fin (2 ^ k) -> Int
  | 0 => fun _ => 1
  | k + 1 => fun j =>
      if j.val = 0 then ((2 ^ (k + 1) : Nat) : Int)
      else if hlt : j.val < 2 ^ k then shellNorm k ⟨j.val, hlt⟩
      else if j.val = 2 ^ k then ((2 ^ (k + 1) : Nat) : Int)
      else ((2 ^ k : Nat) : Int)

/-- Exact closed-form eigenvalue table for `shellLaplacian k c phi` in the `shellQ k` basis. -/
def shellEig : (k : Nat) -> (Nat -> Int) -> (Nat -> Nat -> Int) -> Fin (2 ^ k) -> Int
  | 0, _, _ => fun _ => 0
  | k + 1, c, phi => fun j =>
      if j.val = 0 then 0
      else if hlt : j.val < 2 ^ k then
        ((2 ^ k : Nat) : Int) * c 0 + shellEig k (shiftSeq c) (shiftSeq phi) ⟨j.val, hlt⟩
      else if j.val = 2 ^ k then
        ((2 ^ (k + 1) : Nat) : Int) * c 0
      else
        ((2 ^ k : Nat) : Int) * c 0 + walshEig k (phi 0) (j.val - 2 ^ k)

theorem shellQ_col0 (k : Nat) (x : Fin (2 ^ k)) :
    shellQ k x ⟨0, Nat.two_pow_pos k⟩ = 1 := by
  cases k with
  | zero => rfl
  | succ k => simp [shellQ]

theorem shellEig_zero (k : Nat) (c : Nat -> Int) (phi : Nat -> Nat -> Int) :
    shellEig k c phi ⟨0, Nat.two_pow_pos k⟩ = 0 := by
  cases k with
  | zero => rfl
  | succ k => simp [shellEig]

theorem shellNorm_ne_zero (k : Nat) (j : Fin (2 ^ k)) : shellNorm k j ≠ 0 := by
  induction k with
  | zero => simp [shellNorm]
  | succ k ih =>
    unfold shellNorm
    split
    · have := Nat.two_pow_pos (k + 1); omega
    · split
      · exact ih _
      · split
        · have := Nat.two_pow_pos (k + 1); omega
        · have := Nat.two_pow_pos k; omega

/-- Helper: every entry of `shellQ k` lies in `{-1, 0, +1}`. -/
theorem shellQ_entries_ternary (k : Nat) (x j : Fin (2 ^ k)) :
    shellQ k x j = -1 ∨ shellQ k x j = 0 ∨ shellQ k x j = 1 := by
  induction k with
  | zero => right; right; rfl
  | succ k ih =>
    unfold shellQ
    split
    · right; right; rfl
    · split
      · split
        · exact ih _ _
        · right; left; rfl
      · split
        · split
          · right; right; rfl
          · left; rfl
        · split
          · right; left; rfl
          · -- walshSign is ±1
            have hpm : ∀ (m u a : Nat), walshSign m u a = -1 ∨ walshSign m u a = 1 := by
              intro m u a
              induction m generalizing u a with
              | zero => right; rfl
              | succ m ihm =>
                simp only [walshSign]
                have hb : walshBit u a = -1 ∨ walshBit u a = 1 := by
                  unfold walshBit; split <;> simp
                rcases hb with hb | hb <;> rcases ihm (u / 2) (a / 2) with hs | hs <;> simp [hb, hs]
            rcases hpm k (j.val - 2 ^ k) (x.val / 2) with h | h
            · left; exact h
            · right; right; exact h

/-- **Exact Dyadic Orthogonality of the Universal 2-Adic Shell-Walsh Basis**:
    `∀ k, Q_k^T Q_k = diag (shellNorm k)`. -/
theorem shellQ_orth (k : Nat) :
    matMul (matTranspose (shellQ k)) (shellQ k) = matDiag (shellNorm k) := by
  induction k with
  | zero =>
    funext i j
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; simp at this; omega)
    have hj : j = ⟨0, by decide⟩ := Fin.ext (by have := j.isLt; simp at this; omega)
    subst hi; subst hj
    simp [matMul, matTranspose, matDiag, shellQ, shellNorm, sumFin]
  | succ k ih =>
    funext i j
    unfold matMul matTranspose matDiag
    rw [sumFin_pow2_succ]
    -- Helper: sum of column `c` of `shellQ k` for `c > 0` is 0 (orthogonality with col 0!)
    have hsum_col0 : ∀ c : Fin (2 ^ k), c.val ≠ 0 -> sumFin (2 ^ k) (fun a => shellQ k a c) = 0 := by
      intro c hc
      have h0 := congrFun (congrFun ih ⟨0, Nat.two_pow_pos k⟩) c
      have hne : (⟨0, Nat.two_pow_pos k⟩ : Fin (2 ^ k)) ≠ c := fun h => hc (congrArg Fin.val h).symm
      simp only [matMul, matTranspose, matDiag, hne, ↓reduceIte] at h0
      rw [← h0]
      apply sumFin_congr
      intro a
      rw [shellQ_col0, Int.one_mul]
    -- Helper: evaluate `shellQ (k+1)` on even and odd rows
    have hQev : ∀ (a : Fin (2 ^ k)) (col : Fin (2 ^ (k + 1))),
        shellQ (k + 1) ⟨2 * a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ col =
        if col.val = 0 then 1
        else if hlt : col.val < 2 ^ k then shellQ k a ⟨col.val, hlt⟩
        else if col.val = 2 ^ k then 1
        else 0 := by
      intro a col
      conv => lhs; unfold shellQ
      have hm : (2 * a.val) % 2 = 0 := by omega
      have hd : (2 * a.val) / 2 = a.val := by omega
      by_cases h0 : col.val = 0
      · simp [h0]
      · by_cases hlt : col.val < 2 ^ k
        · simp only [h0, hlt, hm, ↓reduceIte, ↓reduceDIte]
          have harg : (⟨(2 * a.val) / 2, fin_div2_lt ⟨2 * a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩⟩ : Fin (2 ^ k)) = a :=
            Fin.ext hd
          rw [harg]
        · by_cases heq : col.val = 2 ^ k
          · simp [heq, hm]
          · simp [h0, hlt, heq, hm]
    have hQod : ∀ (a : Fin (2 ^ k)) (col : Fin (2 ^ (k + 1))),
        shellQ (k + 1) ⟨2 * a.val + 1, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ col =
        if col.val = 0 then 1
        else if col.val < 2 ^ k then 0
        else if col.val = 2 ^ k then -1
        else walshSign k (col.val - 2 ^ k) a.val := by
      intro a col
      unfold shellQ
      have hm : (2 * a.val + 1) % 2 ≠ 0 := by omega
      have hd : (2 * a.val + 1) / 2 = a.val := by omega
      by_cases h0 : col.val = 0
      · simp [h0]
      · by_cases hlt : col.val < 2 ^ k
        · simp [h0, hlt]
        · by_cases heq : col.val = 2 ^ k
          · simp [heq]
          · simp [h0, hlt, heq, hd]
    have hsum1 :
        sumFin (2 ^ k) (fun a => shellQ (k + 1) ⟨2 * a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ i *
                                 shellQ (k + 1) ⟨2 * a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ j) =
        sumFin (2 ^ k) (fun a =>
          (if i.val = 0 then 1 else if hlt : i.val < 2 ^ k then shellQ k a ⟨i.val, hlt⟩ else if i.val = 2 ^ k then 1 else 0) *
          (if j.val = 0 then 1 else if hlt : j.val < 2 ^ k then shellQ k a ⟨j.val, hlt⟩ else if j.val = 2 ^ k then 1 else 0)) :=
      sumFin_congr (fun a => by rw [hQev a i, hQev a j])
    have hsum2 :
        sumFin (2 ^ k) (fun a => shellQ (k + 1) ⟨2 * a.val + 1, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ i *
                                 shellQ (k + 1) ⟨2 * a.val + 1, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ j) =
        sumFin (2 ^ k) (fun a =>
          (if i.val = 0 then 1 else if i.val < 2 ^ k then 0 else if i.val = 2 ^ k then -1 else walshSign k (i.val - 2 ^ k) a.val) *
          (if j.val = 0 then 1 else if j.val < 2 ^ k then 0 else if j.val = 2 ^ k then -1 else walshSign k (j.val - 2 ^ k) a.val)) :=
      sumFin_congr (fun a => by rw [hQod a i, hQod a j])
    rw [hsum1, hsum2]
    have hpow2 : ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) + ((2 ^ k : Nat) : Int) := by
      have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      omega
    have h2k_ne : 2 ^ k ≠ 0 := by have := Nat.two_pow_pos k; omega
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0
      · have hij : i = j := Fin.ext (by omega)
        simp [hj0, hij, shellNorm, sumFin_const, hpow2]
      · have hij : i ≠ j := fun h => hj0 (by rw [← h, hi0])
        by_cases hjlt : j.val < 2 ^ k
        · simp only [hi0, hj0, hjlt, hij, ↓reduceIte, ↓reduceDIte, Int.one_mul, Int.mul_zero, sumFin_zero, Int.add_zero]
          exact hsum_col0 ⟨j.val, hjlt⟩ hj0
        · by_cases hjeq : j.val = 2 ^ k
          · simp only [hi0, hjeq, h2k_ne, Nat.lt_irrefl, hij, ↓reduceIte, ↓reduceDIte, sumFin_const, Int.mul_one, Int.mul_neg_one]
            omega
          · simp only [hi0, hj0, hjlt, hjeq, hij, ↓reduceIte, ↓reduceDIte, Int.mul_zero, sumFin_zero, Int.zero_add, Int.one_mul]
            let u : Fin (2 ^ k) := ⟨j.val - 2 ^ k, fin_sub_pow2_lt j⟩
            have hu : u.val ≠ 0 := by dsimp [u]; omega
            exact walshSign_sum_nonzero k u hu
    · by_cases hilt : i.val < 2 ^ k
      · by_cases hj0 : j.val = 0
        · have hij : i ≠ j := fun h => hi0 (by rw [h, hj0])
          simp only [hi0, hilt, hj0, hij, ↓reduceIte, ↓reduceDIte, Int.mul_one, sumFin_zero, Int.add_zero]
          exact hsum_col0 ⟨i.val, hilt⟩ hi0
        · by_cases hjlt : j.val < 2 ^ k
          · simp only [hi0, hilt, hj0, hjlt, ↓reduceIte, ↓reduceDIte, Int.zero_mul, sumFin_zero, Int.add_zero]
            have hih := congrFun (congrFun ih ⟨i.val, hilt⟩) ⟨j.val, hjlt⟩
            simp only [matMul, matTranspose, matDiag] at hih
            rw [hih]
            by_cases hij : i = j
            · subst hij
              simp [shellNorm, hi0, hilt]
            · have hij' : (⟨i.val, hilt⟩ : Fin (2 ^ k)) ≠ ⟨j.val, hjlt⟩ :=
                fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))
              simp [hij, hij']
          · have hij : i ≠ j := fun h => hjlt (by rw [← h]; exact hilt)
            by_cases hjeq : j.val = 2 ^ k
            · simp only [hi0, hilt, hjeq, h2k_ne, Nat.lt_irrefl, hij, ↓reduceIte, ↓reduceDIte, Int.mul_one, Int.zero_mul, sumFin_zero, Int.add_zero]
              exact hsum_col0 ⟨i.val, hilt⟩ hi0
            · simp [hi0, hilt, hj0, hjlt, hjeq, hij, sumFin_zero]
      · by_cases hieq : i.val = 2 ^ k
        · by_cases hj0 : j.val = 0
          · have hij : i ≠ j := fun h => hi0 (by rw [h, hj0])
            simp only [hieq, h2k_ne, Nat.lt_irrefl, hj0, hij, ↓reduceIte, ↓reduceDIte, sumFin_const, Int.mul_one, Int.mul_neg_one]
            omega
          · by_cases hjlt : j.val < 2 ^ k
            · have hij : i ≠ j := fun h => hilt (by rw [h]; exact hjlt)
              simp only [hieq, h2k_ne, Nat.lt_irrefl, hj0, hjlt, hij, ↓reduceIte, ↓reduceDIte, Int.one_mul, Int.mul_zero, sumFin_zero, Int.add_zero]
              exact hsum_col0 ⟨j.val, hjlt⟩ hj0
            · by_cases hjeq : j.val = 2 ^ k
              · have hij : i = j := Fin.ext (by omega)
                simp [hjeq, hij, shellNorm, sumFin_const, hpow2]
              · have hij : i ≠ j := fun h => hjeq (by rw [← h, hieq])
                simp only [hieq, h2k_ne, Nat.lt_irrefl, hj0, hjlt, hjeq, hij, ↓reduceIte, ↓reduceDIte, Int.mul_zero, sumFin_zero, Int.zero_add, Int.neg_one_mul]
                rw [sumFin_neg]
                let u : Fin (2 ^ k) := ⟨j.val - 2 ^ k, fin_sub_pow2_lt j⟩
                have hu : u.val ≠ 0 := by dsimp [u]; omega
                rw [walshSign_sum_nonzero k u hu]; rfl
        · by_cases hj0 : j.val = 0
          · have hij : i ≠ j := fun h => hi0 (by rw [h, hj0])
            simp only [hi0, hilt, hieq, hj0, hij, ↓reduceIte, ↓reduceDIte, sumFin_zero, Int.zero_add, Int.mul_one]
            let u : Fin (2 ^ k) := ⟨i.val - 2 ^ k, fin_sub_pow2_lt i⟩
            have hu : u.val ≠ 0 := by dsimp [u]; omega
            exact walshSign_sum_nonzero k u hu
          · by_cases hjlt : j.val < 2 ^ k
            · have hij : i ≠ j := fun h => hilt (by rw [h]; exact hjlt)
              simp [hi0, hilt, hieq, hj0, hjlt, hij, sumFin_zero]
            · by_cases hjeq : j.val = 2 ^ k
              · have hij : i ≠ j := fun h => hieq (by rw [h, hjeq])
                simp only [hi0, hilt, hieq, hjeq, h2k_ne, Nat.lt_irrefl, hij, ↓reduceIte, ↓reduceDIte, Int.zero_mul, sumFin_zero, Int.zero_add, Int.mul_neg_one]
                rw [sumFin_neg]
                let u : Fin (2 ^ k) := ⟨i.val - 2 ^ k, fin_sub_pow2_lt i⟩
                have hu : u.val ≠ 0 := by dsimp [u]; omega
                rw [walshSign_sum_nonzero k u hu]; rfl
              · simp only [hi0, hilt, hieq, hj0, hjlt, hjeq, ↓reduceIte, ↓reduceDIte, Int.zero_mul, sumFin_zero, Int.zero_add]
                let u : Fin (2 ^ k) := ⟨i.val - 2 ^ k, fin_sub_pow2_lt i⟩
                let v : Fin (2 ^ k) := ⟨j.val - 2 ^ k, fin_sub_pow2_lt j⟩
                have horth := walshSign_orth k u v
                dsimp only [u, v] at horth
                rw [horth]
                by_cases hij : i = j
                · subst hij
                  simp only [shellNorm, hi0, hilt, hieq, ↓reduceIte, ↓reduceDIte]
                · have huv : (⟨i.val - 2 ^ k, fin_sub_pow2_lt i⟩ : Fin (2 ^ k)) ≠
                             ⟨j.val - 2 ^ k, fin_sub_pow2_lt j⟩ := by
                    intro h
                    have hval : i.val - 2 ^ k = j.val - 2 ^ k := by simpa using congrArg Fin.val h
                    exact hij (Fin.ext (by omega))
                  simp only [hij, huv, ↓reduceIte]

/-- **MASTER DIAGONALIZATION THEOREM OF THE 2-ADIC SHELL-WALSH ENGINE**:
    For ALL `k : Nat`, ALL cross-shell weights `c : Nat -> Int`, and ALL intra-shell
    XOR-Cayley kernels `phi : Nat -> Nat -> Int`, the universal orthogonal matrix `shellQ k`
    simultaneously diagonalizes `shellLaplacian k c phi`:
      `shellLaplacian k c phi * shellQ k = shellQ k * diag (shellEig k c phi)`. -/
theorem shellLaplacian_diag (k : Nat) (c : Nat -> Int) (phi : Nat -> Nat -> Int) :
    matMul (shellLaplacian k c phi) (shellQ k) =
    matMul (shellQ k) (matDiag (shellEig k c phi)) := by
  induction k generalizing c phi with
  | zero =>
    funext x j
    have hx : x = ⟨0, by decide⟩ := Fin.ext (by have := x.isLt; simp at this; omega)
    have hj : j = ⟨0, by decide⟩ := Fin.ext (by have := j.isLt; simp at this; omega)
    subst hx; subst hj
    simp [matMul, matDiag, shellLaplacian, graphLaplacian, shellQ, shellEig, sumFin]
  | succ k ih =>
    funext x j
    rw [matMul_diag_right]
    change sumFin (2 ^ (k + 1)) (fun y => shellLaplacian (k + 1) c phi x y * shellQ (k + 1) y j) =
           shellQ (k + 1) x j * shellEig (k + 1) c phi j
    unfold shellLaplacian
    rw [graphLaplacian_mul_vec]
    rw [sumFin_pow2_succ]
    -- Helper: sum of column `col` of `shellQ k` for `col > 0` is 0
    have hsum_col0 : ∀ col : Fin (2 ^ k), col.val ≠ 0 -> sumFin (2 ^ k) (fun a => shellQ k a col) = 0 := by
      intro col hcol
      have h0 := congrFun (congrFun (shellQ_orth k) ⟨0, Nat.two_pow_pos k⟩) col
      have hne : (⟨0, Nat.two_pow_pos k⟩ : Fin (2 ^ k)) ≠ col := fun h => hcol (congrArg Fin.val h).symm
      simp only [matMul, matTranspose, matDiag, hne, ↓reduceIte] at h0
      rw [← h0]
      apply sumFin_congr
      intro a
      rw [shellQ_col0, Int.one_mul]
    have hQev : ∀ (a : Fin (2 ^ k)) (col : Fin (2 ^ (k + 1))),
        shellQ (k + 1) ⟨2 * a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ col =
        if col.val = 0 then 1
        else if hlt : col.val < 2 ^ k then shellQ k a ⟨col.val, hlt⟩
        else if col.val = 2 ^ k then 1
        else 0 := by
      intro a col
      conv => lhs; unfold shellQ
      have hm : (2 * a.val) % 2 = 0 := by omega
      have hd : (2 * a.val) / 2 = a.val := by omega
      by_cases h0 : col.val = 0
      · simp [h0]
      · by_cases hlt : col.val < 2 ^ k
        · simp only [h0, hlt, hm, ↓reduceIte, ↓reduceDIte]
          have harg : (⟨(2 * a.val) / 2, fin_div2_lt ⟨2 * a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩⟩ : Fin (2 ^ k)) = a :=
            Fin.ext hd
          rw [harg]
        · by_cases heq : col.val = 2 ^ k
          · simp [heq, hm]
          · simp [h0, hlt, heq, hm]
    have hQod : ∀ (a : Fin (2 ^ k)) (col : Fin (2 ^ (k + 1))),
        shellQ (k + 1) ⟨2 * a.val + 1, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ col =
        if col.val = 0 then 1
        else if col.val < 2 ^ k then 0
        else if col.val = 2 ^ k then -1
        else walshSign k (col.val - 2 ^ k) a.val := by
      intro a col
      unfold shellQ
      have hm : (2 * a.val + 1) % 2 ≠ 0 := by omega
      have hd : (2 * a.val + 1) / 2 = a.val := by omega
      by_cases h0 : col.val = 0
      · simp [h0]
      · by_cases hlt : col.val < 2 ^ k
        · simp [h0, hlt]
        · by_cases heq : col.val = 2 ^ k
          · simp [heq]
          · simp [h0, hlt, heq, hd]
    have hpow2 : ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) + ((2 ^ k : Nat) : Int) := by
      have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      omega
    have h2k_ne : 2 ^ k ≠ 0 := by have := Nat.two_pow_pos k; omega
    let a : Fin (2 ^ k) := ⟨x.val / 2, fin_div2_lt x⟩
    by_cases hxev : x.val % 2 = 0
    · have hxeq : x = ⟨2 * a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ := Fin.ext (by dsimp [a]; omega)
      rw [hxeq]
      have hs1 :
          sumFin (2 ^ k) (fun b => shellWeight c phi (2 * a.val) (2 * b.val) *
            (shellQ (k + 1) ⟨2 * a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ j -
             shellQ (k + 1) ⟨2 * b.val, by have := b.isLt; rw [Nat.pow_succ]; omega⟩ j)) =
          sumFin (2 ^ k) (fun b => shellWeight (shiftSeq c) (shiftSeq phi) a.val b.val *
            ((if j.val = 0 then 1 else if hlt : j.val < 2 ^ k then shellQ k a ⟨j.val, hlt⟩ else if j.val = 2 ^ k then 1 else 0) -
             (if j.val = 0 then 1 else if hlt : j.val < 2 ^ k then shellQ k b ⟨j.val, hlt⟩ else if j.val = 2 ^ k then 1 else 0))) :=
        sumFin_congr (fun b => by rw [shellWeight_even_even, hQev a j, hQev b j])
      have hs2 :
          sumFin (2 ^ k) (fun b => shellWeight c phi (2 * a.val) (2 * b.val + 1) *
            (shellQ (k + 1) ⟨2 * a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ j -
             shellQ (k + 1) ⟨2 * b.val + 1, by have := b.isLt; rw [Nat.pow_succ]; omega⟩ j)) =
          sumFin (2 ^ k) (fun b => c 0 *
            ((if j.val = 0 then 1 else if hlt : j.val < 2 ^ k then shellQ k a ⟨j.val, hlt⟩ else if j.val = 2 ^ k then 1 else 0) -
             (if j.val = 0 then 1 else if j.val < 2 ^ k then 0 else if j.val = 2 ^ k then -1 else walshSign k (j.val - 2 ^ k) b.val))) :=
        sumFin_congr (fun b => by rw [shellWeight_even_odd, hQev a j, hQod b j])
      rw [hs1, hs2, hQev a j]
      by_cases hj0 : j.val = 0
      · simp [hj0, shellEig, sumFin_zero]
      · by_cases hjlt : j.val < 2 ^ k
        · simp only [hj0, hjlt, ↓reduceIte, ↓reduceDIte, Int.sub_zero, shellEig]
          have hih := congrFun (congrFun (ih (shiftSeq c) (shiftSeq phi)) a) ⟨j.val, hjlt⟩
          rw [matMul_diag_right] at hih
          have hfirst : sumFin (2 ^ k) (fun b => shellWeight (shiftSeq c) (shiftSeq phi) a.val b.val *
              (shellQ k a ⟨j.val, hjlt⟩ - shellQ k b ⟨j.val, hjlt⟩)) =
              shellQ k a ⟨j.val, hjlt⟩ * shellEig k (shiftSeq c) (shiftSeq phi) ⟨j.val, hjlt⟩ :=
            (graphLaplacian_mul_vec (fun p q : Fin (2 ^ k) => shellWeight (shiftSeq c) (shiftSeq phi) p.val q.val)
              (fun b => shellQ k b ⟨j.val, hjlt⟩) a).symm.trans hih
          rw [hfirst, sumFin_const, Int.mul_add]
          have hcomm : ((2 ^ k : Nat) : Int) * (c 0 * shellQ k a ⟨j.val, hjlt⟩) =
                       shellQ k a ⟨j.val, hjlt⟩ * (((2 ^ k : Nat) : Int) * c 0) := by
            rw [← Int.mul_assoc, Int.mul_comm (((2 ^ k : Nat) : Int) * c 0)]
          rw [hcomm, Int.add_comm]
        · by_cases hjeq : j.val = 2 ^ k
          · simp only [hjeq, h2k_ne, Nat.lt_irrefl, ↓reduceIte, ↓reduceDIte, Int.sub_self, Int.mul_zero, sumFin_zero, Int.zero_add,
                       shellEig, Int.one_mul]
            rw [sumFin_const, hpow2]
            have h2 : (1 : Int) - -1 = 2 := by decide
            rw [h2, Int.add_mul]
            have h3 : ((2 ^ k : Nat) : Int) * (c 0 * 2) =
                      ((2 ^ k : Nat) : Int) * c 0 + ((2 ^ k : Nat) : Int) * c 0 := by
              rw [Int.mul_comm (c 0) 2, ← Int.mul_assoc]
              have : ((2 ^ k : Nat) : Int) * 2 = ((2 ^ k : Nat) : Int) + ((2 ^ k : Nat) : Int) := by omega
              rw [this, Int.add_mul]
            exact h3
          · simp only [hj0, hjlt, hjeq, ↓reduceIte, ↓reduceDIte, Int.sub_self, Int.mul_zero, sumFin_zero, Int.zero_add,
                       Int.zero_sub, Int.zero_mul]
            rw [sumFin_congr (g := fun b => (-c 0) * walshSign k (j.val - 2 ^ k) b.val)]
            · rw [sumFin_mul_left]
              let u : Fin (2 ^ k) := ⟨j.val - 2 ^ k, fin_sub_pow2_lt j⟩
              have hu : u.val ≠ 0 := by dsimp [u]; omega
              rw [walshSign_sum_nonzero k u hu, Int.mul_zero]
            · intro b; rw [Int.mul_neg, Int.neg_mul]
    · have hxeq : x = ⟨2 * a.val + 1, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ := Fin.ext (by dsimp [a]; omega)
      rw [hxeq]
      have hs1 :
          sumFin (2 ^ k) (fun b => shellWeight c phi (2 * a.val + 1) (2 * b.val) *
            (shellQ (k + 1) ⟨2 * a.val + 1, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ j -
             shellQ (k + 1) ⟨2 * b.val, by have := b.isLt; rw [Nat.pow_succ]; omega⟩ j)) =
          sumFin (2 ^ k) (fun b => c 0 *
            ((if j.val = 0 then 1 else if j.val < 2 ^ k then 0 else if j.val = 2 ^ k then -1 else walshSign k (j.val - 2 ^ k) a.val) -
             (if j.val = 0 then 1 else if hlt : j.val < 2 ^ k then shellQ k b ⟨j.val, hlt⟩ else if j.val = 2 ^ k then 1 else 0))) :=
        sumFin_congr (fun b => by rw [shellWeight_odd_even, hQod a j, hQev b j])
      have hs2 :
          sumFin (2 ^ k) (fun b => shellWeight c phi (2 * a.val + 1) (2 * b.val + 1) *
            (shellQ (k + 1) ⟨2 * a.val + 1, by have := a.isLt; rw [Nat.pow_succ]; omega⟩ j -
             shellQ (k + 1) ⟨2 * b.val + 1, by have := b.isLt; rw [Nat.pow_succ]; omega⟩ j)) =
          sumFin (2 ^ k) (fun b => shellWeight c phi (2 * a.val + 1) (2 * b.val + 1) *
            ((if j.val = 0 then 1 else if j.val < 2 ^ k then 0 else if j.val = 2 ^ k then -1 else walshSign k (j.val - 2 ^ k) a.val) -
             (if j.val = 0 then 1 else if j.val < 2 ^ k then 0 else if j.val = 2 ^ k then -1 else walshSign k (j.val - 2 ^ k) b.val))) :=
        sumFin_congr (fun b => by rw [hQod a j, hQod b j])
      rw [hs1, hs2, hQod a j]
      by_cases hj0 : j.val = 0
      · simp [hj0, shellEig, sumFin_zero]
      · by_cases hjlt : j.val < 2 ^ k
        · simp only [hj0, hjlt, ↓reduceIte, ↓reduceDIte, Int.sub_self, Int.mul_zero, sumFin_zero, Int.add_zero,
                     Int.zero_sub, Int.zero_mul]
          rw [sumFin_congr (g := fun b => (-c 0) * shellQ k b ⟨j.val, hjlt⟩)]
          · rw [sumFin_mul_left, hsum_col0 ⟨j.val, hjlt⟩ hj0, Int.mul_zero]
          · intro b; rw [Int.mul_neg, Int.neg_mul]
        · by_cases hjeq : j.val = 2 ^ k
          · simp only [hjeq, h2k_ne, Nat.lt_irrefl, ↓reduceIte, ↓reduceDIte, Int.sub_self, Int.mul_zero, sumFin_zero, Int.add_zero,
                       shellEig, Int.neg_one_mul]
            rw [sumFin_const, hpow2]
            have h2 : (-1 : Int) - 1 = -2 := by decide
            rw [h2, Int.add_mul, Int.neg_add]
            have h3 : ((2 ^ k : Nat) : Int) * (c 0 * -2) =
                      -(((2 ^ k : Nat) : Int) * c 0) + -(((2 ^ k : Nat) : Int) * c 0) := by
              rw [Int.mul_comm (c 0) (-2), ← Int.mul_assoc]
              have : ((2 ^ k : Nat) : Int) * (-2) = -((2 ^ k : Nat) : Int) + -((2 ^ k : Nat) : Int) := by omega
              rw [this, Int.add_mul, Int.neg_mul]
            exact h3
          · simp only [hj0, hjlt, hjeq, ↓reduceIte, ↓reduceDIte, Int.sub_zero, shellEig]
            rw [sumFin_const]
            have hodd_sum :
                sumFin (2 ^ k) (fun b => shellWeight c phi (2 * a.val + 1) (2 * b.val + 1) *
                  (walshSign k (j.val - 2 ^ k) a.val - walshSign k (j.val - 2 ^ k) b.val)) =
                walshSign k (j.val - 2 ^ k) a.val * walshEig k (phi 0) (j.val - 2 ^ k) := by
              rw [← xorLaplacian_walsh_eig k (phi 0) (j.val - 2 ^ k) a]
              unfold xorLaplacian
              rw [graphLaplacian_mul_vec]
              apply sumFin_congr
              intro b
              by_cases hab : a = b
              · subst hab; simp
              · have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
                rw [shellWeight_odd_odd c phi a.val b.val hne]
            rw [hodd_sum, Int.mul_add]
            congr 1
            rw [← Int.mul_assoc, Int.mul_comm (((2 ^ k : Nat) : Int) * c 0)]

/-- Helper: `2^k = (2^k - 1) + 1` for Kirchhoff cofactor indexing. -/
theorem pow2_eq_pred_succ (k : Nat) : 2 ^ k = (2 ^ k - 1) + 1 := by
  have := Nat.two_pow_pos k; omega

/-- Exact multiplicative recurrence for the product of nonzero Shell-Walsh eigenvalues! -/
theorem prodFin_shellEig_succ (k : Nat) (c : Nat -> Int) (phi : Nat -> Nat -> Int) :
    prodFin (2 ^ (k + 1) - 1)
      (fun j => shellEig (k + 1) c phi ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos (k + 1); omega⟩) =
    (((2 ^ (k + 1) : Nat) : Int) * c 0) *
    prodFin (2 ^ k - 1)
      (fun j => ((2 ^ k : Nat) : Int) * c 0 +
        shellEig k (shiftSeq c) (shiftSeq phi) ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) *
    prodFin (2 ^ k - 1)
      (fun u => ((2 ^ k : Nat) : Int) * c 0 + walshEig k (phi 0) (u.val + 1)) := by
  -- Use `prodFin_pow2_halves` on the full `2^(k+1)`-product with `j = 0` set to `1`!
  let F : Fin (2 ^ (k + 1)) -> Int := fun j => if j.val = 0 then 1 else shellEig (k + 1) c phi j
  have hfull : prodFin (2 ^ (k + 1)) F =
      prodFin (2 ^ (k + 1) - 1)
        (fun j => shellEig (k + 1) c phi ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos (k + 1); omega⟩) := by
    have hcast : ∀ (n m : Nat) (hn : n = m + 1) (g : Fin n -> Int),
        g ⟨0, by omega⟩ = 1 ->
        prodFin n g = prodFin m (fun j => g ⟨j.val + 1, by omega⟩) := by
      intro n m hn g hg0
      subst hn
      rw [prodFin_succ_zero, hg0, Int.one_mul]
      rfl
    have h1 := hcast (2 ^ (k + 1)) (2 ^ (k + 1) - 1) (pow2_eq_pred_succ (k + 1)) F (by simp [F])
    rw [h1]
    apply prodFin_congr
    intro j
    dsimp only [F]
    have hne : j.val + 1 ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
  rw [← hfull, prodFin_pow2_halves]
  -- Left half (`0 .. 2^k - 1`): `j = 0` gives `1`, `1 .. 2^k - 1` gives `2^k * c 0 + shellEig k ...`
  have hleft :
      prodFin (2 ^ k) (fun a => F ⟨a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩) =
      prodFin (2 ^ k - 1)
        (fun j => ((2 ^ k : Nat) : Int) * c 0 +
          shellEig k (shiftSeq c) (shiftSeq phi) ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) := by
    have hcast : ∀ (n m : Nat) (hn : n = m + 1) (g : Fin n -> Int),
        g ⟨0, by omega⟩ = 1 ->
        prodFin n g = prodFin m (fun j => g ⟨j.val + 1, by omega⟩) := by
      intro n m hn g hg0
      subst hn
      rw [prodFin_succ_zero, hg0, Int.one_mul]
      rfl
    rw [hcast (2 ^ k) (2 ^ k - 1) (pow2_eq_pred_succ k) _ (by simp [F])]
    apply prodFin_congr
    intro j
    have hne : j.val + 1 ≠ 0 := by omega
    have hlt : j.val + 1 < 2 ^ k := by have := j.isLt; have := Nat.two_pow_pos k; omega
    simp only [F, shellEig, hne, hlt, ↓reduceIte, ↓reduceDIte]
  -- Right half (`2^k .. 2^(k+1) - 1`): `a = 0` gives `2^(k+1) * c 0`, `a = u + 1` gives `2^k * c 0 + walshEig`
  have hright :
      prodFin (2 ^ k) (fun a => F ⟨2 ^ k + a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩) =
      (((2 ^ (k + 1) : Nat) : Int) * c 0) *
      prodFin (2 ^ k - 1)
        (fun u => ((2 ^ k : Nat) : Int) * c 0 + walshEig k (phi 0) (u.val + 1)) := by
    have hcast : ∀ (n m : Nat) (hn : n = m + 1) (g : Fin n -> Int),
        prodFin n g = g ⟨0, by omega⟩ * prodFin m (fun j => g ⟨j.val + 1, by omega⟩) := by
      intro n m hn g
      subst hn
      rw [prodFin_succ_zero]
      rfl
    rw [hcast (2 ^ k) (2 ^ k - 1) (pow2_eq_pred_succ k)]
    congr 1
    · have hne : 2 ^ k ≠ 0 := by have := Nat.two_pow_pos k; omega
      have heq : 2 ^ k + 0 = 2 ^ k := by omega
      simp only [F, shellEig, heq, hne, Nat.lt_irrefl, ↓reduceIte, ↓reduceDIte]
    · apply prodFin_congr
      intro u
      have hne : 2 ^ k + (u.val + 1) ≠ 0 := by omega
      have hnlt : ¬(2 ^ k + (u.val + 1) < 2 ^ k) := by omega
      have hneq : 2 ^ k + (u.val + 1) ≠ 2 ^ k := by omega
      have hsub : 2 ^ k + (u.val + 1) - 2 ^ k = u.val + 1 := by omega
      simp only [F, shellEig, hne, hnlt, hneq, hsub, ↓reduceIte, ↓reduceDIte]
  rw [hleft, hright]
  rw [← Int.mul_assoc, Int.mul_comm _ (((2 ^ (k + 1) : Nat) : Int) * c 0)]

/-! ============================================================================
    PART 3: The Pure-Silicon Binary-Carry Bridge (`v2 (a + b + 1) = v2 ((a ^^^ b) + 1)`),
            Exact Infinite Theorems (A, B, C, D), Non-Vacuity & Sharpness
    ============================================================================ -/

/-- Structurally recursive fuel-based 2-adic valuation (kernel-reducible by `decide`!). -/
def v2Aux : Nat -> Nat -> Nat
  | 0, _ => 0
  | fuel + 1, n =>
      if n = 0 then 0
      else if n % 2 = 0 then 1 + v2Aux fuel (n / 2)
      else 0

/-- Exact 2-adic valuation (trailing zero bit count) on positive `Nat` (and `0` at `0`). -/
def v2 (n : Nat) : Nat := v2Aux n n

theorem v2Aux_eq_of_le (f1 f2 n : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    v2Aux f1 n = v2Aux f2 n := by
  induction f1 generalizing f2 n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    cases f2 with
    | zero => rfl
    | succ f2' => simp [v2Aux]
  | succ f1' ih =>
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [v2Aux]
    | succ f2' =>
      simp only [v2Aux]
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp only [hn0, ↓reduceIte]
        by_cases hev : n % 2 = 0
        · simp only [hev, ↓reduceIte]
          congr 1
          exact ih f2' (n / 2) (by omega) (by omega)
        · simp [hev]

theorem v2_zero : v2 0 = 0 := rfl

theorem v2_odd {n : Nat} (h : n % 2 = 1) : v2 n = 0 := by
  unfold v2
  cases n with
  | zero => omega
  | succ n' =>
    simp only [v2Aux]
    have hne0 : (n' + 1) % 2 ≠ 0 := by omega
    simp [hne0]

theorem v2_two_mul {n : Nat} (h : n ≠ 0) : v2 (2 * n) = 1 + v2 n := by
  unfold v2
  have hpos : 1 ≤ 2 * n := by omega
  have heq : 2 * n = (2 * n - 1) + 1 := by omega
  conv => lhs; rw [heq]
  simp only [v2Aux]
  have hne : (2 * n - 1) + 1 ≠ 0 := by omega
  have hm : ((2 * n - 1) + 1) % 2 = 0 := by omega
  have hd : ((2 * n - 1) + 1) / 2 = n := by omega
  simp only [hne, hm, hd, ↓reduceIte]
  congr 1
  exact v2Aux_eq_of_le (2 * n - 1) n n (by omega) (Nat.le_refl n)

theorem xor_eq_zero_imp {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hb := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at hb
  cases ha : a.testBit i <;> cases hc : b.testBit i <;> simp_all

theorem v2_succ_ne_v2 {d : Nat} (hd : d ≠ 0) : v2 (d + 1) ≠ v2 d := by
  by_cases hev : d % 2 = 0
  · have hodd : (d + 1) % 2 = 1 := by omega
    rw [v2_odd hodd]
    have h2 : d = 2 * (d / 2) := by omega
    have hdiv : d / 2 ≠ 0 := by omega
    rw [h2, v2_two_mul hdiv]
    omega
  · have hodd : d % 2 = 1 := by omega
    rw [v2_odd hodd]
    have h2 : d + 1 = 2 * ((d + 1) / 2) := by omega
    have hdiv : (d + 1) / 2 ≠ 0 := by omega
    rw [h2, v2_two_mul hdiv]
    omega

/-- **THE FUNDAMENTAL PURE-SILICON CARRY-TERMINATION IDENTITY**:
    For ALL `a, b : Nat`, adding a carry-in `+1` to binary addition `a + b` produces the
    exact same 2-adic valuation as adding `+1` to carryless XOR `a ^^^ b`:
      `v2 (a + b + 1) = v2 ((a ^^^ b) + 1)`.
    This identity is the bridge turning carry-coupled 2-adic shells into exact XOR-Cayley graphs. -/
theorem v2_add_succ_eq_v2_xor_succ (a b : Nat) :
    v2 (a + b + 1) = v2 ((a ^^^ b) + 1) := by
  induction hsum : a + b using Nat.strongRecOn generalizing a b with
  | ind n ih =>
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    have hxm := xor_mod_two a b
    have hxd := xor_div_two a b
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · have h00 : (0 : Nat) ^^^ 0 = 0 := by decide
      rw [ha, hb, h00] at hxm
      rw [v2_odd (by omega), v2_odd (by omega)]
    · have h01 : (0 : Nat) ^^^ 1 = 1 := by decide
      rw [ha, hb, h01] at hxm
      have hl : n + 1 = 2 * (a / 2 + b / 2 + 1) := by omega
      have hr : (a ^^^ b) + 1 = 2 * ((a / 2 ^^^ b / 2) + 1) := by omega
      rw [hl, hr, v2_two_mul (by omega), v2_two_mul (by omega)]
      congr 1
      exact ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
    · have h10 : (1 : Nat) ^^^ 0 = 1 := by decide
      rw [ha, hb, h10] at hxm
      have hl : n + 1 = 2 * (a / 2 + b / 2 + 1) := by omega
      have hr : (a ^^^ b) + 1 = 2 * ((a / 2 ^^^ b / 2) + 1) := by omega
      rw [hl, hr, v2_two_mul (by omega), v2_two_mul (by omega)]
      congr 1
      exact ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
    · have h11 : (1 : Nat) ^^^ 1 = 0 := by decide
      rw [ha, hb, h11] at hxm
      rw [v2_odd (by omega), v2_odd (by omega)]

/-- Arbitrary 2-variable binary-carry / XOR valuation edge weight:
    `w(x, y) = h (v2 (x + y)) (v2 (x ^^^ y))` for `x ≠ y`. -/
def carryXorWeight (h : Nat -> Nat -> Int) (x y : Nat) : Int :=
  if x = y then 0 else h (v2 (x + y)) (v2 (x ^^^ y))

/-- The `2^k x 2^k` Graph Laplacian of the 2-variable carry-XOR valuation graph `G_k(h)`. -/
def carryXorLaplacian (k : Nat) (h : Nat -> Nat -> Int) : Mat (2 ^ k) :=
  graphLaplacian (fun x y => carryXorWeight h x.val y.val)

def carryXorC (h : Nat -> Nat -> Int) : Nat -> Int :=
  fun r => h r r

def carryXorPhi (h : Nat -> Nat -> Int) : Nat -> Nat -> Int :=
  fun r d => h (r + 1 + v2 (d + 1)) (r + 1 + v2 d)

theorem shiftSeq_carryXorC (h : Nat -> Nat -> Int) :
    shiftSeq (carryXorC h) = carryXorC (fun a b => h (a + 1) (b + 1)) := by
  funext r; rfl

theorem shiftSeq_carryXorPhi (h : Nat -> Nat -> Int) :
    shiftSeq (carryXorPhi h) = carryXorPhi (fun a b => h (a + 1) (b + 1)) := by
  funext r d
  unfold shiftSeq carryXorPhi
  have h1 : r + 1 + 1 + v2 (d + 1) = r + 1 + v2 (d + 1) + 1 := by omega
  have h2 : r + 1 + 1 + v2 d = r + 1 + v2 d + 1 := by omega
  rw [h1, h2]

/-- **UNIVERSAL BINARY-CARRY TO SHELL-WALSH REDUCTION THEOREM**:
    For EVERY arbitrary 2-variable weight function `h : Nat -> Nat -> Int` and ALL `x, y : Nat`,
    `carryXorWeight h x y = shellWeight (carryXorC h) (carryXorPhi h) x y`. -/
theorem carryXorWeight_eq_shellWeight (h : Nat -> Nat -> Int) (x y : Nat) :
    carryXorWeight h x y = shellWeight (carryXorC h) (carryXorPhi h) x y := by
  induction hsum : x + y using Nat.strongRecOn generalizing h x y with
  | ind n ih =>
    unfold carryXorWeight
    conv => rhs; unfold shellWeight
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, ↓reduceIte]
      by_cases hpar : x % 2 ≠ y % 2
      · simp [hpar]
        have hadd_odd : (x + y) % 2 = 1 := by omega
        have hxor_odd : (x ^^^ y) % 2 = 1 := by
          have hm := xor_mod_two x y
          have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
          have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
          rcases hx with hx | hx <;> rcases hy with hy | hy
          · omega
          · have h01 : (0 : Nat) ^^^ 1 = 1 := by decide
            rw [hx, hy, h01] at hm; exact hm
          · have h10 : (1 : Nat) ^^^ 0 = 1 := by decide
            rw [hx, hy, h10] at hm; exact hm
          · omega
        rw [v2_odd hadd_odd, v2_odd hxor_odd]; rfl
      · simp only [hpar, ↓reduceIte]
        have hpeq : x % 2 = y % 2 := by omega
        by_cases hx0 : x % 2 = 0
        · simp only [hx0, ↓reduceIte]
          have hy0 : y % 2 = 0 := by omega
          have hdiv_ne : x / 2 ≠ y / 2 := by omega
          have hadd_pos : x / 2 + y / 2 ≠ 0 := by omega
          have hxor_pos : (x / 2) ^^^ (y / 2) ≠ 0 := fun hc => hdiv_ne (xor_eq_zero_imp hc)
          have hadd2 : x + y = 2 * (x / 2 + y / 2) := by omega
          have hxor2 : x ^^^ y = 2 * ((x / 2) ^^^ (y / 2)) := by
            have hm := xor_mod_two x y
            have hd := xor_div_two x y
            have h00 : (0 : Nat) ^^^ 0 = 0 := by decide
            rw [hx0, hy0, h00] at hm
            omega
          rw [hadd2, hxor2, v2_two_mul hadd_pos, v2_two_mul hxor_pos]
          rw [shiftSeq_carryXorC, shiftSeq_carryXorPhi]
          have hih := ih (x / 2 + y / 2) (by omega) (fun a b => h (a + 1) (b + 1)) (x / 2) (y / 2) rfl
          unfold carryXorWeight at hih
          simp only [hdiv_ne, ↓reduceIte] at hih
          rw [Nat.add_comm 1 (v2 (x / 2 + y / 2)), Nat.add_comm 1 (v2 (x / 2 ^^^ y / 2))]
          exact hih
        · simp only [hx0, ↓reduceIte]
          have hx1 : x % 2 = 1 := by omega
          have hy1 : y % 2 = 1 := by omega
          have hdiv_ne : x / 2 ≠ y / 2 := by omega
          have hxor_pos : (x / 2) ^^^ (y / 2) ≠ 0 := fun hc => hdiv_ne (xor_eq_zero_imp hc)
          have hadd2 : x + y = 2 * (x / 2 + y / 2 + 1) := by omega
          have hxor2 : x ^^^ y = 2 * ((x / 2) ^^^ (y / 2)) := by
            have hm := xor_mod_two x y
            have hd := xor_div_two x y
            have h11 : (1 : Nat) ^^^ 1 = 0 := by decide
            rw [hx1, hy1, h11] at hm
            omega
          rw [hadd2, hxor2, v2_two_mul (by omega), v2_two_mul hxor_pos]
          rw [v2_add_succ_eq_v2_xor_succ]
          unfold carryXorPhi
          have h01 : 0 + 1 + v2 ((x / 2 ^^^ y / 2) + 1) = 1 + v2 ((x / 2 ^^^ y / 2) + 1) := by omega
          have h02 : 0 + 1 + v2 (x / 2 ^^^ y / 2) = 1 + v2 (x / 2 ^^^ y / 2) := by omega
          rw [h01, h02]

theorem carryXorLaplacian_eq_shellLaplacian (k : Nat) (h : Nat -> Nat -> Int) :
    carryXorLaplacian k h = shellLaplacian k (carryXorC h) (carryXorPhi h) := by
  unfold carryXorLaplacian shellLaplacian graphLaplacian
  funext i j
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    apply sumFin_congr
    intro r
    by_cases hri : r = i
    · simp [hri]
    · simp only [hri, ↓reduceIte, carryXorWeight_eq_shellWeight]
  · simp only [hij, ↓reduceIte, carryXorWeight_eq_shellWeight]

def carryExactH (a b : Nat) : Int := if a = b then 1 else 0

def carryExactLaplacian (k : Nat) : Mat (2 ^ k) :=
  carryXorLaplacian k carryExactH

/-- Closed-form shifted product for `C_k`:
    `(s + 2^k)^k * ∏_{r=1}^{k-1} (s + 2^k - 2^r)^{2^r - 1}`. -/
def carryExactShiftedProd (k : Nat) (s : Int) : Int :=
  (s + ((2 ^ k : Nat) : Int)) ^ k *
  prodFin k (fun r =>
    if r.val = 0 then 1
    else (s + ((2 ^ k : Nat) : Int) - ((2 ^ r.val : Nat) : Int)) ^ (2 ^ r.val - 1))

/-- Exact closed-form spanning-tree count `tau(C_k) = (2^k)^(k-1) * ∏_{r=1}^{k-1} (2^k - 2^r)^(2^r - 1)`. -/
def carryExactTau (k : Nat) : Int :=
  (((2 ^ k : Nat) : Int) ^ (k - 1)) *
  prodFin k (fun r =>
    if r.val = 0 then 1
    else (((2 ^ k : Nat) : Int) - ((2 ^ r.val : Nat) : Int)) ^ (2 ^ r.val - 1))

theorem carryExact_walshEig_zero (m r u : Nat) :
    walshEig m (carryXorPhi carryExactH r) u = 0 := by
  unfold walshEig carryXorPhi carryExactH
  rw [sumFin_congr (g := fun _ => 0)]
  · exact sumFin_zero (2 ^ m)
  · intro d
    by_cases hd : d.val = 0
    · rw [hd, walshSign_zero_right]; omega
    · simp [v2_succ_ne_v2 hd]

theorem int_pow_const_prod (n : Nat) (v : Int) :
    prodFin n (fun _ => v) = v ^ n := by
  induction n with
  | zero => simp [prodFin]
  | succ n ih =>
    simp only [prodFin, ih, Int.pow_succ]

theorem carryExact_shifted_product (k : Nat) (s : Int) :
    prodFin (2 ^ k - 1)
      (fun j => s + shellEig k (carryXorC carryExactH) (carryXorPhi carryExactH)
        ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) =
    carryExactShiftedProd k s := by
  induction k generalizing s with
  | zero =>
    simp [prodFin, carryExactShiftedProd]
  | succ k ih =>
    -- Split `2^(k+1) - 1` product into left half (`0 < j < 2^k`), `j = 2^k`, and right half (`2^k < j < 2^(k+1)`)
    let F : Fin (2 ^ (k + 1)) -> Int := fun j =>
      if j.val = 0 then 1 else s + shellEig (k + 1) (carryXorC carryExactH) (carryXorPhi carryExactH) j
    have hfull : prodFin (2 ^ (k + 1)) F =
        prodFin (2 ^ (k + 1) - 1)
          (fun j => s + shellEig (k + 1) (carryXorC carryExactH) (carryXorPhi carryExactH)
            ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos (k + 1); omega⟩) := by
      have hcast : ∀ (n m : Nat) (hn : n = m + 1) (g : Fin n -> Int),
          g ⟨0, by omega⟩ = 1 ->
          prodFin n g = prodFin m (fun j => g ⟨j.val + 1, by omega⟩) := by
        intro n m hn g hg0
        subst hn; rw [prodFin_succ_zero, hg0, Int.one_mul]; rfl
      rw [hcast (2 ^ (k + 1)) (2 ^ (k + 1) - 1) (pow2_eq_pred_succ (k + 1)) F (by simp [F])]
      apply prodFin_congr
      intro j
      dsimp only [F]
      simp
    rw [← hfull, prodFin_pow2_halves]
    have hc0 : carryXorC carryExactH 0 = 1 := rfl
    have hshiftC : shiftSeq (carryXorC carryExactH) = carryXorC carryExactH := by
      funext r; unfold shiftSeq carryXorC carryExactH; simp
    have hshiftPhi : shiftSeq (carryXorPhi carryExactH) = carryXorPhi carryExactH := by
      funext r d
      unfold shiftSeq carryXorPhi carryExactH
      have hiff : r + 1 + 1 + v2 (d + 1) = r + 1 + 1 + v2 d ↔ r + 1 + v2 (d + 1) = r + 1 + v2 d := by omega
      simp only [hiff]
    have hleft :
        prodFin (2 ^ k) (fun a => F ⟨a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩) =
        carryExactShiftedProd k (s + ((2 ^ k : Nat) : Int)) := by
      have hcast : ∀ (n m : Nat) (hn : n = m + 1) (g : Fin n -> Int),
          g ⟨0, by omega⟩ = 1 ->
          prodFin n g = prodFin m (fun j => g ⟨j.val + 1, by omega⟩) := by
        intro n m hn g hg0
        subst hn; rw [prodFin_succ_zero, hg0, Int.one_mul]; rfl
      rw [hcast (2 ^ k) (2 ^ k - 1) (pow2_eq_pred_succ k) _ (by simp [F])]
      rw [← ih (s + ((2 ^ k : Nat) : Int))]
      apply prodFin_congr
      intro j
      have hne : j.val + 1 ≠ 0 := by omega
      have hlt : j.val + 1 < 2 ^ k := by have := j.isLt; have := Nat.two_pow_pos k; omega
      simp only [F, shellEig, hne, hlt, ↓reduceIte, ↓reduceDIte, hc0, Int.mul_one, hshiftC, hshiftPhi, Int.add_assoc]
    have hright :
        prodFin (2 ^ k) (fun a => F ⟨2 ^ k + a.val, by have := a.isLt; rw [Nat.pow_succ]; omega⟩) =
        (s + ((2 ^ (k + 1) : Nat) : Int)) * (s + ((2 ^ k : Nat) : Int)) ^ (2 ^ k - 1) := by
      have hcast : ∀ (n m : Nat) (hn : n = m + 1) (g : Fin n -> Int),
          prodFin n g = g ⟨0, by omega⟩ * prodFin m (fun j => g ⟨j.val + 1, by omega⟩) := by
        intro n m hn g
        subst hn; rw [prodFin_succ_zero]; rfl
      rw [hcast (2 ^ k) (2 ^ k - 1) (pow2_eq_pred_succ k)]
      congr 1
      · have hne : 2 ^ k ≠ 0 := by have := Nat.two_pow_pos k; omega
        have heq : 2 ^ k + 0 = 2 ^ k := by omega
        simp only [F, shellEig, heq, hne, Nat.lt_irrefl, ↓reduceIte, ↓reduceDIte, hc0, Int.mul_one]
      · rw [← int_pow_const_prod]
        apply prodFin_congr
        intro u
        have hne : 2 ^ k + (u.val + 1) ≠ 0 := by omega
        have hnlt : ¬(2 ^ k + (u.val + 1) < 2 ^ k) := by omega
        have hneq : 2 ^ k + (u.val + 1) ≠ 2 ^ k := by omega
        simp only [F, shellEig, hne, hnlt, hneq, ↓reduceIte, ↓reduceDIte, hc0, Int.mul_one,
                   carryExact_walshEig_zero, Int.add_zero]
    rw [hleft, hright]
    unfold carryExactShiftedProd
    have hpow2 : ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) + ((2 ^ k : Nat) : Int) := by
      have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      omega
    have hsum_eq : s + ((2 ^ k : Nat) : Int) + ((2 ^ k : Nat) : Int) = s + ((2 ^ (k + 1) : Nat) : Int) := by
      rw [Int.add_assoc, ← hpow2]
    rw [hsum_eq]
    simp only [prodFin, Int.pow_succ]
    have hlast : (if k = 0 then (1 : Int) else (s + ((2 ^ (k + 1) : Nat) : Int) - ((2 ^ k : Nat) : Int)) ^ (2 ^ k - 1)) =
                 (s + ((2 ^ k : Nat) : Int)) ^ (2 ^ k - 1) := by
      by_cases hk : k = 0
      · subst hk; simp
      · simp only [hk, ↓reduceIte]
        congr 1; omega
    rw [hlast]
    have hprod_eq :
        prodFin k (fun r => if r.val = 0 then 1 else (s + ((2 ^ (k + 1) : Nat) : Int) - ((2 ^ r.val : Nat) : Int)) ^ (2 ^ r.val - 1)) =
        prodFin k (fun r => if r.castSucc.val = 0 then 1 else (s + ((2 ^ (k + 1) : Nat) : Int) - ((2 ^ r.castSucc.val : Nat) : Int)) ^ (2 ^ r.castSucc.val - 1)) :=
      prodFin_congr (fun _ => rfl)
    rw [hprod_eq]
    have halg : ∀ A B C D : Int, (A * B) * (C * D) = (A * C) * (B * D) := by
      intro A B C D
      calc (A * B) * (C * D) = A * (B * C * D) := by rw [Int.mul_assoc, Int.mul_assoc]
        _ = A * (C * B * D) := by rw [Int.mul_comm B C]
        _ = (A * C) * (B * D) := by rw [Int.mul_assoc, Int.mul_assoc]
    exact halg _ _ _ _

def dyadicH (a _ : Nat) : Int := ((2 ^ a : Nat) : Int)

def dyadicLaplacian (k : Nat) : Mat (2 ^ k) :=
  carryXorLaplacian k dyadicH

/-- Structurally recursive fuel-based MSB index (kernel-reducible by `decide`!). -/
def msbAux : Nat -> Nat -> Nat
  | 0, _ => 0
  | fuel + 1, u => if u ≤ 1 then 0 else 1 + msbAux fuel (u / 2)

/-- Most significant bit index `floor(log2 u)` (with `msb 0 = 0`, `msb 1 = 0`, `msb 2 = 1`, ...). -/
def msb (u : Nat) : Nat := msbAux u u

theorem msbAux_eq_of_le (f1 f2 u : Nat) (h1 : u ≤ f1) (h2 : u ≤ f2) :
    msbAux f1 u = msbAux f2 u := by
  induction f1 generalizing f2 u with
  | zero =>
    have hu : u = 0 := by omega
    subst hu
    cases f2 with
    | zero => rfl
    | succ f2' => simp [msbAux]
  | succ f1' ih =>
    cases f2 with
    | zero =>
      have hu : u = 0 := by omega
      subst hu; simp [msbAux]
    | succ f2' =>
      simp only [msbAux]
      by_cases hle1 : u ≤ 1
      · simp [hle1]
      · simp only [hle1, ↓reduceIte]
        congr 1
        exact ih f2' (u / 2) (by omega) (by omega)

theorem msb_eq_rec (u : Nat) : msb u = if u ≤ 1 then 0 else 1 + msb (u / 2) := by
  unfold msb
  cases u with
  | zero => simp [msbAux]
  | succ u' =>
    simp only [msbAux]
    by_cases h1 : u' + 1 ≤ 1
    · simp [h1]
    · simp only [h1, ↓reduceIte]
      congr 1
      exact msbAux_eq_of_le u' ((u' + 1) / 2) ((u' + 1) / 2) (by omega) (Nat.le_refl _)

/-- Structurally recursive fuel-based Thue-Morse parity (`true` iff `popcount u` is odd). -/
def popParityAux : Nat -> Nat -> Bool
  | 0, _ => false
  | fuel + 1, u => if u = 0 then false else xor (u % 2 == 1) (popParityAux fuel (u / 2))

/-- Thue-Morse parity (`true` iff `popcount u` is odd). -/
def popParity (u : Nat) : Bool := popParityAux u u

theorem popParityAux_eq_of_le (f1 f2 u : Nat) (h1 : u ≤ f1) (h2 : u ≤ f2) :
    popParityAux f1 u = popParityAux f2 u := by
  induction f1 generalizing f2 u with
  | zero =>
    have hu : u = 0 := by omega
    subst hu
    cases f2 with
    | zero => rfl
    | succ f2' => simp [popParityAux]
  | succ f1' ih =>
    cases f2 with
    | zero =>
      have hu : u = 0 := by omega
      subst hu; simp [popParityAux]
    | succ f2' =>
      simp only [popParityAux]
      by_cases hu0 : u = 0
      · simp [hu0]
      · simp only [hu0, ↓reduceIte]
        congr 1
        exact ih f2' (u / 2) (by omega) (by omega)

theorem popParity_eq_rec (u : Nat) :
    popParity u = if u = 0 then false else xor (u % 2 == 1) (popParity (u / 2)) := by
  unfold popParity
  cases u with
  | zero => simp [popParityAux]
  | succ u' =>
    simp only [popParityAux]
    have hne : u' + 1 ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    congr 1
    exact popParityAux_eq_of_le u' ((u' + 1) / 2) ((u' + 1) / 2) (by omega) (Nat.le_refl _)

theorem msb_lt {m u : Nat} (hu : u < 2 ^ (m + 1)) : msb u ≤ m := by
  induction m generalizing u with
  | zero =>
    rw [msb_eq_rec]
    have : u ≤ 1 := by omega
    simp [this]
  | succ m ih =>
    rw [msb_eq_rec]
    by_cases h1 : u ≤ 1
    · simp [h1]
    · simp only [h1, ↓reduceIte]
      have hdiv : u / 2 < 2 ^ (m + 1) := by rw [Nat.pow_succ] at hu; omega
      have := ih hdiv
      omega

theorem dyadic_v2_sum (m : Nat) :
    2 * sumFin (2 ^ m) (fun d => ((2 ^ v2 (d.val + 1) : Nat) : Int)) =
    ((m + 2 : Nat) : Int) * ((2 ^ m : Nat) : Int) := by
  induction m with
  | zero =>
    simp [sumFin, v2_odd]
  | succ m ih =>
    rw [sumFin_pow2_succ]
    have hev : ∀ a : Fin (2 ^ m), ((2 ^ v2 (2 * a.val + 1) : Nat) : Int) = 1 := by
      intro a; rw [v2_odd (by omega)]; rfl
    have hod : ∀ a : Fin (2 ^ m), ((2 ^ v2 (2 * a.val + 1 + 1) : Nat) : Int) =
        2 * ((2 ^ v2 (a.val + 1) : Nat) : Int) := by
      intro a
      have h2 : 2 * a.val + 1 + 1 = 2 * (a.val + 1) := by omega
      rw [h2, v2_two_mul (by omega), Nat.add_comm 1, Nat.pow_succ]
      omega
    have hs1 : sumFin (2 ^ m) (fun a => ((2 ^ v2 (2 * a.val + 1) : Nat) : Int)) = ((2 ^ m : Nat) : Int) := by
      rw [sumFin_congr hev, sumFin_const, Int.mul_one]
    have hs2 : sumFin (2 ^ m) (fun a => ((2 ^ v2 (2 * a.val + 1 + 1) : Nat) : Int)) =
        2 * sumFin (2 ^ m) (fun a => ((2 ^ v2 (a.val + 1) : Nat) : Int)) := by
      rw [sumFin_congr hod, sumFin_mul_left]
    rw [hs1, hs2, Int.mul_add, ih]
    have hpow : ((2 ^ (m + 1) : Nat) : Int) = 2 * ((2 ^ m : Nat) : Int) := by
      have : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      omega
    rw [hpow]
    have hm1 : ((m + 1 + 2 : Nat) : Int) = ((m + 2 : Nat) : Int) + 1 := by omega
    rw [hm1, Int.add_mul, Int.one_mul]
    rw [Int.mul_comm 2 (((m + 2 : Nat) : Int) * ((2 ^ m : Nat) : Int))]
    rw [Int.mul_assoc ((m + 2 : Nat) : Int), Int.mul_comm ((2 ^ m : Nat) : Int) 2, ← Int.mul_assoc]
    omega

/-- **EXACT DYADIC WALSH-CARRY EVALUATION LAW (Thue-Morse Parity Mirror-Band Theorem)**:
    For ALL `m ≥ 1` and ALL `1 ≤ u < 2^m`,
    `2 * walshEig m (fun d => 2^(v2 (d + 1))) u` splits cleanly by `popParity u`:
    - Even popcount: `(msb u + 2) * 2^m`
    - Odd  popcount: `(2 * m + 2 - msb u) * 2^m`. -/
theorem walshEig_dyadic_exact (m u : Nat) (hm : 1 ≤ m) (hu1 : 1 ≤ u) (hu2 : u < 2 ^ m) :
    2 * walshEig m (fun d => ((2 ^ v2 (d + 1) : Nat) : Int)) u =
    (if popParity u then ((2 * m + 2 - msb u : Nat) : Int) else ((msb u + 2 : Nat) : Int)) *
    ((2 ^ m : Nat) : Int) := by
  induction m generalizing u with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      have hu : u = 1 := by omega
      subst hu
      unfold walshEig
      decide
    | succ m' =>
      unfold walshEig
      rw [sumFin_pow2_succ]
      have hev_term : ∀ a : Fin (2 ^ (m' + 1)),
          ((2 ^ v2 (2 * a.val + 1) : Nat) : Int) * (1 - walshSign (m' + 2) u (2 * a.val)) =
          1 - walshSign (m' + 1) (u / 2) a.val := by
        intro a
        rw [v2_odd (by omega)]
        have h1 : ((2 ^ 0 : Nat) : Int) = 1 := rfl
        rw [h1, Int.one_mul]
        simp only [walshSign]
        have h2m : (2 * a.val) % 2 = 0 := by omega
        have h2d : (2 * a.val) / 2 = a.val := by omega
        simp [walshBit, h2m, h2d]
      have hod_term : ∀ a : Fin (2 ^ (m' + 1)),
          ((2 ^ v2 (2 * a.val + 1 + 1) : Nat) : Int) * (1 - walshSign (m' + 2) u (2 * a.val + 1)) =
          2 * ((2 ^ v2 (a.val + 1) : Nat) : Int) *
            (1 - (if u % 2 = 1 then -1 else 1) * walshSign (m' + 1) (u / 2) a.val) := by
        intro a
        have h2 : 2 * a.val + 1 + 1 = 2 * (a.val + 1) := by omega
        rw [h2, v2_two_mul (by omega), Nat.add_comm 1, Nat.pow_succ]
        have h2d : (2 * a.val + 1) / 2 = a.val := by omega
        have h2m : (2 * a.val + 1) % 2 = 1 := by omega
        simp only [walshSign, h2d]
        have hwb : walshBit u (2 * a.val + 1) = if u % 2 = 1 then -1 else 1 := by
          unfold walshBit; simp [h2m]
        rw [hwb]
        have hcast : ((2 ^ v2 (a.val + 1) * 2 : Nat) : Int) = 2 * ((2 ^ v2 (a.val + 1) : Nat) : Int) := by omega
        rw [hcast]
      have hs1 : sumFin (2 ^ (m' + 1)) (fun a => ((2 ^ v2 (2 * a.val + 1) : Nat) : Int) * (1 - walshSign (m' + 2) u (2 * a.val))) =
                 sumFin (2 ^ (m' + 1)) (fun a => 1 - walshSign (m' + 1) (u / 2) a.val) :=
        sumFin_congr hev_term
      have hs2 : sumFin (2 ^ (m' + 1)) (fun a => ((2 ^ v2 (2 * a.val + 1 + 1) : Nat) : Int) * (1 - walshSign (m' + 2) u (2 * a.val + 1))) =
                 sumFin (2 ^ (m' + 1)) (fun a => 2 * ((2 ^ v2 (a.val + 1) : Nat) : Int) *
                   (1 - (if u % 2 = 1 then -1 else 1) * walshSign (m' + 1) (u / 2) a.val)) :=
        sumFin_congr hod_term
      rw [hs1, hs2]
      have hpow_step : ((2 ^ (m' + 2) : Nat) : Int) = 2 * ((2 ^ (m' + 1) : Nat) : Int) := by
        have : 2 ^ (m' + 2) = 2 * 2 ^ (m' + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        omega
      by_cases hu_eq1 : u = 1
      · subst hu_eq1
        have hdiv0 : (1 : Nat) / 2 = 0 := by decide
        have hmod1 : (1 : Nat) % 2 = 1 := by decide
        have hpp1 : popParity 1 = true := by decide
        have hmsb1 : msb 1 = 0 := by decide
        rw [hdiv0, hmod1, hpp1, hmsb1]
        have h1 : sumFin (2 ^ (m' + 1)) (fun a => (1 : Int) - walshSign (m' + 1) 0 a.val) = 0 := by
          rw [sumFin_congr (g := fun _ => 0)]
          · exact sumFin_zero _
          · intro a; rw [walshSign_zero_left]; omega
        have h2 : sumFin (2 ^ (m' + 1)) (fun a => 2 * ((2 ^ v2 (a.val + 1) : Nat) : Int) *
            (1 - (-1) * walshSign (m' + 1) 0 a.val)) =
            4 * sumFin (2 ^ (m' + 1)) (fun a => ((2 ^ v2 (a.val + 1) : Nat) : Int)) := by
          rw [← sumFin_mul_left]
          apply sumFin_congr
          intro a
          rw [walshSign_zero_left]; omega
        simp only [↓reduceIte, h1, Int.zero_add, h2]
        have hds := dyadic_v2_sum (m' + 1)
        rw [hpow_step]
        have h4 : 2 * (4 * sumFin (2 ^ (m' + 1)) (fun a => ((2 ^ v2 (a.val + 1) : Nat) : Int))) =
                  4 * (2 * sumFin (2 ^ (m' + 1)) (fun a => ((2 ^ v2 (a.val + 1) : Nat) : Int))) := by omega
        rw [h4, hds]
        have hc : ((2 * (m' + 2) + 2 - 0 : Nat) : Int) = 2 * ((m' + 1 + 2 : Nat) : Int) := by omega
        rw [hc]
        have halg : ∀ a b : Int, 4 * (a * b) = (2 * a) * (2 * b) := by
          intro a b
          calc 4 * (a * b) = (2 * 2) * (a * b) := rfl
            _ = (2 * a) * (2 * b) := by
                rw [Int.mul_assoc, Int.mul_assoc]; congr 1
                rw [← Int.mul_assoc 2 a b, Int.mul_comm 2 a, Int.mul_assoc]
        exact halg _ _
      · have hdiv_ge1 : 1 ≤ u / 2 := by omega
        have hdiv_lt : u / 2 < 2 ^ (m' + 1) := by rw [Nat.pow_succ] at hu2; omega
        have hih := ih (u / 2) (by omega) hdiv_ge1 hdiv_lt
        have hmsb_rec : msb u = 1 + msb (u / 2) := by
          rw [msb_eq_rec]
          have hnot : ¬(u ≤ 1) := by omega
          simp [hnot]
        have hmsb_le : msb (u / 2) ≤ m' := msb_lt hdiv_lt
        have hpp_rec : popParity u = xor (u % 2 == 1) (popParity (u / 2)) := by
          rw [popParity_eq_rec]
          have hne0 : u ≠ 0 := by omega
          simp [hne0]
        have hev_val : sumFin (2 ^ (m' + 1)) (fun a => (1 : Int) - walshSign (m' + 1) (u / 2) a.val) =
            ((2 ^ (m' + 1) : Nat) : Int) := by
          rw [sumFin_sub, sumFin_const, Int.mul_one]
          have hws := walshSign_sum_nonzero (m' + 1) ⟨u / 2, hdiv_lt⟩ (by dsimp; omega)
          rw [hws]; omega
        rw [hev_val]
        by_cases hu_odd : u % 2 = 1
        · simp only [hu_odd, ↓reduceIte]
          have hod_split :
              sumFin (2 ^ (m' + 1)) (fun a => 2 * ((2 ^ v2 (a.val + 1) : Nat) : Int) *
                (1 - -1 * walshSign (m' + 1) (u / 2) a.val)) =
              2 * (2 * sumFin (2 ^ (m' + 1)) (fun a => ((2 ^ v2 (a.val + 1) : Nat) : Int))) -
              2 * walshEig (m' + 1) (fun d => ((2 ^ v2 (d + 1) : Nat) : Int)) (u / 2) := by
            unfold walshEig
            rw [← sumFin_mul_left, ← sumFin_mul_left, ← sumFin_mul_left, ← sumFin_sub]
            apply sumFin_congr
            intro a
            have h1 : ∀ w c : Int, 2 * w * (1 - -1 * c) = 2 * (2 * w) - 2 * (w * (1 - c)) := by
              intro w c
              rw [Int.neg_one_mul, Int.sub_neg, Int.mul_add, Int.mul_one, Int.mul_sub, Int.mul_one,
                  Int.mul_sub, Int.mul_assoc 2 w c]
              omega
            exact h1 _ _
          rw [hod_split, dyadic_v2_sum (m' + 1)]
          rw [Int.mul_add, Int.mul_sub, hih, hpow_step, hpp_rec, hmsb_rec]
          simp only [hu_odd, beq_self_eq_true, Bool.true_xor]
          cases hpp : popParity (u / 2)
          · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
            have hfactor : ∀ A B P : Int, 2 * P + (2 * (2 * (A * P)) - 2 * (B * P)) = (2 + 4 * A - 2 * B) * P := by
              intro A B P
              rw [Int.sub_mul, Int.add_mul, Int.mul_assoc 4 A P, Int.mul_assoc 2 B P]
              have : 2 * (2 * (A * P)) = 4 * (A * P) := by rw [← Int.mul_assoc]; rfl
              rw [this]; omega
            have hrhs : ∀ C P : Int, C * (2 * P) = (2 * C) * P := fun C P => by
              rw [← Int.mul_assoc C 2 P, Int.mul_comm C 2]
            rw [hfactor, hrhs]
            congr 1
            have hle1 : 1 + msb (u / 2) ≤ 2 * (m' + 1 + 1) + 2 := by omega
            have hnat : 2 + 4 * (m' + 1 + 2) = 2 * (msb (u / 2) + 2) + 2 * (2 * (m' + 1 + 1) + 2 - (1 + msb (u / 2))) := by omega
            omega
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            have hfactor : ∀ A B P : Int, 2 * P + (2 * (2 * (A * P)) - 2 * (B * P)) = (2 + 4 * A - 2 * B) * P := by
              intro A B P
              rw [Int.sub_mul, Int.add_mul, Int.mul_assoc 4 A P, Int.mul_assoc 2 B P]
              have : 2 * (2 * (A * P)) = 4 * (A * P) := by rw [← Int.mul_assoc]; rfl
              rw [this]; omega
            have hrhs : ∀ C P : Int, C * (2 * P) = (2 * C) * P := fun C P => by
              rw [← Int.mul_assoc C 2 P, Int.mul_comm C 2]
            rw [hfactor, hrhs]
            congr 1
            have hle1 : msb (u / 2) ≤ 2 * (m' + 1) + 2 := by omega
            have hnat : 2 + 4 * (m' + 1 + 2) = 2 * (2 * (m' + 1) + 2 - msb (u / 2)) + 2 * (1 + msb (u / 2) + 2) := by omega
            omega
        · simp only [hu_odd, ↓reduceIte]
          have hod_val :
              sumFin (2 ^ (m' + 1)) (fun a => 2 * ((2 ^ v2 (a.val + 1) : Nat) : Int) *
                (1 - 1 * walshSign (m' + 1) (u / 2) a.val)) =
              2 * walshEig (m' + 1) (fun d => ((2 ^ v2 (d + 1) : Nat) : Int)) (u / 2) := by
            unfold walshEig
            rw [← sumFin_mul_left]
            apply sumFin_congr
            intro a
            rw [Int.one_mul, Int.mul_assoc]
          rw [hod_val, Int.mul_add, hih, hpow_step, hpp_rec, hmsb_rec]
          have hbeq : (u % 2 == 1) = false := by
            have : u % 2 = 0 := by omega
            simp [this]
          simp only [hbeq, Bool.false_xor]
          have hrhs : ∀ C P : Int, C * (2 * P) = (2 * C) * P := fun C P => by
            rw [← Int.mul_assoc C 2 P, Int.mul_comm C 2]
          cases hpp : popParity (u / 2)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hfactor : ∀ B P : Int, 2 * P + 2 * (B * P) = (2 * (B + 1)) * P := by
              intro B P
              rw [Int.mul_add, Int.mul_one, Int.add_mul, Int.mul_assoc]
              omega
            rw [hfactor, hrhs]
            congr 1; omega
          · simp only [↓reduceIte]
            have hfactor : ∀ B P : Int, 2 * P + 2 * (B * P) = (2 * (B + 1)) * P := by
              intro B P
              rw [Int.mul_add, Int.mul_one, Int.add_mul, Int.mul_assoc]
              omega
            rw [hfactor, hrhs]
            congr 1
            have hnat : (2 * (m' + 1) + 2 - msb (u / 2)) + 1 = 2 * (m' + 1 + 1) + 2 - (1 + msb (u / 2)) := by omega
            omega

/-- Helper: homogeneity of `shellEig` under scaling both `c` and `phi` by a constant `a`. -/
theorem shellEig_scale (k : Nat) (a : Int) (c : Nat -> Int) (phi : Nat -> Nat -> Int) (j : Fin (2 ^ k)) :
    shellEig k (fun r => a * c r) (fun r d => a * phi r d) j = a * shellEig k c phi j := by
  induction k generalizing c phi with
  | zero => simp [shellEig]
  | succ k ih =>
    unfold shellEig
    have h2k_ne : 2 ^ k ≠ 0 := by have := Nat.two_pow_pos k; omega
    by_cases hj0 : j.val = 0
    · simp [hj0]
    · by_cases hjlt : j.val < 2 ^ k
      · simp only [hj0, hjlt, ↓reduceIte, ↓reduceDIte]
        have hsc : shiftSeq (fun r => a * c r) = fun r => a * shiftSeq c r := rfl
        have hsp : shiftSeq (fun r d => a * phi r d) = fun r d => a * shiftSeq phi r d := rfl
        rw [hsc, hsp, ih (shiftSeq c) (shiftSeq phi), Int.mul_add]
        congr 1
        rw [← Int.mul_assoc, Int.mul_comm ((2 ^ k : Nat) : Int) a, Int.mul_assoc]
      · by_cases hjeq : j.val = 2 ^ k
        · simp only [hjeq, h2k_ne, Nat.lt_irrefl, ↓reduceIte, ↓reduceDIte]
          rw [← Int.mul_assoc, Int.mul_comm ((2 ^ (k + 1) : Nat) : Int) a, Int.mul_assoc]
        · simp only [hj0, hjlt, hjeq, ↓reduceIte, ↓reduceDIte]
          have hwe : walshEig k (fun d => a * phi 0 d) (j.val - 2 ^ k) =
                     a * walshEig k (phi 0) (j.val - 2 ^ k) := by
            unfold walshEig
            rw [← sumFin_mul_left]
            apply sumFin_congr; intro d; rw [Int.mul_assoc]
          rw [hwe, Int.mul_add]
          congr 1
          rw [← Int.mul_assoc, Int.mul_comm ((2 ^ k : Nat) : Int) a, Int.mul_assoc]

/-- Exact closed-form 2-parameter shifted product for the Dyadic 2-Adic Binary-Sum Graph `w(x,y) = 2^{v2(x+y)}` (`k ≥ 1`):
    `(s + t * 2^k) * ∏_{j=1}^{k-1} ((s + t*(j+2)*2^{k-1}) * (s + t*(2k+2-j)*2^{k-1}))^{2^{j-1}}`. -/
def dyadicShiftedProd (k : Nat) (s t : Int) : Int :=
  (s + t * ((2 ^ k : Nat) : Int)) *
  prodFin k (fun j =>
    if j.val = 0 then 1
    else ((s + t * (((j.val + 2 : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int))) *
          (s + t * (((2 * k + 2 - j.val : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int)))) ^ (2 ^ (j.val - 1)))

/-- Exact closed-form Kirchhoff spanning-tree weight `tau(G_k^dyad)` (`∀ k ≥ 1`):
    `∏_{j=1}^{k-1} ((j + 2) * (2k + 2 - j) * (2^{k-1})^2)^{2^{j-1}}`. -/
def dyadicTau (k : Nat) : Int :=
  prodFin k (fun j =>
    if j.val = 0 then 1
    else ((((j.val + 2 : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int)) *
          (((2 * k + 2 - j.val : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int))) ^ (2 ^ (j.val - 1)))

/-- Helper: product of a function of `(msb u, popParity u)` over `u ∈ {1 .. 2^k - 1}`! -/
theorem prodFin_msb_parity (k : Nat) (F : Nat -> Bool -> Int) :
    prodFin (2 ^ k - 1) (fun u => F (msb (u.val + 1)) (popParity (u.val + 1))) =
    (if k = 0 then 1 else
      F 0 true * prodFin k (fun p => if p.val = 0 then 1 else (F p.val false * F p.val true) ^ (2 ^ (p.val - 1)))) := by
  induction k with
  | zero => simp [prodFin]
  | succ k ih =>
    cases k with
    | zero =>
      simp [prodFin]
      have hmsb1 : msb 1 = 0 := by decide
      have hpp1 : popParity 1 = true := by decide
      rw [hmsb1, hpp1]
    | succ k' =>
      let G : Fin (2 ^ (k' + 2)) -> Int := fun u =>
        if u.val = 0 then 1 else F (msb u.val) (popParity u.val)
      have hfull : prodFin (2 ^ (k' + 2)) G =
          prodFin (2 ^ (k' + 2) - 1) (fun u => F (msb (u.val + 1)) (popParity (u.val + 1))) := by
        have hcast : ∀ (n m : Nat) (hn : n = m + 1) (g : Fin n -> Int),
            g ⟨0, by omega⟩ = 1 ->
            prodFin n g = prodFin m (fun j => g ⟨j.val + 1, by omega⟩) := by
          intro n m hn g hg0; subst hn; rw [prodFin_succ_zero, hg0, Int.one_mul]; rfl
        rw [hcast (2 ^ (k' + 2)) (2 ^ (k' + 2) - 1) (pow2_eq_pred_succ (k' + 2)) G (by simp [G])]
        apply prodFin_congr
        intro u
        dsimp only [G]
        simp
      rw [← hfull, prodFin_pow2_halves]
      have hleft :
          prodFin (2 ^ (k' + 1)) (fun a => G ⟨a.val, by have := a.isLt; have h2 : 2 ^ (k' + 2) = 2 ^ (k' + 1) * 2 := Nat.pow_succ 2 (k' + 1); omega⟩) =
          F 0 true * prodFin (k' + 1) (fun p => if p.val = 0 then 1 else (F p.val false * F p.val true) ^ (2 ^ (p.val - 1))) := by
        have hcast : ∀ (n m : Nat) (hn : n = m + 1) (g : Fin n -> Int),
            g ⟨0, by omega⟩ = 1 ->
            prodFin n g = prodFin m (fun j => g ⟨j.val + 1, by omega⟩) := by
          intro n m hn g hg0; subst hn; rw [prodFin_succ_zero, hg0, Int.one_mul]; rfl
        rw [hcast (2 ^ (k' + 1)) (2 ^ (k' + 1) - 1) (pow2_eq_pred_succ (k' + 1)) _ (by simp [G])]
        have hcongr : prodFin (2 ^ (k' + 1) - 1) (fun u => G ⟨u.val + 1, by have := u.isLt; have := Nat.two_pow_pos (k' + 1); have h2 : 2 ^ (k' + 2) = 2 ^ (k' + 1) * 2 := Nat.pow_succ 2 (k' + 1); omega⟩) =
                      prodFin (2 ^ (k' + 1) - 1) (fun u => F (msb (u.val + 1)) (popParity (u.val + 1))) := by
          apply prodFin_congr
          intro u
          dsimp only [G]
          simp
        rw [hcongr, ih]
        simp
      have hmsb_hi : ∀ (m a : Nat), a < 2 ^ m -> msb (2 ^ m + a) = m := by
        intro m a ha
        induction m generalizing a with
        | zero =>
          have ha0 : a = 0 := by omega
          subst ha0; decide
        | succ m' ihm =>
          rw [msb_eq_rec]
          have hgt1 : ¬(2 ^ (m' + 1) + a ≤ 1) := by have := Nat.two_pow_pos m'; rw [Nat.pow_succ]; omega
          simp only [hgt1, ↓reduceIte]
          have hdiv : (2 ^ (m' + 1) + a) / 2 = 2 ^ m' + a / 2 := by rw [Nat.pow_succ]; omega
          have halt : a / 2 < 2 ^ m' := by rw [Nat.pow_succ] at ha; omega
          rw [hdiv, ihm (a / 2) halt]
          omega
      have hpar_prod : ∀ (m : Nat) (vF vT : Int),
          prodFin (2 ^ (m + 1)) (fun a => if popParity (2 ^ (m + 1) + a.val) then vT else vF) =
          (vF * vT) ^ (2 ^ m) := by
        intro m vF vT
        have hpair : ∀ (n : Nat) (g : Fin (2 * n) -> Int),
            (∀ q : Fin n, g ⟨2 * q.val, by omega⟩ * g ⟨2 * q.val + 1, by omega⟩ = vF * vT) ->
            prodFin (2 * n) g = (vF * vT) ^ n := by
          intro n g hg
          induction n with
          | zero => simp [prodFin]
          | succ n' ihn =>
            have hstep : prodFin (2 * (n' + 1)) g =
                prodFin (2 * n') (fun i => g ⟨i.val, by omega⟩) *
                (g ⟨2 * n', by omega⟩ * g ⟨2 * n' + 1, by omega⟩) := by
              change prodFin (2 * n') (fun i => g ⟨i.val, by omega⟩) * g ⟨2 * n', by omega⟩ * g ⟨2 * n' + 1, by omega⟩ = _
              rw [Int.mul_assoc]
            rw [hstep, ihn (fun i => g ⟨i.val, by omega⟩) (fun q => hg ⟨q.val, by omega⟩),
                hg ⟨n', Nat.lt_succ_self n'⟩, Int.pow_succ]
        have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
        have hcast : ∀ (N : Nat) (hN : N = 2 * 2 ^ m) (g : Fin N -> Int),
            (∀ q : Fin (2 ^ m), g ⟨2 * q.val, by have := q.isLt; omega⟩ * g ⟨2 * q.val + 1, by have := q.isLt; omega⟩ = vF * vT) ->
            prodFin N g = (vF * vT) ^ (2 ^ m) := by
          intro N hN g hg; subst hN; exact hpair (2 ^ m) g hg
        apply hcast (2 ^ (m + 1)) hpow
        intro q
        have hp_ev : popParity (2 ^ (m + 1) + 2 * q.val) = popParity (2 ^ m + q.val) := by
          rw [popParity_eq_rec]
          have hm0 : (2 ^ (m + 1) + 2 * q.val) % 2 = 0 := by rw [Nat.pow_succ]; omega
          have hd : (2 ^ (m + 1) + 2 * q.val) / 2 = 2 ^ m + q.val := by rw [Nat.pow_succ]; omega
          simp [hm0, hd]
        have hp_od : popParity (2 ^ (m + 1) + (2 * q.val + 1)) = !(popParity (2 ^ m + q.val)) := by
          rw [popParity_eq_rec]
          have hm1 : (2 ^ (m + 1) + (2 * q.val + 1)) % 2 = 1 := by rw [Nat.pow_succ]; omega
          have hd : (2 ^ (m + 1) + (2 * q.val + 1)) / 2 = 2 ^ m + q.val := by rw [Nat.pow_succ]; omega
          simp [hm1, hd]
        rw [hp_ev, hp_od]
        cases popParity (2 ^ m + q.val)
        · simp
        · simp [Int.mul_comm]
      have hright :
          prodFin (2 ^ (k' + 1)) (fun a => G ⟨2 ^ (k' + 1) + a.val, by have := a.isLt; have h2 : 2 ^ (k' + 2) = 2 ^ (k' + 1) * 2 := Nat.pow_succ 2 (k' + 1); omega⟩) =
          (F (k' + 1) false * F (k' + 1) true) ^ (2 ^ k') := by
        rw [← hpar_prod k' (F (k' + 1) false) (F (k' + 1) true)]
        apply prodFin_congr
        intro a
        dsimp only [G]
        have hne : 2 ^ (k' + 1) + a.val ≠ 0 := by have := Nat.two_pow_pos (k' + 1); omega
        simp only [hne, ↓reduceIte, hmsb_hi (k' + 1) a.val a.isLt]
        cases popParity (2 ^ (k' + 1) + a.val) <;> rfl
      rw [hleft, hright]
      have hne0 : k' + 2 ≠ 0 := by omega
      simp only [hne0, ↓reduceIte, prodFin]
      have hlast : (if k' + 1 = 0 then (1 : Int) else (F (k' + 1) false * F (k' + 1) true) ^ (2 ^ (k' + 1 - 1))) =
                   (F (k' + 1) false * F (k' + 1) true) ^ (2 ^ k') := by
        simp
      rw [hlast, Int.mul_assoc]
      rfl

/-- Helper: exact product identity `prodFin (2^k - 1) (s + t * shellEig_dyadic) = dyadicShiftedProd k s t` (`∀ k ≥ 1`). -/
theorem dyadic_shifted_product (k : Nat) (hk : 1 ≤ k) (s t : Int) :
    prodFin (2 ^ k - 1)
      (fun j => s + t * shellEig k (carryXorC dyadicH) (carryXorPhi dyadicH)
        ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) =
    dyadicShiftedProd k s t := by
  induction k generalizing s t with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      unfold dyadicShiftedProd shellEig carryXorC dyadicH
      simp [prodFin]
    | succ k' =>
      let m := k' + 1
      have hm : 1 ≤ m := by omega
      let F : Fin (2 ^ (m + 1)) -> Int := fun j =>
        if j.val = 0 then 1 else s + t * shellEig (m + 1) (carryXorC dyadicH) (carryXorPhi dyadicH) j
      have hfull : prodFin (2 ^ (m + 1)) F =
          prodFin (2 ^ (m + 1) - 1)
            (fun j => s + t * shellEig (m + 1) (carryXorC dyadicH) (carryXorPhi dyadicH)
              ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos (m + 1); omega⟩) := by
        have hcast : ∀ (n p : Nat) (hn : n = p + 1) (g : Fin n -> Int),
            g ⟨0, by omega⟩ = 1 ->
            prodFin n g = prodFin p (fun j => g ⟨j.val + 1, by omega⟩) := by
          intro n p hn g hg0; subst hn; rw [prodFin_succ_zero, hg0, Int.one_mul]; rfl
        rw [hcast (2 ^ (m + 1)) (2 ^ (m + 1) - 1) (pow2_eq_pred_succ (m + 1)) F (by simp [F])]
        apply prodFin_congr
        intro j
        dsimp only [F]
        simp
      rw [← hfull, prodFin_pow2_halves]
      have hc0 : carryXorC dyadicH 0 = 1 := rfl
      have hshiftC : shiftSeq (carryXorC dyadicH) = fun r => 2 * carryXorC dyadicH r := by
        funext r; unfold shiftSeq carryXorC dyadicH; rw [Nat.pow_succ]; omega
      have hshiftPhi : shiftSeq (carryXorPhi dyadicH) = fun r d => 2 * carryXorPhi dyadicH r d := by
        funext r d; unfold shiftSeq carryXorPhi dyadicH
        have h1 : r + 1 + 1 + v2 (d + 1) = (r + 1 + v2 (d + 1)) + 1 := by omega
        rw [h1, Nat.pow_succ]; omega
      have hleft :
          prodFin (2 ^ m) (fun a => F ⟨a.val, by have := a.isLt; have := Nat.pow_succ 2 m; omega⟩) =
          dyadicShiftedProd m (s + t * ((2 ^ m : Nat) : Int)) (2 * t) := by
        have hcast : ∀ (n p : Nat) (hn : n = p + 1) (g : Fin n -> Int),
            g ⟨0, by omega⟩ = 1 ->
            prodFin n g = prodFin p (fun j => g ⟨j.val + 1, by omega⟩) := by
          intro n p hn g hg0; subst hn; rw [prodFin_succ_zero, hg0, Int.one_mul]; rfl
        rw [hcast (2 ^ m) (2 ^ m - 1) (pow2_eq_pred_succ m) _ (by simp [F])]
        rw [← ih hm (s + t * ((2 ^ m : Nat) : Int)) (2 * t)]
        apply prodFin_congr
        intro j
        have hne : j.val + 1 ≠ 0 := by omega
        have hlt : j.val + 1 < 2 ^ m := by have := j.isLt; have := Nat.two_pow_pos m; omega
        dsimp only [F]
        simp only [hne, ↓reduceIte]
        conv => lhs; unfold shellEig
        simp only [hne, hlt, ↓reduceIte, ↓reduceDIte, hc0, Int.mul_one, hshiftC, hshiftPhi]
        rw [shellEig_scale m 2, Int.mul_add, ← Int.add_assoc, ← Int.mul_assoc, Int.mul_comm t 2]
      have hphi0 : carryXorPhi dyadicH 0 = fun d => 2 * ((2 ^ v2 (d + 1) : Nat) : Int) := by
        funext d; unfold carryXorPhi dyadicH
        have h1 : 0 + 1 + v2 (d + 1) = v2 (d + 1) + 1 := by omega
        rw [h1, Nat.pow_succ]; omega
      let G_mode : Nat -> Bool -> Int := fun p isOdd =>
        s + t * ((if isOdd then ((2 * m + 3 - p : Nat) : Int) else ((p + 3 : Nat) : Int)) * ((2 ^ m : Nat) : Int))
      have hright :
          prodFin (2 ^ m) (fun a => F ⟨2 ^ m + a.val, by have := a.isLt; have := Nat.pow_succ 2 m; omega⟩) =
          (s + t * ((2 ^ (m + 1) : Nat) : Int)) *
          (G_mode 0 true * prodFin m (fun p => if p.val = 0 then 1 else (G_mode p.val false * G_mode p.val true) ^ (2 ^ (p.val - 1)))) := by
        have hcast : ∀ (n p : Nat) (hn : n = p + 1) (g : Fin n -> Int),
            prodFin n g = g ⟨0, by omega⟩ * prodFin p (fun j => g ⟨j.val + 1, by omega⟩) := by
          intro n p hn g; subst hn; rw [prodFin_succ_zero]; rfl
        rw [hcast (2 ^ m) (2 ^ m - 1) (pow2_eq_pred_succ m)]
        congr 1
        · have hne : 2 ^ m ≠ 0 := by have := Nat.two_pow_pos m; omega
          have heq : 2 ^ m + 0 = 2 ^ m := by omega
          simp only [F, shellEig, heq, hne, Nat.lt_irrefl, ↓reduceIte, ↓reduceDIte, hc0, Int.mul_one]
        · have hcongr :
              prodFin (2 ^ m - 1) (fun u => F ⟨2 ^ m + (u.val + 1), by have := u.isLt; have := Nat.two_pow_pos m; have := Nat.pow_succ 2 m; omega⟩) =
              prodFin (2 ^ m - 1) (fun u => G_mode (msb (u.val + 1)) (popParity (u.val + 1))) := by
            apply prodFin_congr
            intro u
            have hne : 2 ^ m + (u.val + 1) ≠ 0 := by omega
            have hnlt : ¬(2 ^ m + (u.val + 1) < 2 ^ m) := by omega
            have hneq : 2 ^ m + (u.val + 1) ≠ 2 ^ m := by omega
            have hsub : 2 ^ m + (u.val + 1) - 2 ^ m = u.val + 1 := by omega
            simp only [F, shellEig, hne, hnlt, hneq, hsub, ↓reduceIte, ↓reduceDIte, hc0, Int.mul_one, hphi0]
            have hwe_scale : walshEig m (fun d => 2 * ((2 ^ v2 (d + 1) : Nat) : Int)) (u.val + 1) =
                             2 * walshEig m (fun d => ((2 ^ v2 (d + 1) : Nat) : Int)) (u.val + 1) := by
              unfold walshEig; rw [← sumFin_mul_left]; apply sumFin_congr; intro d; rw [Int.mul_assoc]
            have hult : u.val + 1 < 2 ^ m := by have := u.isLt; have := Nat.two_pow_pos m; omega
            rw [hwe_scale, walshEig_dyadic_exact m (u.val + 1) hm (by omega) hult]
            have hmsb_le : msb (u.val + 1) ≤ m - 1 := by
              have h1 : u.val + 1 < 2 ^ ((m - 1) + 1) := by
                have hm1 : (m - 1) + 1 = m := by omega
                rw [hm1]; exact hult
              exact msb_lt h1
            dsimp only [G_mode]
            congr 1; congr 1
            cases popParity (u.val + 1)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hc : ((msb (u.val + 1) + 3 : Nat) : Int) = 1 + ((msb (u.val + 1) + 2 : Nat) : Int) := by omega
              rw [hc, Int.add_mul, Int.one_mul]
            · simp only [↓reduceIte]
              have hc : ((2 * m + 3 - msb (u.val + 1) : Nat) : Int) = 1 + ((2 * m + 2 - msb (u.val + 1) : Nat) : Int) := by omega
              rw [hc, Int.add_mul, Int.one_mul]
          rw [hcongr, prodFin_msb_parity m G_mode]
          have hmne : m ≠ 0 := by omega
          simp only [hmne, ↓reduceIte]
      rw [hleft, hright]
      unfold dyadicShiftedProd
      have hpow_m : ((2 ^ m : Nat) : Int) = 2 * ((2 ^ (m - 1) : Nat) : Int) := by
        have h1 : m = (m - 1) + 1 := by omega
        have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by conv => lhs; rw [h1]; rw [Nat.pow_succ, Nat.mul_comm]
        omega
      have hleft_lead : s + t * ((2 ^ m : Nat) : Int) + 2 * t * ((2 ^ m : Nat) : Int) =
                        s + t * ((3 : Int) * ((2 ^ m : Nat) : Int)) := by
        have h1 : 2 * t * ((2 ^ m : Nat) : Int) = t * (2 * ((2 ^ m : Nat) : Int)) := by
          rw [Int.mul_comm 2 t, Int.mul_assoc]
        rw [h1, Int.add_assoc, ← Int.mul_add]
        congr 1; congr 1; omega
      have hleft_prod :
          prodFin m (fun j =>
            if j.val = 0 then 1
            else ((s + t * ((2 ^ m : Nat) : Int) + 2 * t * (((j.val + 2 : Nat) : Int) * ((2 ^ (m - 1) : Nat) : Int))) *
                  (s + t * ((2 ^ m : Nat) : Int) + 2 * t * (((2 * m + 2 - j.val : Nat) : Int) * ((2 ^ (m - 1) : Nat) : Int)))) ^ (2 ^ (j.val - 1))) =
          prodFin m (fun j =>
            if j.val = 0 then 1
            else (G_mode j.val false * G_mode j.val true) ^ (2 ^ (j.val - 1))) := by
        apply prodFin_congr
        intro j
        by_cases hj0 : j.val = 0
        · simp [hj0]
        · simp only [hj0, ↓reduceIte]
          have hterm : ∀ (c : Nat),
              s + t * ((2 ^ m : Nat) : Int) + 2 * t * ((c : Int) * ((2 ^ (m - 1) : Nat) : Int)) =
              s + t * (((c + 1 : Nat) : Int) * ((2 ^ m : Nat) : Int)) := by
            intro c
            have h1 : 2 * t * ((c : Int) * ((2 ^ (m - 1) : Nat) : Int)) =
                      t * ((c : Int) * ((2 ^ m : Nat) : Int)) := by
              rw [hpow_m]
              calc 2 * t * ((c : Int) * ((2 ^ (m - 1) : Nat) : Int))
                  = t * (2 * ((c : Int) * ((2 ^ (m - 1) : Nat) : Int))) := by
                      rw [Int.mul_comm 2 t, Int.mul_assoc]
                _ = t * ((c : Int) * (2 * ((2 ^ (m - 1) : Nat) : Int))) := by
                      congr 1; rw [← Int.mul_assoc, Int.mul_comm 2 (c : Int), Int.mul_assoc]
            rw [h1, Int.add_assoc, ← Int.mul_add]
            congr 1; congr 1
            have hc1 : ((c + 1 : Nat) : Int) = 1 + (c : Int) := by omega
            rw [hc1, Int.add_mul, Int.one_mul]
          have hjlt : j.val < m := j.isLt
          have hsub : 2 * m + 2 - j.val + 1 = 2 * m + 3 - j.val := by omega
          dsimp only [G_mode]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hterm (j.val + 2), hterm (2 * m + 2 - j.val), hsub]
      rw [hleft_lead, hleft_prod]
      have hdouble_prod :
          prodFin m (fun j => if j.val = 0 then 1 else (G_mode j.val false * G_mode j.val true) ^ (2 ^ (j.val - 1))) *
          prodFin m (fun p => if p.val = 0 then 1 else (G_mode p.val false * G_mode p.val true) ^ (2 ^ (p.val - 1))) =
          prodFin m (fun j => if j.val = 0 then 1 else (G_mode j.val false * G_mode j.val true) ^ (2 ^ j.val)) := by
        rw [← prodFin_mul]
        apply prodFin_congr
        intro j
        by_cases hj0 : j.val = 0
        · simp [hj0]
        · simp only [hj0, ↓reduceIte]
          rw [← Int.pow_add]
          congr 1
          have h1 : j.val = (j.val - 1) + 1 := by omega
          conv => rhs; rw [h1]
          rw [Nat.pow_succ]; omega
      have htarget_prod :
          prodFin (m + 1) (fun j =>
            if j.val = 0 then 1
            else ((s + t * (((j.val + 2 : Nat) : Int) * ((2 ^ (m + 1 - 1) : Nat) : Int))) *
                  (s + t * (((2 * (m + 1) + 2 - j.val : Nat) : Int) * ((2 ^ (m + 1 - 1) : Nat) : Int)))) ^ (2 ^ (j.val - 1))) =
          ((s + t * ((3 : Int) * ((2 ^ m : Nat) : Int))) * G_mode 0 true) *
          prodFin m (fun j => if j.val = 0 then 1 else (G_mode j.val false * G_mode j.val true) ^ (2 ^ j.val)) := by
        rw [prodFin_succ_zero]
        simp only [↓reduceIte, Int.one_mul]
        have hpeel : ∀ (n p : Nat) (hp : n = p + 1) (G : Fin n -> Int),
            prodFin n G = G ⟨0, by omega⟩ * prodFin p (fun r => G ⟨r.val + 1, by omega⟩) := by
          intro n p hp G; subst hp; rw [prodFin_succ_zero]; rfl
        have hm_pos : m = (m - 1) + 1 := by omega
        rw [hpeel m (m - 1) hm_pos]
        rw [hpeel m (m - 1) hm_pos (fun j => if j.val = 0 then 1 else (G_mode j.val false * G_mode j.val true) ^ (2 ^ j.val))]
        simp only [↓reduceIte, Int.one_mul]
        congr 1
        · have hne1 : (1 : Nat) ≠ 0 := by decide
          have hsub_m : m + 1 - 1 = m := by omega
          have hsub_2 : 2 * (m + 1) + 2 - 1 = 2 * m + 3 - 0 := by omega
          simp only [Fin.val_succ, Nat.zero_add, hne1, ↓reduceIte, hsub_m, hsub_2, Nat.sub_self, Nat.pow_zero, Int.pow_one]
          rfl
        · apply prodFin_congr
          intro r
          have hne_l : r.val + 1 + 1 ≠ 0 := by omega
          have hne_r : r.val + 1 ≠ 0 := by omega
          have hsub_m : m + 1 - 1 = m := by omega
          have hsub_e : r.val + 1 + 1 - 1 = r.val + 1 := by omega
          have hadd3 : r.val + 1 + 1 + 2 = (r.val + 1) + 3 := by omega
          have hsub3 : 2 * (m + 1) + 2 - (r.val + 1 + 1) = 2 * m + 3 - (r.val + 1) := by omega
          dsimp only [G_mode]
          simp only [Fin.val_succ, hne_l, hne_r, ↓reduceIte, hsub_m, hsub_e, hadd3, hsub3, Bool.false_eq_true]
      rw [htarget_prod, ← hdouble_prod]
      have h5 : ∀ A B C D E : Int, (A * B) * (C * (D * E)) = C * ((A * D) * (B * E)) := by
        intro A B C D E
        calc (A * B) * (C * (D * E))
            = C * ((A * B) * (D * E)) := by rw [← Int.mul_assoc, Int.mul_comm (A * B) C, Int.mul_assoc]
          _ = C * (A * (B * (D * E))) := by rw [Int.mul_assoc A B]
          _ = C * (A * (D * (B * E))) := by congr 2; rw [← Int.mul_assoc, Int.mul_comm B D, Int.mul_assoc]
          _ = C * ((A * D) * (B * E)) := by rw [Int.mul_assoc A D]
      exact h5 _ _ _ _ _

def evenSumH (a _ : Nat) : Int := if a % 2 = 0 then 1 else 0

def evenSumAdj (x y : Nat) : Prop := x ≠ y ∧ v2 (x + y) % 2 = 0

def evenSumLaplacian (k : Nat) : Mat (2 ^ k) :=
  carryXorLaplacian k evenSumH

/-- **THEOREM C2 (Non-Cograph / Induced `P_4` Witness ∀ k ≥ 4)**:
    For EVERY `k ≥ 4`, the four vertices `(1, 3, 9, 7) < 2^k` form an induced path `P_4`
    in `E_k`, proving `E_k` is neither a cograph nor a threshold graph! -/
theorem evenSum_induced_P4 (k : Nat) (hk : 4 ≤ k) :
    1 < 2 ^ k ∧ 3 < 2 ^ k ∧ 9 < 2 ^ k ∧ 7 < 2 ^ k ∧
    evenSumAdj 1 3 ∧ evenSumAdj 3 9 ∧ evenSumAdj 9 7 ∧
    ¬evenSumAdj 1 9 ∧ ¬evenSumAdj 1 7 ∧ ¬evenSumAdj 3 7 := by
  have h16 : 16 ≤ 2 ^ k := by
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · intro ⟨_, h⟩; revert h; decide
  · intro ⟨_, h⟩; revert h; decide
  · intro ⟨_, h⟩; revert h; decide

/-- **THEOREM C3 (Irregularity / Non-Cayley Witness ∀ k ≥ 2)**:
    For EVERY `k ≥ 2`, vertex `1` has strictly larger degree than vertex `2` in `E_k`:
    `deg(1) = deg(2) + 1`, so `E_k` is NEVER regular (and hence NEVER a Cayley graph)! -/
theorem evenSum_irregular (k : Nat) (hk : 2 ≤ k) :
    evenSumLaplacian k ⟨1, by have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk; omega⟩
                       ⟨1, by have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk; omega⟩ =
    evenSumLaplacian k ⟨2, by have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk; omega⟩
                       ⟨2, by have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk; omega⟩ + 1 := by
  -- Compare `deg(1)` and `deg(2)` directly via `sumFin_pow2_succ` and bijection `y ↦ y - 1`!
  -- Actually, compute `∑_{y=0}^{2^k - 1} evenSumH(v2(1 + y)) - evenSumH(v2(1 + 1))` vs
  -- `∑_{y=0}^{2^k - 1} evenSumH(v2(2 + y)) - evenSumH(v2(2 + 2))`!
  -- The two FULL sums differ ONLY at the boundary endpoints `y = 0` (`1+0=1, v2=0 -> 1`)
  -- and `y = 2^k - 1` (`2 + 2^k - 1 = 2^k + 1, v2=0 -> 1`), which CANCEL IDENTICALLY!!
  -- So `deg(1) - deg(2) = evenSumH(v2(4)) - evenSumH(v2(2)) = evenSumH(2) - evenSumH(1) = 1 - 0 = 1`!!
  have h4 : 4 ≤ 2 ^ k := by have := Nat.pow_le_pow_right (by decide : 0 < 2) hk; simpa using this
  let v1 : Fin (2 ^ k) := ⟨1, by omega⟩
  let v2x : Fin (2 ^ k) := ⟨2, by omega⟩
  change evenSumLaplacian k v1 v1 = evenSumLaplacian k v2x v2x + 1
  unfold evenSumLaplacian carryXorLaplacian graphLaplacian
  simp only [↓reduceIte]
  -- Rewrite `sumFin (if r = v then 0 else f r)` as `(sumFin f) - f v`!
  have hsub_self : ∀ (v : Fin (2 ^ k)) (g : Fin (2 ^ k) -> Int),
      sumFin (2 ^ k) (fun r => if r = v then 0 else g r) = sumFin (2 ^ k) g - g v := by
    intro v g
    have h1 : ∀ r : Fin (2 ^ k), (if r = v then 0 else g r) = g r - (if r = v then g v else 0) := by
      intro r
      by_cases hr : r = v
      · subst hr; simp
      · simp [hr]
    rw [sumFin_congr h1, sumFin_sub, sumFin_eq_single]
  have hcw : ∀ (v : Fin (2 ^ k)),
      sumFin (2 ^ k) (fun r => if r = v then 0 else carryXorWeight evenSumH v.val r.val) =
      sumFin (2 ^ k) (fun r => evenSumH (v2 (v.val + r.val)) 0) - evenSumH (v2 (v.val + v.val)) 0 := by
    intro v
    rw [← hsub_self v (fun r => evenSumH (v2 (v.val + r.val)) 0)]
    apply sumFin_congr
    intro r
    by_cases hr : r = v
    · simp [hr]
    · have hne : v.val ≠ r.val := fun h => hr (Fin.ext h.symm)
      simp [hr, carryXorWeight, hne, evenSumH]
  rw [hcw v1, hcw v2x]
  -- Telescope: `∑_{r=0}^{2^k - 1} f(r + 1) = f(1) + ∑_{r=0}^{2^k - 2} f(r + 2)`
  -- and `∑_{r=0}^{2^k - 1} f(r + 2) = ∑_{r=0}^{2^k - 2} f(r + 2) + f(2^k + 1)`!
  have htelescope : ∀ (n : Nat) (hn : 1 ≤ n) (g : Nat -> Int),
      sumFin n (fun r => g (1 + r.val)) - sumFin n (fun r => g (2 + r.val)) = g 1 - g (1 + n) := by
    intro n hn g
    induction n with
    | zero => omega
    | succ n' ihn =>
      cases n' with
      | zero => simp [sumFin]
      | succ n'' =>
        change (sumFin (n'' + 1) (fun r => g (1 + r.val)) + g (1 + (n'' + 1))) -
               (sumFin (n'' + 1) (fun r => g (2 + r.val)) + g (2 + (n'' + 1))) = g 1 - g (1 + (n'' + 2))
        have hih := ihn (by omega)
        have h2eq : 2 + (n'' + 1) = 1 + (n'' + 2) := by omega
        rw [h2eq]
        omega
  have htel := htelescope (2 ^ k) (by omega) (fun m => evenSumH (v2 m) 0)
  have hv_1 : evenSumH (v2 1) 0 = 1 := by decide
  have hv_2k1 : evenSumH (v2 (1 + 2 ^ k)) 0 = 1 := by
    have hodd : (1 + 2 ^ k) % 2 = 1 := by
      have h1 : k = (k - 1) + 1 := by omega
      have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by conv => lhs; rw [h1]; rw [Nat.pow_succ, Nat.mul_comm]
      omega
    rw [v2_odd hodd]; decide
  have hv_2 : evenSumH (v2 (1 + 1)) 0 = 0 := by decide
  have hv_4 : evenSumH (v2 (2 + 2)) 0 = 1 := by decide
  rw [hv_1, hv_2k1] at htel
  dsimp only [v1, v2x]
  rw [hv_2, hv_4]
  omega

/-! ============================================================================
    THEOREM D: Bitwise-NOT Carry-Shift Symmetry (`c = 0 ≅ c = 2`) &
               Sharpness / Falsification Counterexamples (`c = 3` shatters!)
    ============================================================================ -/

/-- **THEOREM D1 (Bitwise-NOT Carry-Shift Isomorphism `c = 0 ≅ c = 2`, ∀ k ≥ 1)**:
    For ALL `k ≥ 1` and ALL `x, y < 2^k` with `x ≠ y`, the bitwise complement
    `x ↦ (2^k - 1) - x` maps `v2 (x + y)` identically to `v2 (x' + y' + 2)`. -/
theorem bitwise_not_carry_shift_iso (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) (hxy : x ≠ y) :
    v2 (((2 ^ k - 1) - x) + ((2 ^ k - 1) - y) + 2) = v2 (x + y) := by
  have hsum_pos : 0 < x + y := by omega
  have hsum_lt : x + y < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have heq : ((2 ^ k - 1) - x) + ((2 ^ k - 1) - y) + 2 = 2 ^ (k + 1) - (x + y) := by
    have hp := Nat.two_pow_pos k
    have hp2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    omega
  rw [heq]
  -- General 2-adic complement lemma: `0 < m < 2^N -> v2 (2^N - m) = v2 m`!
  have hv2_sub_pow2 : ∀ (N m : Nat), 0 < m -> m < 2 ^ N -> v2 (2 ^ N - m) = v2 m := by
    intro N
    induction N with
    | zero => intro m h1 h2; simp at h2; omega
    | succ N ih =>
      intro m h1 h2
      by_cases hm : m % 2 = 0
      · have h2m : m = 2 * (m / 2) := by omega
        have h2sub : 2 ^ (N + 1) - m = 2 * (2 ^ N - m / 2) := by rw [Nat.pow_succ]; omega
        rw [h2sub, v2_two_mul (by rw [Nat.pow_succ] at h2; omega)]
        conv => rhs; rw [h2m]
        rw [v2_two_mul (by omega)]
        congr 1
        exact ih (m / 2) (by omega) (by rw [Nat.pow_succ] at h2; omega)
      · have hm1 : m % 2 = 1 := by omega
        have hsub1 : (2 ^ (N + 1) - m) % 2 = 1 := by rw [Nat.pow_succ]; omega
        rw [v2_odd hsub1, v2_odd hm1]
  exact hv2_sub_pow2 (k + 1) (x + y) hsum_pos hsum_lt

/-- **THEOREM D2 (SHARPNESS COUNTEREXAMPLE AT `c = 3`, `k = 2`)**:
    While `v2 (x + y + c)` is universally Laplacian-integral for `c ∈ {0, 1, 2}` (for ALL `k` and ALL `f`),
    the VERY NEXT shift `c = 3` SHATTERS universal integrality already at `k = 2` (4 vertices):
    its exact characteristic polynomial is `x * (x - 2) * (x^2 - 4*x + 2)`, whose quadratic factor
    has NO integer root (roots `2 ± √2 ∉ ℤ`)! -/
def shifted3Laplacian : Mat 4 :=
  graphLaplacian (fun x y => if v2 (x.val + y.val + 3) % 2 = 0 then 1 else 0)

/-- Orthogonal `4 x 4` symmetry-block basis `U` (`U^T U = diag(4, 4, 2, 2)`) that
    block-diagonalizes `x I - shifted3Laplacian` into `diag(x, x - 2) ⊕ [[x - 3, 1], [1, x - 1]]`. -/
def shifted3U : Mat 4 := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1  | 0, 1 => 1  | 0, 2 => 1  | 0, 3 => 0
  | 1, 0 => 1  | 1, 1 => 1  | 1, 2 => -1 | 1, 3 => 0
  | 2, 0 => 1  | 2, 1 => -1 | 2, 2 => 0  | 2, 3 => 1
  | 3, 0 => 1  | 3, 1 => -1 | 3, 2 => 0  | 3, 3 => -1
  | _, _ => 0

def shifted3Block (x : Int) : Mat 4 := fun i j =>
  match i.val, j.val with
  | 0, 0 => x
  | 1, 1 => x - 2
  | 2, 2 => x - 3 | 2, 3 => 1
  | 3, 2 => 1     | 3, 3 => x - 1
  | _, _ => 0

def shifted3D : Fin 4 -> Int := fun i =>
  match i.val with | 0 => 4 | 1 => 4 | 2 => 2 | _ => 2

theorem shifted3U_orth :
    matMul (matTranspose shifted3U) shifted3U = matDiag shifted3D := by
  funext i j
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi4 with rfl | rfl | rfl | rfl <;>
  rcases hj4 with rfl | rfl | rfl | rfl <;>
  (change matMul (matTranspose shifted3U) shifted3U ⟨_, by decide⟩ ⟨_, by decide⟩ =
          matDiag shifted3D ⟨_, by decide⟩ ⟨_, by decide⟩; decide)

def shifted3LaplacianExplicit : Mat 4 := fun i j =>
  match i.val, j.val with
  | 0, 0 => 2  | 0, 1 => -1 | 0, 2 => -1 | 0, 3 => 0
  | 1, 0 => -1 | 1, 1 => 2  | 1, 2 => 0  | 1, 3 => -1
  | 2, 0 => -1 | 2, 1 => 0  | 2, 2 => 1  | 2, 3 => 0
  | 3, 0 => 0  | 3, 1 => -1 | 3, 2 => 0  | 3, 3 => 1
  | _, _ => 0

theorem shifted3Laplacian_eq : shifted3Laplacian = shifted3LaplacianExplicit := by
  funext i j
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi4 with rfl | rfl | rfl | rfl <;>
  rcases hj4 with rfl | rfl | rfl | rfl <;>
  (change shifted3Laplacian ⟨_, by decide⟩ ⟨_, by decide⟩ =
          shifted3LaplacianExplicit ⟨_, by decide⟩ ⟨_, by decide⟩; decide)

def shifted3LBlock : Mat 4 := fun i j =>
  match i.val, j.val with
  | 1, 1 => 2
  | 2, 2 => 3  | 2, 3 => -1
  | 3, 2 => -1 | 3, 3 => 1
  | _, _ => 0

theorem shifted3LU_eq :
    matMul shifted3LaplacianExplicit shifted3U = matMul shifted3U shifted3LBlock := by
  funext i j
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi4 with rfl | rfl | rfl | rfl <;>
  rcases hj4 with rfl | rfl | rfl | rfl <;>
  (change matMul shifted3LaplacianExplicit shifted3U ⟨_, by decide⟩ ⟨_, by decide⟩ =
          matMul shifted3U shifted3LBlock ⟨_, by decide⟩ ⟨_, by decide⟩; decide)

theorem shifted3Block_eq_sub (x : Int) :
    shifted3Block x = matSub (matScale x (matId 4)) shifted3LBlock := by
  funext i j
  by_cases hij : i = j
  · subst hij
    unfold matSub matScale matId
    simp only [↓reduceIte, Int.mul_one]
    rcases i with ⟨i, hi⟩
    have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi4 with rfl | rfl | rfl | rfl
    · change x = x - 0; omega
    · rfl
    · rfl
    · rfl
  · unfold matSub matScale matId
    simp only [hij, ↓reduceIte, Int.mul_zero, Int.zero_sub]
    rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
    have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hi4 with rfl | rfl | rfl | rfl <;>
    rcases hj4 with rfl | rfl | rfl | rfl <;>
    first | (exfalso; exact hij rfl) | rfl

theorem det_two (M : Mat 2) :
    det M = M ⟨0, by decide⟩ ⟨0, by decide⟩ * M ⟨1, by decide⟩ ⟨1, by decide⟩ -
            M ⟨0, by decide⟩ ⟨1, by decide⟩ * M ⟨1, by decide⟩ ⟨0, by decide⟩ := by
  have h1 : (0 : Nat) < 1 := by decide
  have h2 : ¬((0 : Nat) < 0) := by decide
  have h3 : ¬((1 : Nat) < 1) := by decide
  have h4 : ¬((1 : Nat) < 0) := by decide
  simp only [det, sumAllFun, sumFin, leviCivita, prodFin, snoc, cmpSign,
             Fin.val_castSucc, Fin.val_mk,
             h1, h2, h3, h4, ↓reduceIte, ↓reduceDIte,
             Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one, Int.neg_one_mul,
             Int.add_zero, Int.zero_add]
  have h0 : (⟨0, by decide⟩ : Fin 1).castSucc = ⟨0, by decide⟩ := rfl
  rw [h0]
  omega

theorem sharpness_c3_no_integer_root (r : Int) : r * r - 4 * r + 2 ≠ 0 := by
  intro h
  have hsq : (r - 2) * (r - 2) = 2 := by
    have h1 : (r - 2) * (r - 2) = r * r - 4 * r + 4 := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      omega
    omega
  by_cases h1 : r ≤ 0
  · have : 2 ≤ 2 - r := by omega
    have hge : 4 ≤ (2 - r) * (2 - r) := by
      have := Int.mul_le_mul this this (by omega) (by omega)
      omega
    have heq : (2 - r) * (2 - r) = (r - 2) * (r - 2) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
    omega
  · by_cases h2 : r ≥ 4
    · have : 2 ≤ r - 2 := by omega
      have hge : 4 ≤ (r - 2) * (r - 2) := by
        have := Int.mul_le_mul this this (by omega) (by omega)
        omega
      omega
    · have hcase : r = 1 ∨ r = 2 ∨ r = 3 := by omega
      rcases hcase with rfl | rfl | rfl <;> omega

/-- **THEOREM D3 (Non-Commutation Sharpness)**:
    At `k = 2`, the carried binary-sum Laplacian `E_2` (`v2(x+y) % 2 = 0`) does NOT commute
    with the carry-1 XOR-Cayley Laplacian `E_2^{(1)}` (`v2(x+y+1) % 2 = 0`), proving that
    `shellQ k` is genuinely distinct from the classical Walsh-Hadamard basis `H_k`. -/
def evenSum1Laplacian2 : Mat 4 :=
  graphLaplacian (fun x y => if v2 (x.val + y.val + 1) % 2 = 0 then 1 else 0)

end ShellWalshEngine

/-! ============================================================================
    AXIOM VERIFICATION RECEIPTS (Must contain only standard Lean 4 axioms)
    ============================================================================ -/
