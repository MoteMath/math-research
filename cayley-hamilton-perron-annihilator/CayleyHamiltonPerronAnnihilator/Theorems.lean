import CayleyHamiltonPerronAnnihilator.Defs

namespace CHKAE
theorem finSum_zero (n : Nat) : finSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [finSum, ih]

theorem finSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem finSum_add (n : Nat) (f g : Fin n → Int) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem finSum_sub (n : Nat) (f g : Fin n → Int) :
    finSum n (fun i => f i - g i) = finSum n f - finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem finSum_mul_left (n : Nat) (c : Int) (f : Fin n → Int) :
    finSum n (fun i => c * f i) = c * finSum n f := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc), Int.mul_add]

theorem finSum_mul_right (n : Nat) (f : Fin n → Int) (c : Int) :
    finSum n (fun i => f i * c) = finSum n f * c := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc), Int.add_mul]

theorem finSum_swap (m n : Nat) (f : Fin m → Fin n → Int) :
    finSum m (fun i => finSum n (fun j => f i j)) =
    finSum n (fun j => finSum m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [finSum]
    exact (finSum_zero n).symm
  | succ m ih =>
    simp only [finSum]
    rw [ih (fun i j => f i.castSucc j)]
    exact (finSum_add n (fun j => finSum m (fun i => f i.castSucc j))
      (fun j => f (Fin.last m) j)).symm

theorem finSum_nonneg {n : Nat} {f : Fin n → Int} (h : ∀ i, 0 ≤ f i) :
    0 ≤ finSum n f := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h (Fin.last n)
    omega

theorem finSum_le_finSum {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h (Fin.last n)
    omega

theorem finSum_pos_of_nonneg_of_exists_pos {n : Nat} {f : Fin n → Int}
    (hge : ∀ i, 0 ≤ f i) (hex : ∃ i, 0 < f i) : 0 < finSum n f := by
  induction n with
  | zero =>
    rcases hex with ⟨i, _⟩
    exact Fin.elim0 i
  | succ n ih =>
    simp only [finSum]
    rcases hex with ⟨i, hi⟩
    cases i using Fin.lastCases with
    | last =>
      have h1 : 0 ≤ finSum n (fun j => f j.castSucc) := finSum_nonneg (fun j => hge j.castSucc)
      omega
    | cast j =>
      have h1 : 0 < finSum n (fun k => f k.castSucc) := ih (fun k => hge k.castSucc) ⟨j, hi⟩
      have h2 : 0 ≤ f (Fin.last n) := hge (Fin.last n)
      omega

/-- Constructive extraction of a positive summand from a positive sum of nonnegatives. -/
theorem exists_pos_of_finSum_pos {n : Nat} {f : Fin n → Int}
    (hge : ∀ i, 0 ≤ f i) (hpos : 0 < finSum n f) : ∃ i, 0 < f i := by
  induction n with
  | zero =>
    simp [finSum] at hpos
  | succ n ih =>
    simp only [finSum] at hpos
    by_cases hlast : 0 < f (Fin.last n)
    · exact ⟨Fin.last n, hlast⟩
    · have hle : f (Fin.last n) ≤ 0 := by omega
      have hprev : 0 < finSum n (fun i => f i.castSucc) := by omega
      rcases ih (fun i => hge i.castSucc) hprev with ⟨j, hj⟩
      exact ⟨j.castSucc, hj⟩

theorem finSum_shift (m : Nat) (f : Fin (m + 1) → Int) :
    f 0 + finSum m (fun i => f i.succ) = finSum (m + 1) f := by
  induction m with
  | zero => simp [finSum]
  | succ m ihm =>
    change f 0 + (finSum m (fun i => f i.castSucc.succ) + f (Fin.last (m + 1))) =
      finSum (m + 1) (fun i => f i.castSucc) + f (Fin.last (m + 1))
    have h1 := ihm (fun i => f i.castSucc)
    change f 0 + finSum m (fun i => f i.castSucc.succ) = finSum (m + 1) (fun i => f i.castSucc) at h1
    omega

private theorem fin_castSucc_ne_last {n : Nat} (i : Fin n) : i.castSucc ≠ Fin.last n := by
  intro h
  have hv : i.val = n := congrArg Fin.val h
  omega

theorem finSum_single_eq (n : Nat) (k : Fin n) (c : Int) :
    finSum n (fun i => if i = k then c else 0) = c := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [finSum]
    cases k using Fin.lastCases with
    | last =>
      have h0 : finSum n (fun i : Fin n => if i.castSucc = Fin.last n then c else 0) = 0 := by
        rw [finSum_congr (g := fun _ => 0)]
        · exact finSum_zero n
        · intro i
          have hne := fin_castSucc_ne_last i
          simp [hne]
      simp [h0]
    | cast k' =>
      have h1 : finSum n (fun i : Fin n => if i.castSucc = k'.castSucc then c else 0) = c := by
        rw [finSum_congr (g := fun i => if i = k' then c else 0)]
        · exact ih k'
        · intro i
          by_cases h : i = k'
          · subst h; simp
          · have hne : i.castSucc ≠ k'.castSucc := fun heq => h (Fin.castSucc_inj.mp heq)
            simp [h, hne]
      have hne : Fin.last n ≠ k'.castSucc := (fin_castSucc_ne_last k').symm
      simp [h1, hne]

private theorem int_pos_of_mul_pos_left {a b : Int} (ha : 0 < a) (hab : 0 < a * b) : 0 < b := by
  by_cases hb : 0 < b
  · exact hb
  · have hle : 0 ≤ a * (-b) := Int.mul_nonneg (by omega) (by omega)
    rw [Int.mul_neg] at hle
    omega

private theorem int_le_of_mul_le_left {a b c : Int} (ha : 0 < a) (h : a * b ≤ a * c) : b ≤ c := by
  by_cases hbc : b ≤ c
  · exact hbc
  · have hlt : c < b := by omega
    have hmul := Int.mul_lt_mul_of_pos_left hlt ha
    omega

/-! ### Abstract Vectors and Rectangular/Square Matrices over `Int` -/

theorem rMatMul_assoc {a b c d : Nat} (A : RMat a b) (B : RMat b c) (C : RMat c d) :
    rMatMul (rMatMul A B) C = rMatMul A (rMatMul B C) := by
  funext i j
  simp only [rMatMul]
  calc
    finSum c (fun t => finSum b (fun s => A i s * B s t) * C t j)
      = finSum c (fun t => finSum b (fun s => (A i s * B s t) * C t j)) := by
          apply finSum_congr; intro t; rw [← finSum_mul_right]
    _ = finSum b (fun s => finSum c (fun t => (A i s * B s t) * C t j)) := finSum_swap c b _
    _ = finSum b (fun s => A i s * finSum c (fun t => B s t * C t j)) := by
          apply finSum_congr; intro s
          rw [← finSum_mul_left]
          apply finSum_congr; intro t; exact Int.mul_assoc _ _ _

theorem rMatMul_matId_left {r c : Nat} (A : RMat r c) : rMatMul (matId r) A = A := by
  funext i j
  simp only [rMatMul, matId]
  rw [finSum_congr (g := fun t => if t = i then A i j else 0)]
  · exact finSum_single_eq r i (A i j)
  · intro t
    by_cases h : i = t
    · subst h; simp
    · have h' : t ≠ i := fun heq => h heq.symm
      simp [h, h']

theorem rMatMul_matId_right {r c : Nat} (A : RMat r c) : rMatMul A (matId c) = A := by
  funext i j
  simp only [rMatMul, matId]
  rw [finSum_congr (g := fun t => if t = j then A i j else 0)]
  · exact finSum_single_eq c j (A i j)
  · intro t
    by_cases h : t = j
    · subst h; simp
    · simp [h]

theorem rMatVecMul_assoc {r k c : Nat} (A : RMat r k) (B : RMat k c) (v : Vec c) :
    rMatVecMul (rMatMul A B) v = rMatVecMul A (rMatVecMul B v) := by
  funext i
  simp only [rMatVecMul, rMatMul]
  calc
    finSum c (fun j => finSum k (fun t => A i t * B t j) * v j)
      = finSum c (fun j => finSum k (fun t => (A i t * B t j) * v j)) := by
          apply finSum_congr; intro j; rw [← finSum_mul_right]
    _ = finSum k (fun t => finSum c (fun j => (A i t * B t j) * v j)) := finSum_swap c k _
    _ = finSum k (fun t => A i t * finSum c (fun j => B t j * v j)) := by
          apply finSum_congr; intro t
          rw [← finSum_mul_left]
          apply finSum_congr; intro j; exact Int.mul_assoc _ _ _

theorem rMatVecMul_matId {d : Nat} (v : Vec d) : rMatVecMul (matId d) v = v := by
  funext i
  simp only [rMatVecMul, matId]
  rw [finSum_congr (g := fun j => if j = i then v i else 0)]
  · exact finSum_single_eq d i (v i)
  · intro j
    by_cases h : i = j
    · subst h; simp
    · have h' : j ≠ i := fun heq => h heq.symm
      simp [h, h']

theorem rMatVecMul_sub {r c : Nat} (A : RMat r c) (v w : Vec c) :
    rMatVecMul A (vecSub v w) = vecSub (rMatVecMul A v) (rMatVecMul A w) := by
  funext i
  simp only [rMatVecMul, vecSub]
  rw [← finSum_sub]
  apply finSum_congr; intro j; exact Int.mul_sub _ _ _

theorem rMatVecMul_scale {r c : Nat} (A : RMat r c) (a : Int) (v : Vec c) :
    rMatVecMul A (vecScale a v) = vecScale a (rMatVecMul A v) := by
  funext i
  simp only [rMatVecMul, vecScale]
  rw [← finSum_mul_left]
  apply finSum_congr; intro j
  rw [← Int.mul_assoc, Int.mul_comm (A i j) a, Int.mul_assoc]

theorem rMatScale_mul_left {r k c : Nat} (a : Int) (A : RMat r k) (B : RMat k c) :
    rMatMul (rMatScale a A) B = rMatScale a (rMatMul A B) := by
  funext i j
  simp only [rMatMul, rMatScale]
  rw [← finSum_mul_left]
  apply finSum_congr; intro t; exact Int.mul_assoc _ _ _

theorem rMatScale_mul_right {r k c : Nat} (A : RMat r k) (a : Int) (B : RMat k c) :
    rMatMul A (rMatScale a B) = rMatScale a (rMatMul A B) := by
  funext i j
  simp only [rMatMul, rMatScale]
  rw [← finSum_mul_left]
  apply finSum_congr; intro t
  rw [← Int.mul_assoc, Int.mul_comm (A i t) a, Int.mul_assoc]

theorem rMatScale_vecMul {r c : Nat} (a : Int) (A : RMat r c) (v : Vec c) :
    rMatVecMul (rMatScale a A) v = vecScale a (rMatVecMul A v) := by
  funext i
  simp only [rMatVecMul, rMatScale, vecScale]
  rw [← finSum_mul_left]
  apply finSum_congr; intro j; exact Int.mul_assoc _ _ _

theorem vecDot_rMatVecMul {r c : Nat} (u : Vec r) (A : RMat r c) (v : Vec c) :
    vecDot u (rMatVecMul A v) = vecDot (vecRMatMul u A) v := by
  simp only [vecDot, rMatVecMul, vecRMatMul]
  calc
    finSum r (fun i => u i * finSum c (fun j => A i j * v j))
      = finSum r (fun i => finSum c (fun j => u i * (A i j * v j))) := by
          apply finSum_congr; intro i; rw [← finSum_mul_left]
    _ = finSum c (fun j => finSum r (fun i => u i * (A i j * v j))) := finSum_swap r c _
    _ = finSum c (fun j => finSum r (fun i => u i * A i j) * v j) := by
          apply finSum_congr; intro j
          rw [← finSum_mul_right]
          apply finSum_congr; intro i; exact (Int.mul_assoc _ _ _).symm

theorem vecDot_sub_right {d : Nat} (u v w : Vec d) :
    vecDot u (vecSub v w) = vecDot u v - vecDot u w := by
  simp only [vecDot, vecSub]
  rw [← finSum_sub]
  apply finSum_congr; intro i; exact Int.mul_sub _ _ _

theorem vecDot_scale_right {d : Nat} (u : Vec d) (a : Int) (v : Vec d) :
    vecDot u (vecScale a v) = a * vecDot u v := by
  simp only [vecDot, vecScale]
  rw [← finSum_mul_left]
  apply finSum_congr; intro i
  rw [← Int.mul_assoc, Int.mul_comm (u i) a, Int.mul_assoc]

theorem matPow_add {d : Nat} (M : Mat d) (a b : Nat) :
    matPow M (a + b) = rMatMul (matPow M a) (matPow M b) := by
  induction a with
  | zero =>
    simp only [Nat.zero_add, matPow]
    exact (rMatMul_matId_left (matPow M b)).symm
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [matPow]
    rw [ih, rMatMul_assoc]

theorem matPow_succ_right {d : Nat} (M : Mat d) (n : Nat) :
    matPow M (n + 1) = rMatMul (matPow M n) M := by
  rw [matPow_add]
  have h1 : matPow M 1 = M := by simp [matPow, rMatMul_matId_right]
  rw [h1]

theorem matPow_scale {d : Nat} (a : Int) (M : Mat d) (n : Nat) :
    matPow (rMatScale a M) n = rMatScale (a ^ n) (matPow M n) := by
  induction n with
  | zero =>
    funext i j
    simp [matPow, rMatScale]
  | succ n ih =>
    simp only [matPow]
    rw [ih, rMatScale_mul_left, rMatScale_mul_right]
    funext i j
    simp only [rMatScale]
    rw [Int.pow_succ, Int.mul_comm (a ^ n) a, Int.mul_assoc]

theorem obs_scale_mat {d : Nat} (a : Int) (M : Mat d) (u v : Vec d) (n : Nat) :
    obs (rMatScale a M) u v n = a ^ n * obs M u v n := by
  simp only [obs, matPow_scale, rMatScale_vecMul, vecDot_scale_right]

theorem rMatVecMul_finSum {d k : Nat} (A : Mat d) (f : Fin k → Vec d) :
    rMatVecMul A (fun i => finSum k (fun j => f j i)) =
    fun i => finSum k (fun j => rMatVecMul A (f j) i) := by
  funext i
  simp only [rMatVecMul]
  calc
    finSum d (fun t => A i t * finSum k (fun j => f j t))
      = finSum d (fun t => finSum k (fun j => A i t * f j t)) := by
          apply finSum_congr; intro t; rw [← finSum_mul_left]
    _ = finSum k (fun j => finSum d (fun t => A i t * f j t)) := finSum_swap d k _

theorem vecDot_finSum {d k : Nat} (u : Vec d) (f : Fin k → Vec d) :
    vecDot u (fun i => finSum k (fun j => f j i)) =
    finSum k (fun j => vecDot u (f j)) := by
  simp only [vecDot]
  calc
    finSum d (fun i => u i * finSum k (fun j => f j i))
      = finSum d (fun i => finSum k (fun j => u i * f j i)) := by
          apply finSum_congr; intro i; rw [← finSum_mul_left]
    _ = finSum k (fun j => finSum d (fun i => u i * f j i)) := finSum_swap d k _

theorem rMatVecMul_matIterLinComb {d k : Nat} (M : Mat d) (c : Fin k → Int) (v : Vec d) :
    rMatVecMul (matIterLinComb M c) v = vecIterLinComb M v c := by
  funext i
  simp only [rMatVecMul, matIterLinComb, vecIterLinComb]
  calc
    finSum d (fun j => finSum k (fun t => c t * matPow M t.val i j) * v j)
      = finSum d (fun j => finSum k (fun t => (c t * matPow M t.val i j) * v j)) := by
          apply finSum_congr; intro j; rw [← finSum_mul_right]
    _ = finSum k (fun t => finSum d (fun j => (c t * matPow M t.val i j) * v j)) :=
          finSum_swap d k _
    _ = finSum k (fun t => c t * finSum d (fun j => matPow M t.val i j * v j)) := by
          apply finSum_congr; intro t
          rw [← finSum_mul_left]
          apply finSum_congr; intro j; exact Int.mul_assoc _ _ _

/-- Right-Krylov annihilator lifting: `M^k v = ∑ c_j M^j v` lifts to all `n : Nat`. -/
theorem krylov_ann_lift {d k : Nat} (M : Mat d) (v : Vec d) (c : Fin k → Int)
    (h : rMatVecMul (matPow M k) v = vecIterLinComb M v c) :
    ∀ n : Nat, rMatVecMul (matPow M (n + k)) v =
      fun i => finSum k (fun j => c j * rMatVecMul (matPow M (n + j.val)) v i) := by
  intro n
  rw [matPow_add, rMatVecMul_assoc, h]
  have h1 := rMatVecMul_finSum (matPow M n) (fun j : Fin k => vecScale (c j) (rMatVecMul (matPow M j.val) v))
  funext i
  have hi := congrFun h1 i
  simp only [vecScale] at hi
  change rMatVecMul (matPow M n) (fun t => finSum k (fun j => c j * rMatVecMul (matPow M j.val) v t)) i = _
  rw [hi]
  apply finSum_congr
  intro j
  rw [rMatVecMul_scale, ← rMatVecMul_assoc, ← matPow_add]
  rfl

theorem krylov_obs_recurrence {d k : Nat} (M : Mat d) (u v : Vec d) (c : Fin k → Int)
    (h : rMatVecMul (matPow M k) v = vecIterLinComb M v c) :
    ∀ n : Nat, obs M u v (n + k) = finSum k (fun j => c j * obs M u v (n + j.val)) := by
  intro n
  simp only [obs]
  rw [krylov_ann_lift M v c h n]
  have h1 := vecDot_finSum u (fun j : Fin k => vecScale (c j) (rMatVecMul (matPow M (n + j.val)) v))
  simp only [vecScale] at h1
  rw [h1]
  apply finSum_congr
  intro j
  exact vecDot_scale_right u (c j) (rMatVecMul (matPow M (n + j.val)) v)

/-- Zero-observable lifting from Krylov annihilator + `k` initial zeroes. -/
theorem krylov_obs_zero {d k : Nat} (M : Mat d) (u v : Vec d) (c : Fin k → Int)
    (hann : rMatVecMul (matPow M k) v = vecIterLinComb M v c)
    (hinit : ∀ j : Fin k, obs M u v j.val = 0) :
    ∀ n : Nat, obs M u v n = 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hlt : n < k
    · exact hinit ⟨n, hlt⟩
    · have hge : k ≤ n := Nat.le_of_not_lt hlt
      have hsplit : n = (n - k) + k := (Nat.sub_add_cancel hge).symm
      rw [hsplit, krylov_obs_recurrence M u v c hann (n - k)]
      rw [finSum_congr (g := fun _ => 0)]
      · exact finSum_zero k
      · intro j
        have hlt2 : (n - k) + j.val < n := by omega
        rw [ih ((n - k) + j.val) hlt2, Int.mul_zero]

/-- Two-Stage Quotient Annihilator Theorem (Kalman Observability Projection):
    Even when `p(M) (M^{n0} v) ≠ 0`, if the defect vector `w = M^k v0 - ∑ c_j M^j v0`
    is annihilated by `r(M) w = 0` and `u^T M^j w = 0` for `j < deg r`, then
    `obs M u v` satisfies the reduced recurrence `c` for ALL `n : Nat`! -/
theorem quot_ann_obs_recurrence {d k dr : Nat} (M : Mat d) (u v : Vec d) (n0 : Nat)
    (c : Fin k → Int) (r : Fin dr → Int)
    (hdef_ann :
      let v0 := rMatVecMul (matPow M n0) v
      let w := vecSub (rMatVecMul (matPow M k) v0) (vecIterLinComb M v0 c)
      rMatVecMul (matPow M dr) w = vecIterLinComb M w r)
    (hdef_init :
      let v0 := rMatVecMul (matPow M n0) v
      let w := vecSub (rMatVecMul (matPow M k) v0) (vecIterLinComb M v0 c)
      ∀ j : Fin dr, obs M u w j.val = 0) :
    ∀ n : Nat, obs M u v (n + n0 + k) = finSum k (fun j => c j * obs M u v (n + n0 + j.val)) := by
  intro n
  let v0 := rMatVecMul (matPow M n0) v
  let w := vecSub (rMatVecMul (matPow M k) v0) (vecIterLinComb M v0 c)
  have hw0 : obs M u w n = 0 := krylov_obs_zero M u w r hdef_ann hdef_init n
  have hexp : obs M u w n =
      obs M u v (n + n0 + k) - finSum k (fun j => c j * obs M u v (n + n0 + j.val)) := by
    simp only [obs, w, v0]
    rw [rMatVecMul_sub, vecDot_sub_right]
    have hL : rMatVecMul (matPow M n) (rMatVecMul (matPow M k) (rMatVecMul (matPow M n0) v)) =
        rMatVecMul (matPow M (n + n0 + k)) v := by
      rw [← rMatVecMul_assoc, ← rMatVecMul_assoc, ← matPow_add, ← matPow_add]
      have heq : n + k + n0 = n + n0 + k := by omega
      rw [heq]
    have hR : vecDot u (rMatVecMul (matPow M n) (vecIterLinComb M (rMatVecMul (matPow M n0) v) c)) =
        finSum k (fun j => c j * vecDot u (rMatVecMul (matPow M (n + n0 + j.val)) v)) := by
      have h1 := rMatVecMul_finSum (matPow M n)
        (fun j : Fin k => vecScale (c j) (rMatVecMul (matPow M j.val) (rMatVecMul (matPow M n0) v)))
      have h2 : rMatVecMul (matPow M n) (vecIterLinComb M (rMatVecMul (matPow M n0) v) c) =
          fun i => finSum k (fun j => c j * rMatVecMul (matPow M (n + n0 + j.val)) v i) := by
        funext i
        have hi := congrFun h1 i
        simp only [vecScale] at hi
        change rMatVecMul (matPow M n) (fun t => finSum k (fun j => c j * rMatVecMul (matPow M j.val) (rMatVecMul (matPow M n0) v) t)) i = _
        rw [hi]
        apply finSum_congr; intro j
        rw [rMatVecMul_scale, ← rMatVecMul_assoc, ← rMatVecMul_assoc, ← matPow_add, ← matPow_add]
        have heq : n + j.val + n0 = n + n0 + j.val := by omega
        rw [heq]
        rfl
      rw [h2]
      have h3 := vecDot_finSum u (fun j : Fin k => vecScale (c j) (rMatVecMul (matPow M (n + n0 + j.val)) v))
      simp only [vecScale] at h3
      rw [h3]
      apply finSum_congr; intro j
      exact vecDot_scale_right u (c j) (rMatVecMul (matPow M (n + n0 + j.val)) v)
    rw [hL, hR]
  omega

/-! ### Concrete List-Backed Executable Layer (`CVec`, `CMat`) for Fast Kernel `decide` -/

theorem list_getD_eq_getElem {α : Type} (l : List α) (i : Nat) (hi : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem hi]

theorem list_getD_map {α β : Type} (f : α → β) (l : List α) (i : Nat) (hi : i < l.length) (da : α) (db : β) :
    (l.map f).getD i db = f (l.getD i da) := by
  rw [list_getD_eq_getElem (l.map f) i (by simp [hi]) db,
      list_getD_eq_getElem l i hi da, List.getElem_map]

theorem list_getD_range (n i : Nat) (hi : i < n) (d : Nat) :
    (List.range n).getD i d = i := by
  rw [list_getD_eq_getElem (List.range n) i (by simp [hi]) d, List.getElem_range]

theorem cVecDotAux_eq_finSum (n : Nat) (u v : CVec) (hu : u.length = n) (hv : v.length = n) :
    cVecDotAux u v = finSum n (fun i => u.getD i.val 0 * v.getD i.val 0) := by
  induction n generalizing u v with
  | zero =>
    cases u with
    | nil =>
      cases v with
      | nil => rfl
      | cons _ _ => simp at hv
    | cons _ _ => simp at hu
  | succ n ih =>
    cases u with
    | nil => simp at hu
    | cons a as =>
      cases v with
      | nil => simp at hv
      | cons b bs =>
        simp only [List.length_cons, Nat.succ.injEq] at hu hv
        simp only [cVecDotAux]
        rw [ih as bs hu hv]
        have h2 := finSum_shift n (fun i : Fin (n + 1) => (a :: as).getD i.val 0 * (b :: bs).getD i.val 0)
        rw [← h2]
        rfl

theorem cVecDot_eq {d : Nat} (u v : CVec) (hu : u.length = d) (hv : v.length = d) :
    cVecDot u v = vecDot (toVec d u) (toVec d v) :=
  cVecDotAux_eq_finSum d u v hu hv

theorem cVecAdd_length (u v : CVec) (d : Nat) (hu : u.length = d) (hv : v.length = d) :
    (cVecAdd u v).length = d := by
  induction d generalizing u v with
  | zero => cases u <;> cases v <;> simp_all [cVecAdd]
  | succ d ih => cases u <;> cases v <;> simp_all [cVecAdd]

theorem toVec_cVecAdd {d : Nat} (u v : CVec) (hu : u.length = d) (hv : v.length = d) :
    toVec d (cVecAdd u v) = vecAdd (toVec d u) (toVec d v) := by
  funext i
  rcases i with ⟨idx, hidx⟩
  induction d generalizing u v idx with
  | zero => omega
  | succ d ih =>
    cases u with
    | nil => simp at hu
    | cons a as =>
      cases v with
      | nil => simp at hv
      | cons b bs =>
        simp only [List.length_cons, Nat.succ.injEq] at hu hv
        cases idx with
        | zero => rfl
        | succ k => exact ih as bs hu hv k (by omega)

theorem cVecSub_length (u v : CVec) (d : Nat) (hu : u.length = d) (hv : v.length = d) :
    (cVecSub u v).length = d := by
  induction d generalizing u v with
  | zero => cases u <;> cases v <;> simp_all [cVecSub]
  | succ d ih => cases u <;> cases v <;> simp_all [cVecSub]

theorem toVec_cVecSub {d : Nat} (u v : CVec) (hu : u.length = d) (hv : v.length = d) :
    toVec d (cVecSub u v) = vecSub (toVec d u) (toVec d v) := by
  funext i
  rcases i with ⟨idx, hidx⟩
  induction d generalizing u v idx with
  | zero => omega
  | succ d ih =>
    cases u with
    | nil => simp at hu
    | cons a as =>
      cases v with
      | nil => simp at hv
      | cons b bs =>
        simp only [List.length_cons, Nat.succ.injEq] at hu hv
        cases idx with
        | zero => rfl
        | succ k => exact ih as bs hu hv k (by omega)

theorem cVecScale_length (a : Int) (v : CVec) (d : Nat) (hv : v.length = d) :
    (cVecScale a v).length = d := by
  simp [cVecScale, hv]

theorem toVec_cVecScale {d : Nat} (a : Int) (v : CVec) (hv : v.length = d) :
    toVec d (cVecScale a v) = vecScale a (toVec d v) := by
  funext i
  simp only [toVec, cVecScale, vecScale]
  rw [list_getD_map _ _ _ (by omega) 0 0]

theorem wfMat_of_bool {r c : Nat} {M : CMat} (h : wfMatBool r c M = true) : WFMat r c M := by
  simp only [wfMatBool, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro i
  have hi : i.val < M.length := by rw [h.1]; exact i.isLt
  rw [list_getD_eq_getElem M i.val hi []]
  exact h.2 (M[i.val]) (List.getElem_mem hi)

theorem cMatVecMul_length {r c : Nat} (M : CMat) (v : CVec) (hM : WFMat r c M) :
    (cMatVecMul M v).length = r := by
  simp [cMatVecMul, hM.1]

theorem toVec_cMatVecMul {r c : Nat} (M : CMat) (v : CVec)
    (hM : WFMat r c M) (hv : v.length = c) :
    toVec r (cMatVecMul M v) = rMatVecMul (toMat r c M) (toVec c v) := by
  funext i
  simp only [toVec, cMatVecMul, rMatVecMul, toMat]
  rw [list_getD_map _ _ _ (by rw [hM.1]; exact i.isLt) [] 0]
  exact cVecDot_eq (M.getD i.val []) v (hM.2 i) hv

theorem cMatScale_wf {r c : Nat} (a : Int) (M : CMat) (hM : WFMat r c M) :
    WFMat r c (cMatScale a M) := by
  refine ⟨by simp [cMatScale, hM.1], ?_⟩
  intro i
  simp only [cMatScale]
  rw [list_getD_map _ _ _ (by rw [hM.1]; exact i.isLt) [] []]
  rw [List.length_map]
  exact hM.2 i

theorem toMat_cMatScale {r c : Nat} (a : Int) (M : CMat) (hM : WFMat r c M) :
    toMat r c (cMatScale a M) = rMatScale a (toMat r c M) := by
  funext i j
  simp only [toMat, cMatScale, rMatScale]
  rw [list_getD_map _ _ _ (by rw [hM.1]; exact i.isLt) [] []]
  rw [list_getD_map _ _ _ (by rw [hM.2 i]; exact j.isLt) 0 0]

theorem cMatAdd_wf {r c : Nat} (A B : CMat) (hA : WFMat r c A) (hB : WFMat r c B) :
    WFMat r c (cMatAdd A B) := by
  rcases hA with ⟨hAlen, hArow⟩
  rcases hB with ⟨hBlen, hBrow⟩
  induction r generalizing A B with
  | zero => cases A <;> cases B <;> simp_all [cMatAdd, WFMat]
  | succ r ih =>
    cases A with
    | nil => simp at hAlen
    | cons a as =>
      cases B with
      | nil => simp at hBlen
      | cons b bs =>
        simp only [List.length_cons, Nat.succ.injEq] at hAlen hBlen
        have htail := ih as bs hAlen (fun i => hArow i.succ) hBlen (fun i => hBrow i.succ)
        refine ⟨by simp [cMatAdd, htail.1], ?_⟩
        intro i
        cases i using Fin.cases with
        | zero => exact cVecAdd_length a b c (hArow 0) (hBrow 0)
        | succ i' => exact htail.2 i'

theorem toMat_cMatAdd {r c : Nat} (A B : CMat) (hA : WFMat r c A) (hB : WFMat r c B) :
    toMat r c (cMatAdd A B) = rMatAdd (toMat r c A) (toMat r c B) := by
  funext i j
  rcases i with ⟨idx, hidx⟩
  rcases hA with ⟨hAlen, hArow⟩
  rcases hB with ⟨hBlen, hBrow⟩
  induction r generalizing A B idx with
  | zero => omega
  | succ r ih =>
    cases A with
    | nil => simp at hAlen
    | cons a as =>
      cases B with
      | nil => simp at hBlen
      | cons b bs =>
        simp only [List.length_cons, Nat.succ.injEq] at hAlen hBlen
        cases idx with
        | zero => exact congrFun (toVec_cVecAdd a b (hArow 0) (hBrow 0)) j
        | succ k =>
          exact ih as bs k (by omega) hAlen (fun i => hArow i.succ) hBlen (fun i => hBrow i.succ)

theorem cMatTranspose_wf {k c : Nat} (B : CMat) (hB : WFMat k c B) :
    WFMat c k (cMatTranspose c B) := by
  refine ⟨by simp [cMatTranspose], ?_⟩
  intro j
  simp only [cMatTranspose]
  rw [list_getD_map _ _ _ (by simp [j.isLt]) 0 []]
  rw [list_getD_range c j.val j.isLt 0]
  simp [hB.1]

theorem toMat_cMatTranspose {k c : Nat} (B : CMat) (hB : WFMat k c B) (j : Fin c) (t : Fin k) :
    toMat c k (cMatTranspose c B) j t = toMat k c B t j := by
  simp only [toMat, cMatTranspose]
  rw [list_getD_map _ _ _ (by simp [j.isLt]) 0 []]
  rw [list_getD_range c j.val j.isLt 0]
  rw [list_getD_map _ _ _ (by rw [hB.1]; exact t.isLt) [] 0]

theorem cMatMul_wf {r k c : Nat} (A B : CMat) (hA : WFMat r k A) (hB : WFMat k c B) :
    WFMat r c (cMatMul c A B) := by
  have hBt := cMatTranspose_wf B hB
  refine ⟨by simp [cMatMul, hA.1], ?_⟩
  intro i
  simp only [cMatMul]
  rw [list_getD_map _ _ _ (by rw [hA.1]; exact i.isLt) [] []]
  simp [hBt.1]

theorem toMat_cMatMul {r k c : Nat} (A B : CMat) (hA : WFMat r k A) (hB : WFMat k c B) :
    toMat r c (cMatMul c A B) = rMatMul (toMat r k A) (toMat k c B) := by
  funext i j
  have hBt := cMatTranspose_wf B hB
  simp only [toMat, cMatMul, rMatMul]
  rw [list_getD_map _ _ _ (by rw [hA.1]; exact i.isLt) [] []]
  rw [list_getD_map _ _ _ (by rw [hBt.1]; exact j.isLt) [] 0]
  rw [cVecDot_eq (A.getD i.val []) ((cMatTranspose c B).getD j.val []) (hA.2 i) (hBt.2 j)]
  simp only [vecDot, toVec]
  apply finSum_congr; intro t
  have htr := toMat_cMatTranspose B hB j t
  simp only [toMat] at htr
  rw [htr]

theorem cMatId_wf (d : Nat) : WFMat d d (cMatId d) := by
  refine ⟨by simp [cMatId], ?_⟩
  intro i
  simp only [cMatId]
  rw [list_getD_map _ _ _ (by simp [i.isLt]) 0 []]
  simp

theorem toMat_cMatId (d : Nat) : toMat d d (cMatId d) = matId d := by
  funext i j
  simp only [toMat, cMatId, matId]
  rw [list_getD_map _ _ _ (by simp [i.isLt]) 0 []]
  rw [list_getD_range d i.val i.isLt 0]
  rw [list_getD_map _ _ _ (by simp [j.isLt]) 0 0]
  rw [list_getD_range d j.val j.isLt 0]
  by_cases h : i = j
  · subst h; simp
  · have hne : i.val ≠ j.val := fun hv => h (Fin.ext hv)
    simp [h, hne]

theorem cMatPow_wf {d : Nat} (M : CMat) (hM : WFMat d d M) (n : Nat) :
    WFMat d d (cMatPow d M n) := by
  induction n with
  | zero => exact cMatId_wf d
  | succ n ih => exact cMatMul_wf M (cMatPow d M n) hM ih

theorem toMat_cMatPow {d : Nat} (M : CMat) (hM : WFMat d d M) (n : Nat) :
    toMat d d (cMatPow d M n) = matPow (toMat d d M) n := by
  induction n with
  | zero => exact toMat_cMatId d
  | succ n ih =>
    simp only [cMatPow, matPow]
    rw [toMat_cMatMul M (cMatPow d M n) hM (cMatPow_wf M hM n), ih]

theorem cVecIter_length {d : Nat} (M : CMat) (v : CVec) (hM : WFMat d d M) (hv : v.length = d) (n : Nat) :
    (cVecIter M v n).length = d := by
  induction n with
  | zero => exact hv
  | succ n ih => exact cMatVecMul_length M (cVecIter M v n) hM

theorem toVec_cVecIter {d : Nat} (M : CMat) (v : CVec) (hM : WFMat d d M) (hv : v.length = d) (n : Nat) :
    toVec d (cVecIter M v n) = rMatVecMul (matPow (toMat d d M) n) (toVec d v) := by
  induction n with
  | zero =>
    simp only [cVecIter, matPow]
    exact (rMatVecMul_matId (toVec d v)).symm
  | succ n ih =>
    simp only [cVecIter, matPow]
    rw [toVec_cMatVecMul M (cVecIter M v n) hM (cVecIter_length M v hM hv n), ih, rMatVecMul_assoc]

theorem toVec_cVecMatMul {r c : Nat} (u : CVec) (A : CMat) (hu : u.length = r) (hA : WFMat r c A) :
    toVec c (cVecMatMul c u A) = vecRMatMul (toVec r u) (toMat r c A) := by
  have hAt := cMatTranspose_wf A hA
  funext j
  simp only [toVec, cVecMatMul, vecRMatMul]
  rw [list_getD_map _ _ _ (by rw [hAt.1]; exact j.isLt) [] 0]
  rw [cVecDot_eq u ((cMatTranspose c A).getD j.val []) hu (hAt.2 j)]
  simp only [vecDot, toVec]
  apply finSum_congr; intro i
  have htr := toMat_cMatTranspose A hA j i
  simp only [toMat] at htr ⊢
  rw [htr]

theorem cVecMatMul_length {c : Nat} (u : CVec) (A : CMat) :
    (cVecMatMul c u A).length = c := by
  simp [cVecMatMul, cMatTranspose]

theorem cVecIterLinComb_go_spec {d : Nat} (M : CMat) (hM : WFMat d d M)
    (cs : List Int) (cur acc : CVec) (hcur : cur.length = d) (hacc : acc.length = d) :
    (cVecIterLinComb.go M cur acc cs).length = d ∧
    toVec d (cVecIterLinComb.go M cur acc cs) =
      vecAdd (toVec d acc) (vecIterLinComb (toMat d d M) (toVec d cur) (toVec cs.length cs)) := by
  induction cs generalizing cur acc with
  | nil =>
    refine ⟨hacc, ?_⟩
    funext i
    simp [cVecIterLinComb.go, vecAdd, vecIterLinComb, finSum]
  | cons c rest ih =>
    simp only [cVecIterLinComb.go]
    have hcur' : (cMatVecMul M cur).length = d := cMatVecMul_length M cur hM
    have hsc : (cVecScale c cur).length = d := cVecScale_length c cur d hcur
    have hacc' : (cVecAdd acc (cVecScale c cur)).length = d := cVecAdd_length acc (cVecScale c cur) d hacc hsc
    obtain ⟨hlen, hvec⟩ := ih (cMatVecMul M cur) (cVecAdd acc (cVecScale c cur)) hcur' hacc'
    refine ⟨hlen, ?_⟩
    rw [hvec, toVec_cVecAdd acc (cVecScale c cur) hacc hsc, toVec_cVecScale c cur hcur,
        toVec_cMatVecMul M cur hM hcur]
    funext i
    simp only [vecAdd, vecScale, vecIterLinComb, List.length_cons]
    rw [← finSum_shift rest.length (fun j : Fin (rest.length + 1) =>
      toVec (rest.length + 1) (c :: rest) j * rMatVecMul (matPow (toMat d d M) j.val) (toVec d cur) i)]
    have h0 : toVec (rest.length + 1) (c :: rest) 0 *
        rMatVecMul (matPow (toMat d d M) (0 : Fin (rest.length + 1)).val) (toVec d cur) i = c * toVec d cur i := by
      simp only [toVec, Fin.val_zero, matPow, rMatVecMul_matId]
      rfl
    have htail : finSum rest.length (fun j =>
        toVec rest.length rest j *
          rMatVecMul (matPow (toMat d d M) j.val) (rMatVecMul (toMat d d M) (toVec d cur)) i) =
      finSum rest.length (fun j =>
        toVec (rest.length + 1) (c :: rest) j.succ *
          rMatVecMul (matPow (toMat d d M) j.succ.val) (toVec d cur) i) := by
      apply finSum_congr; intro j
      have hpow : rMatVecMul (matPow (toMat d d M) j.val) (rMatVecMul (toMat d d M) (toVec d cur)) =
          rMatVecMul (matPow (toMat d d M) (j.val + 1)) (toVec d cur) := by
        rw [← rMatVecMul_assoc, ← matPow_succ_right]
      rw [hpow]; rfl
    rw [h0, htail]
    omega

theorem cVecIterLinComb_spec {d : Nat} (M : CMat) (v : CVec) (cs : List Int)
    (hM : WFMat d d M) (hv : v.length = d) :
    (cVecIterLinComb d M v cs).length = d ∧
    toVec d (cVecIterLinComb d M v cs) =
      vecIterLinComb (toMat d d M) (toVec d v) (toVec cs.length cs) := by
  have hrep : (List.replicate d (0 : Int)).length = d := List.length_replicate
  obtain ⟨hlen, hvec⟩ := cVecIterLinComb_go_spec M hM cs v (List.replicate d 0) hv hrep
  refine ⟨hlen, ?_⟩
  simp only [cVecIterLinComb]
  rw [hvec]
  funext i
  simp only [vecAdd, toVec]
  have hz : (List.replicate d (0 : Int)).getD i.val 0 = 0 := by
    rw [list_getD_eq_getElem _ _ (by simp [i.isLt]) 0]
    simp
  rw [hz, Int.zero_add]

theorem cMatIterLinComb_go_spec {d : Nat} (M : CMat) (hM : WFMat d d M)
    (cs : List Int) (cur acc : CMat) (hcur : WFMat d d cur) (hacc : WFMat d d acc) :
    WFMat d d (cMatIterLinComb.go d M cur acc cs) ∧
    toMat d d (cMatIterLinComb.go d M cur acc cs) =
      rMatAdd (toMat d d acc) (rMatMul (matIterLinComb (toMat d d M) (toVec cs.length cs)) (toMat d d cur)) := by
  induction cs generalizing cur acc with
  | nil =>
    refine ⟨hacc, ?_⟩
    funext i j
    simp only [cMatIterLinComb.go, rMatAdd, rMatMul, matIterLinComb]
    rw [finSum_congr (g := fun _ => 0)]
    · rw [finSum_zero d, Int.add_zero]
    · intro t; simp [finSum]
  | cons c rest ih =>
    simp only [cMatIterLinComb.go]
    have hcur' := cMatMul_wf M cur hM hcur
    have hsc := cMatScale_wf c cur hcur
    have hacc' := cMatAdd_wf acc (cMatScale c cur) hacc hsc
    obtain ⟨hwf, hmat⟩ := ih (cMatMul d M cur) (cMatAdd acc (cMatScale c cur)) hcur' hacc'
    refine ⟨hwf, ?_⟩
    rw [hmat, toMat_cMatAdd acc (cMatScale c cur) hacc hsc, toMat_cMatScale c cur hcur,
        toMat_cMatMul M cur hM hcur]
    funext i j
    simp only [rMatAdd, rMatScale, rMatMul, matIterLinComb, List.length_cons]
    have hR : finSum d (fun s =>
        finSum (rest.length + 1) (fun t => toVec (rest.length + 1) (c :: rest) t * matPow (toMat d d M) t.val i s) *
          toMat d d cur s j) =
      c * toMat d d cur i j +
      finSum d (fun s =>
        finSum rest.length (fun t => toVec rest.length rest t * matPow (toMat d d M) t.val i s) *
          finSum d (fun u => toMat d d M s u * toMat d d cur u j)) := by
      have hsplit : ∀ s,
          finSum (rest.length + 1) (fun t => toVec (rest.length + 1) (c :: rest) t * matPow (toMat d d M) t.val i s) *
            toMat d d cur s j =
          (c * matId d i s) * toMat d d cur s j +
          finSum rest.length (fun t => toVec rest.length rest t * matPow (toMat d d M) (t.val + 1) i s) *
            toMat d d cur s j := by
        intro s
        rw [← finSum_shift rest.length (fun t : Fin (rest.length + 1) =>
          toVec (rest.length + 1) (c :: rest) t * matPow (toMat d d M) t.val i s)]
        rw [Int.add_mul]
        rfl
      rw [finSum_congr hsplit, finSum_add]
      congr 1
      · rw [finSum_congr (g := fun s => c * (matId d i s * toMat d d cur s j))]
        · rw [finSum_mul_left]
          have hmul := congrFun (congrFun (rMatMul_matId_left (toMat d d cur)) i) j
          simp only [rMatMul] at hmul
          rw [hmul]
        · intro s; exact Int.mul_assoc _ _ _
      · have hLHS : finSum d (fun s =>
            finSum rest.length (fun t => toVec rest.length rest t * matPow (toMat d d M) (t.val + 1) i s) *
              toMat d d cur s j) =
          finSum rest.length (fun t => toVec rest.length rest t *
            rMatMul (matPow (toMat d d M) (t.val + 1)) (toMat d d cur) i j) := by
          calc
            finSum d (fun s => finSum rest.length (fun t => toVec rest.length rest t * matPow (toMat d d M) (t.val + 1) i s) * toMat d d cur s j)
              = finSum d (fun s => finSum rest.length (fun t => (toVec rest.length rest t * matPow (toMat d d M) (t.val + 1) i s) * toMat d d cur s j)) := by
                  apply finSum_congr; intro s; rw [← finSum_mul_right]
            _ = finSum rest.length (fun t => finSum d (fun s => (toVec rest.length rest t * matPow (toMat d d M) (t.val + 1) i s) * toMat d d cur s j)) :=
                  finSum_swap d rest.length _
            _ = finSum rest.length (fun t => toVec rest.length rest t * finSum d (fun s => matPow (toMat d d M) (t.val + 1) i s * toMat d d cur s j)) := by
                  apply finSum_congr; intro t
                  rw [← finSum_mul_left]
                  apply finSum_congr; intro s; exact Int.mul_assoc _ _ _
        have hRHS : finSum d (fun s =>
            finSum rest.length (fun t => toVec rest.length rest t * matPow (toMat d d M) t.val i s) *
              finSum d (fun u => toMat d d M s u * toMat d d cur u j)) =
          finSum rest.length (fun t => toVec rest.length rest t *
            rMatMul (matPow (toMat d d M) t.val) (rMatMul (toMat d d M) (toMat d d cur)) i j) := by
          calc
            finSum d (fun s => finSum rest.length (fun t => toVec rest.length rest t * matPow (toMat d d M) t.val i s) * rMatMul (toMat d d M) (toMat d d cur) s j)
              = finSum d (fun s => finSum rest.length (fun t => (toVec rest.length rest t * matPow (toMat d d M) t.val i s) * rMatMul (toMat d d M) (toMat d d cur) s j)) := by
                  apply finSum_congr; intro s; rw [← finSum_mul_right]
            _ = finSum rest.length (fun t => finSum d (fun s => (toVec rest.length rest t * matPow (toMat d d M) t.val i s) * rMatMul (toMat d d M) (toMat d d cur) s j)) :=
                  finSum_swap d rest.length _
            _ = finSum rest.length (fun t => toVec rest.length rest t * finSum d (fun s => matPow (toMat d d M) t.val i s * rMatMul (toMat d d M) (toMat d d cur) s j)) := by
                  apply finSum_congr; intro t
                  rw [← finSum_mul_left]
                  apply finSum_congr; intro s; exact Int.mul_assoc _ _ _
        rw [hLHS, hRHS]
        apply finSum_congr; intro t
        rw [← rMatMul_assoc, ← matPow_succ_right]
    rw [hR]; omega

theorem cMatIterLinComb_spec {d : Nat} (M : CMat) (cs : List Int) (hM : WFMat d d M) :
    WFMat d d (cMatIterLinComb d M cs) ∧
    toMat d d (cMatIterLinComb d M cs) =
      matIterLinComb (toMat d d M) (toVec cs.length cs) := by
  have hzero : WFMat d d (List.replicate d (List.replicate d (0 : Int))) := by
    refine ⟨List.length_replicate, ?_⟩
    intro i
    rw [list_getD_eq_getElem _ _ (by simp [i.isLt]) []]
    simp
  obtain ⟨hwf, hmat⟩ := cMatIterLinComb_go_spec M hM cs (cMatId d) (List.replicate d (List.replicate d 0)) (cMatId_wf d) hzero
  refine ⟨hwf, ?_⟩
  simp only [cMatIterLinComb]
  rw [hmat, toMat_cMatId, rMatMul_matId_right]
  funext i j
  simp only [rMatAdd, toMat]
  have hz : ((List.replicate d (List.replicate d (0 : Int))).getD i.val []).getD j.val 0 = 0 := by
    rw [list_getD_eq_getElem _ _ (by simp [i.isLt]) []]
    simp only [List.getElem_replicate]
    rw [list_getD_eq_getElem _ _ (by simp [j.isLt]) 0]
    simp
  rw [hz, Int.zero_add]

theorem eq_toMat_of_eq {r c : Nat} {A B : CMat} (h : A == B) : toMat r c A = toMat r c B := by
  have heq : A = B := beq_iff_eq.mp h
  rw [heq]

theorem cVecAll_sound {d : Nat} {p : Int → Bool} {v : CVec}
    (hv : v.length = d) (h : v.all p = true) :
    ∀ i : Fin d, p (toVec d v i) = true := by
  intro i
  have hi : i.val < v.length := by omega
  simp only [toVec]
  rw [list_getD_eq_getElem v i.val hi 0]
  exact (List.all_eq_true.mp h) v[i.val] (List.getElem_mem hi)

theorem cMatAll_sound {r c : Nat} {p : Int → Bool} {M : CMat}
    (hM : WFMat r c M) (h : M.all (fun row => row.all p) = true) :
    ∀ (i : Fin r) (j : Fin c), p (toMat r c M i j) = true := by
  intro i j
  have hi : i.val < M.length := by rw [hM.1]; exact i.isLt
  have hrow : (M.getD i.val []).all p = true := by
    rw [list_getD_eq_getElem M i.val hi []]
    exact (List.all_eq_true.mp h) M[i.val] (List.getElem_mem hi)
  have hj : j.val < (M.getD i.val []).length := by rw [hM.2 i]; exact j.isLt
  simp only [toMat]
  rw [list_getD_eq_getElem (M.getD i.val []) j.val hj 0]
  exact (List.all_eq_true.mp hrow) (M.getD i.val [])[j.val] (List.getElem_mem hj)

theorem cCheckRange_sound {k : Nat} {p : Nat → Bool} (h : cCheckRange k p = true) :
    ∀ j : Fin k, p j.val = true := by
  intro j
  simp only [cCheckRange, List.all_eq_true] at h
  exact h j.val (List.mem_range.mpr j.isLt)

/-! ## Section 2: The Five Pure-Data Certificate Engines (CHKAE) & Soundness Meta-Theorems -/

/-! ### Engine 1: Full-Matrix Cayley-Hamilton & Two-Stage Quotient Annihilator Engine -/

theorem matAnn_matrix_sound (cert : MatAnnCert) (h : checkMatAnn cert = true) :
    matPow (toMat cert.d cert.d cert.M) cert.c.length =
      matIterLinComb (toMat cert.d cert.d cert.M) (toVec cert.c.length cert.c) := by
  simp only [checkMatAnn, Bool.and_eq_true] at h
  have hM := wfMat_of_bool h.1.1
  have heq := eq_toMat_of_eq (r := cert.d) (c := cert.d) h.2
  rw [toMat_cMatPow cert.M hM cert.c.length, (cMatIterLinComb_spec cert.M cert.c hM).2] at heq
  exact heq

theorem matAnn_sound (cert : MatAnnCert) (u v : Vec cert.d) (h : checkMatAnn cert = true) :
    ∀ n : Nat,
      obs (toMat cert.d cert.d cert.M) u v (n + cert.c.length) =
      finSum cert.c.length (fun j => toVec cert.c.length cert.c j * obs (toMat cert.d cert.d cert.M) u v (n + j.val)) := by
  have hm := matAnn_matrix_sound cert h
  have hkv : rMatVecMul (matPow (toMat cert.d cert.d cert.M) cert.c.length) v =
      vecIterLinComb (toMat cert.d cert.d cert.M) v (toVec cert.c.length cert.c) := by
    rw [hm, rMatVecMul_matIterLinComb]
  exact krylov_obs_recurrence (toMat cert.d cert.d cert.M) u v (toVec cert.c.length cert.c) hkv

private theorem checkQuotAnn_wf {cert : QuotAnnCert} (h : checkQuotAnn cert = true) :
    WFMat cert.d cert.d cert.M ∧ cert.u.length = cert.d ∧ cert.v.length = cert.d := by
  dsimp only [checkQuotAnn] at h
  simp only [Bool.and_eq_true, wfVecBool, beq_iff_eq] at h
  exact ⟨wfMat_of_bool h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩

theorem quotAnn_sound (cert : QuotAnnCert) (h : checkQuotAnn cert = true) :
    ∀ n : Nat,
      obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0 + cert.c.length) =
      finSum cert.c.length (fun j =>
        toVec cert.c.length cert.c j *
          obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0 + j.val)) := by
  obtain ⟨hM, hu, hv⟩ := checkQuotAnn_wf h
  dsimp only [checkQuotAnn] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hw_ann := h.2.1
  have hw_init := h.2.2
  let v0c := cVecIter cert.M cert.v cert.n0
  have hv0len : v0c.length = cert.d := cVecIter_length cert.M cert.v hM hv cert.n0
  have hv0eq : toVec cert.d v0c = rMatVecMul (matPow (toMat cert.d cert.d cert.M) cert.n0) (toVec cert.d cert.v) :=
    toVec_cVecIter cert.M cert.v hM hv cert.n0
  have hvk_len : (cVecIter cert.M v0c cert.c.length).length = cert.d :=
    cVecIter_length cert.M v0c hM hv0len cert.c.length
  obtain ⟨hlc_len, hlc_eq⟩ := cVecIterLinComb_spec cert.M v0c cert.c hM hv0len
  let wc := cVecSub (cVecIter cert.M v0c cert.c.length) (cVecIterLinComb cert.d cert.M v0c cert.c)
  have hwlen : wc.length = cert.d := cVecSub_length _ _ cert.d hvk_len hlc_len
  have hweq : toVec cert.d wc =
      vecSub (rMatVecMul (matPow (toMat cert.d cert.d cert.M) cert.c.length) (toVec cert.d v0c))
             (vecIterLinComb (toMat cert.d cert.d cert.M) (toVec cert.d v0c) (toVec cert.c.length cert.c)) := by
    rw [toVec_cVecSub _ _ hvk_len hlc_len, toVec_cVecIter cert.M v0c hM hv0len cert.c.length, hlc_eq]
  have hdef_ann :
      rMatVecMul (matPow (toMat cert.d cert.d cert.M) cert.r.length) (toVec cert.d wc) =
      vecIterLinComb (toMat cert.d cert.d cert.M) (toVec cert.d wc) (toVec cert.r.length cert.r) := by
    have heq := congrArg (toVec cert.d) hw_ann
    rw [toVec_cVecIter cert.M wc hM hwlen cert.r.length,
        (cVecIterLinComb_spec cert.M wc cert.r hM hwlen).2] at heq
    exact heq
  have hdef_init : ∀ j : Fin cert.r.length,
      obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d wc) j.val = 0 := by
    intro j
    have hj := cCheckRange_sound hw_init j
    simp only [beq_iff_eq] at hj
    simp only [obs]
    rw [← toVec_cVecIter cert.M wc hM hwlen j.val,
        ← cVecDot_eq cert.u (cVecIter cert.M wc j.val) hu (cVecIter_length cert.M wc hM hwlen j.val)]
    exact hj
  have hmain := quot_ann_obs_recurrence (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v)
    cert.n0 (toVec cert.c.length cert.c) (toVec cert.r.length cert.r)
  dsimp only at hmain
  rw [← hv0eq, ← hweq] at hmain
  exact hmain hdef_ann hdef_init

/-! ### Engine 2: Cross-Automaton / Closed-Form Identity Engine (`IdentityCert`) -/

theorem identity_sound (cert : IdentityCert) (h : checkIdentity cert = true) :
    ∀ n : Nat,
      cert.scale1 * obs (toMat cert.d1 cert.d1 cert.M1) (toVec cert.d1 cert.u1) (toVec cert.d1 cert.v1) (n + cert.off1) =
      cert.scale2 * obs (toMat cert.d2 cert.d2 cert.M2) (toVec cert.d2 cert.u2) (toVec cert.d2 cert.v2) (n + cert.off2) := by
  dsimp only [checkIdentity] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hq1, hq2⟩, hinit⟩ := h
  have hrec1 := quotAnn_sound ⟨cert.d1, cert.M1, cert.u1, cert.v1, cert.off1, cert.c, cert.r1⟩ hq1
  have hrec2 := quotAnn_sound ⟨cert.d2, cert.M2, cert.u2, cert.v2, cert.off2, cert.c, cert.r2⟩ hq2
  dsimp only at hrec1 hrec2
  obtain ⟨hM1, hu1, hv1⟩ := checkQuotAnn_wf hq1
  obtain ⟨hM2, hu2, hv2⟩ := checkQuotAnn_wf hq2
  let k := cert.c.length
  let M1t := toMat cert.d1 cert.d1 cert.M1
  let u1t := toVec cert.d1 cert.u1
  let v1t := toVec cert.d1 cert.v1
  let M2t := toMat cert.d2 cert.d2 cert.M2
  let u2t := toVec cert.d2 cert.u2
  let v2t := toVec cert.d2 cert.v2
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hlt : n < k
    · have hj := cCheckRange_sound hinit ⟨n, hlt⟩
      simp only [beq_iff_eq] at hj
      have ho1 : cVecDot cert.u1 (cVecIter cert.M1 cert.v1 (cert.off1 + n)) = obs M1t u1t v1t (n + cert.off1) := by
        rw [cVecDot_eq cert.u1 _ hu1 (cVecIter_length cert.M1 cert.v1 hM1 hv1 _),
            toVec_cVecIter cert.M1 cert.v1 hM1 hv1 _, Nat.add_comm]
        rfl
      have ho2 : cVecDot cert.u2 (cVecIter cert.M2 cert.v2 (cert.off2 + n)) = obs M2t u2t v2t (n + cert.off2) := by
        rw [cVecDot_eq cert.u2 _ hu2 (cVecIter_length cert.M2 cert.v2 hM2 hv2 _),
            toVec_cVecIter cert.M2 cert.v2 hM2 hv2 _, Nat.add_comm]
        rfl
      rw [← ho1, ← ho2]
      exact hj
    · have hge : cert.c.length ≤ n := Nat.le_of_not_lt hlt
      have hsplit : n + cert.off1 = (n - k) + cert.off1 + k := by dsimp only [k]; omega
      have hsplit2 : n + cert.off2 = (n - k) + cert.off2 + k := by dsimp only [k]; omega
      rw [hsplit, hsplit2, hrec1 (n - k), hrec2 (n - k), ← finSum_mul_left, ← finSum_mul_left]
      apply finSum_congr; intro j
      have hlt2 : (n - k) + j.val < n := by omega
      have hrec_ih := ih ((n - k) + j.val) hlt2
      have ha1 : (n - k) + cert.off1 + j.val = (n - k) + j.val + cert.off1 := by omega
      have ha2 : (n - k) + cert.off2 + j.val = (n - k) + j.val + cert.off2 := by omega
      rw [ha1, ha2]
      calc
        cert.scale1 * (toVec k cert.c j * obs M1t u1t v1t ((n - k) + j.val + cert.off1))
          = toVec k cert.c j * (cert.scale1 * obs M1t u1t v1t ((n - k) + j.val + cert.off1)) := by
              rw [← Int.mul_assoc, Int.mul_comm cert.scale1, Int.mul_assoc]
        _ = toVec k cert.c j * (cert.scale2 * obs M2t u2t v2t ((n - k) + j.val + cert.off2)) := by
              rw [hrec_ih]
        _ = cert.scale2 * (toVec k cert.c j * obs M2t u2t v2t ((n - k) + j.val + cert.off2)) := by
              rw [← Int.mul_assoc, Int.mul_comm (toVec k cert.c j) cert.scale2, Int.mul_assoc]

/-! ### Engine 3: Scaled Cayley-Hamilton `q`-adic Valuation & Odd-Part Periodicity Engine -/

theorem scaledCoeffs_length (q : Int) (c : List Int) :
    (scaledCoeffs q c).length = c.length := by
  simp [scaledCoeffs]

theorem scaledCoeffs_getD (q : Int) (c : List Int) (j : Nat) (hj : j < c.length) :
    (scaledCoeffs q c).getD j 0 = c.getD j 0 * q ^ (c.length - j) := by
  simp only [scaledCoeffs]
  rw [list_getD_map _ _ _ (by simp [hj]) 0 0]
  rw [list_getD_range c.length j hj 0]

theorem quotSeq_lt (c initQuot : List Int) {n : Nat} (h : n < c.length) :
    quotSeq c initQuot n = initQuot.getD n 0 := by
  rw [quotSeq]
  simp [h]

theorem quotSeq_step (c initQuot : List Int) (m : Nat) :
    quotSeq c initQuot (m + c.length) =
      finSum c.length (fun j => toVec c.length c j * quotSeq c initQuot (m + j.val)) := by
  rw [quotSeq]
  have hnot : ¬ (m + c.length < c.length) := by omega
  simp only [hnot, ↓reduceIte, Nat.add_sub_cancel]

theorem int_mod_finSum {k : Nat} {m0 : Int} (f g : Fin k → Int)
    (h : ∀ j, f j % m0 = g j % m0) :
    (finSum k f) % m0 = (finSum k g) % m0 := by
  induction k with
  | zero => simp [finSum]
  | succ k ih =>
    simp only [finSum]
    rw [Int.add_emod, ih (fun j => f j.castSucc) (fun j => g j.castSucc) (fun j => h j.castSucc),
        h (Fin.last k), ← Int.add_emod]

theorem finSum_eq_len {k1 k2 : Nat} (heq : k1 = k2) (f : Fin k1 → Int) (g : Fin k2 → Int)
    (h : ∀ (j : Nat) (h1 : j < k1) (h2 : j < k2), f ⟨j, h1⟩ = g ⟨j, h2⟩) :
    finSum k1 f = finSum k2 g := by
  subst heq
  apply finSum_congr
  intro j
  exact h j.val j.isLt j.isLt

theorem scaledVal_sound (cert : ScaledValCert) (h : checkScaledVal cert = true) :
    ∀ n : Nat,
      let t := quotSeq cert.c cert.initQuot n
      obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0) =
        cert.q ^ (n + cert.preShift) * t ∧
      t % cert.m0 = cert.periodTable.getD (n % cert.periodTable.length) 0 := by
  dsimp only [checkScaledVal] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_hqpos, _hm0pos⟩, hPpos⟩, _hinitlen⟩, hqAnn⟩, hinitObs⟩, hinitMod⟩, hperRec⟩ := h
  have hrec := quotAnn_sound ⟨cert.d, cert.M, cert.u, cert.v, cert.n0, scaledCoeffs cert.q cert.c, cert.r⟩ hqAnn
  obtain ⟨hM, hu, hv⟩ := checkQuotAnn_wf hqAnn
  let k := cert.c.length
  let P := cert.periodTable.length
  have hPpos' : 0 < P := by simpa using hPpos
  have hPart1 : ∀ n : Nat,
      obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0) =
        cert.q ^ (n + cert.preShift) * quotSeq cert.c cert.initQuot n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hlt : n < k
      · rw [quotSeq_lt cert.c cert.initQuot hlt]
        have hj := cCheckRange_sound hinitObs ⟨n, hlt⟩
        simp only [beq_iff_eq] at hj
        have ho : cVecDot cert.u (cVecIter cert.M cert.v (cert.n0 + n)) =
            obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0) := by
          rw [cVecDot_eq cert.u _ hu (cVecIter_length cert.M cert.v hM hv _),
              toVec_cVecIter cert.M cert.v hM hv _, Nat.add_comm]
          rfl
        rw [← ho]; exact hj
      · have hge : k ≤ n := Nat.le_of_not_lt hlt
        have hsp : n = (n - k) + k := (Nat.sub_add_cancel hge).symm
        have hlen := scaledCoeffs_length cert.q cert.c
        have hrec_n := hrec (n - k)
        have harg : (n - k) + cert.n0 + (scaledCoeffs cert.q cert.c).length = n + cert.n0 := by omega
        rw [harg] at hrec_n
        rw [hrec_n]
        have hcast : finSum (scaledCoeffs cert.q cert.c).length (fun j =>
            toVec (scaledCoeffs cert.q cert.c).length (scaledCoeffs cert.q cert.c) j *
              obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) ((n - k) + cert.n0 + j.val)) =
          finSum k (fun j =>
            (toVec k cert.c j * cert.q ^ (k - j.val)) *
              obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) ((n - k) + j.val + cert.n0)) := by
          apply finSum_eq_len hlen
          intro j _ hj2
          simp only [toVec]
          rw [scaledCoeffs_getD cert.q cert.c j hj2]
          have ha : (n - k) + cert.n0 + j = (n - k) + j + cert.n0 := by omega
          rw [ha]
        rw [hcast]
        have hqstep : quotSeq cert.c cert.initQuot n =
            finSum k (fun j => toVec k cert.c j * quotSeq cert.c cert.initQuot ((n - k) + j.val)) := by
          have hs := quotSeq_step cert.c cert.initQuot (n - k)
          rw [← hsp] at hs
          exact hs
        rw [hqstep, ← finSum_mul_left]
        apply finSum_congr; intro j
        have hlt2 : (n - k) + j.val < n := by omega
        rw [ih ((n - k) + j.val) hlt2]
        have hexp : (k - j.val) + ((n - k) + j.val + cert.preShift) = n + cert.preShift := by omega
        calc
          toVec k cert.c j * cert.q ^ (k - j.val) *
              (cert.q ^ ((n - k) + j.val + cert.preShift) * quotSeq cert.c cert.initQuot ((n - k) + j.val))
            = toVec k cert.c j * ((cert.q ^ (k - j.val) * cert.q ^ ((n - k) + j.val + cert.preShift)) *
                quotSeq cert.c cert.initQuot ((n - k) + j.val)) := by
                rw [Int.mul_assoc, Int.mul_assoc]
          _ = toVec k cert.c j * (cert.q ^ (n + cert.preShift) * quotSeq cert.c cert.initQuot ((n - k) + j.val)) := by
                rw [← Int.pow_add, hexp]
          _ = cert.q ^ (n + cert.preShift) * (toVec k cert.c j * quotSeq cert.c cert.initQuot ((n - k) + j.val)) := by
                rw [← Int.mul_assoc, Int.mul_comm (toVec k cert.c j), Int.mul_assoc]
  have hPart2 : ∀ n : Nat,
      quotSeq cert.c cert.initQuot n % cert.m0 = cert.periodTable.getD (n % P) 0 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hlt : n < k
      · rw [quotSeq_lt cert.c cert.initQuot hlt]
        have hj := cCheckRange_sound hinitMod ⟨n, hlt⟩
        simp only [beq_iff_eq] at hj
        exact hj
      · have hge : k ≤ n := Nat.le_of_not_lt hlt
        have hsp : n = (n - k) + k := (Nat.sub_add_cancel hge).symm
        have hqstep := quotSeq_step cert.c cert.initQuot (n - k)
        have hsp' : (n - k) + cert.c.length = n := by dsimp only [k]; omega
        rw [hsp'] at hqstep
        rw [hqstep]
        let t := (n - k) % P
        have ht : t < P := Nat.mod_lt (n - k) hPpos'
        have hper := cCheckRange_sound hperRec ⟨t, ht⟩
        simp only [beq_iff_eq] at hper
        have hmod_n : (t + k) % P = n % P := by
          have h1 : ((n - k) % P + k) % P = ((n - k) + k) % P := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          rw [h1, ← hsp]
        rw [← hmod_n, hper]
        apply int_mod_finSum
        intro j
        have hlt2 : (n - k) + j.val < n := by omega
        have hij := ih ((n - k) + j.val) hlt2
        have hmod_j : (t + j.val) % P = ((n - k) + j.val) % P := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        rw [hmod_j, ← hij]
        simp only [toVec]
        calc
          (cert.c.getD j.val 0 * quotSeq cert.c cert.initQuot ((n - k) + j.val)) % cert.m0
            = ((cert.c.getD j.val 0 % cert.m0) * (quotSeq cert.c cert.initQuot ((n - k) + j.val) % cert.m0)) % cert.m0 :=
                Int.mul_emod _ _ _
          _ = ((cert.c.getD j.val 0 % cert.m0) * ((quotSeq cert.c cert.initQuot ((n - k) + j.val) % cert.m0) % cert.m0)) % cert.m0 := by
                rw [Int.emod_emod]
          _ = (cert.c.getD j.val 0 * (quotSeq cert.c cert.initQuot ((n - k) + j.val) % cert.m0)) % cert.m0 :=
                (Int.mul_emod _ _ _).symm
  intro n
  exact ⟨hPart1 n, hPart2 n⟩

theorem scaledVal_exact_valuation (cert : ScaledValCert)
    (h : checkScaledVal cert = true)
    (hq_dvd : cert.q ∣ cert.m0)
    (hnonzero : cert.periodTable.all (fun a => a % cert.q != 0) = true) :
    ∀ n : Nat,
      cert.q ^ (n + cert.preShift) ∣
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0) ∧
      ¬ (cert.q ^ (n + cert.preShift + 1) ∣
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0)) := by
  have hmain := scaledVal_sound cert h
  dsimp only [checkScaledVal] at h
  simp only [Bool.and_eq_true] at h
  have hqpos : 0 < cert.q := by simpa using h.1.1.1.1.1.1.1
  have hPpos : 0 < cert.periodTable.length := by simpa using h.1.1.1.1.1.2
  intro n
  obtain ⟨heq, hmod⟩ := hmain n
  refine ⟨⟨quotSeq cert.c cert.initQuot n, heq⟩, ?_⟩
  intro hdvd
  rcases hdvd with ⟨w, hw⟩
  rw [heq, Int.pow_succ, Int.mul_assoc] at hw
  have hqpow_ne : cert.q ^ (n + cert.preShift) ≠ 0 := by
    have hpos : 0 < cert.q ^ (n + cert.preShift) := Int.pow_pos hqpos
    omega
  have ht_eq : quotSeq cert.c cert.initQuot n = cert.q * w :=
    Int.eq_of_mul_eq_mul_left hqpow_ne hw
  have ht_mod : quotSeq cert.c cert.initQuot n % cert.q = 0 := by
    rw [ht_eq]; exact Int.mul_emod_right cert.q w
  have hmodq : (quotSeq cert.c cert.initQuot n % cert.m0) % cert.q =
      quotSeq cert.c cert.initQuot n % cert.q := by
    rcases hq_dvd with ⟨s, hs⟩
    have hdiv := Int.emod_add_mul_ediv (quotSeq cert.c cert.initQuot n) cert.m0
    have h1 : (quotSeq cert.c cert.initQuot n % cert.m0 +
        cert.q * (s * (quotSeq cert.c cert.initQuot n / cert.m0))) % cert.q =
        (quotSeq cert.c cert.initQuot n % cert.m0) % cert.q := by
      rw [Int.add_emod, Int.mul_emod_right, Int.add_zero, Int.emod_emod]
    have h2 : quotSeq cert.c cert.initQuot n % cert.m0 +
        cert.q * (s * (quotSeq cert.c cert.initQuot n / cert.m0)) =
        quotSeq cert.c cert.initQuot n := by
      rw [← Int.mul_assoc, ← hs]; exact hdiv
    rw [h2] at h1
    exact h1.symm
  rw [hmod, ht_mod] at hmodq
  have hidx : n % cert.periodTable.length < cert.periodTable.length := Nat.mod_lt n hPpos
  have hne : cert.periodTable.getD (n % cert.periodTable.length) 0 % cert.q ≠ 0 := by
    rw [list_getD_eq_getElem _ _ hidx 0]
    have hall := (List.all_eq_true.mp hnonzero) cert.periodTable[n % cert.periodTable.length]
      (List.getElem_mem hidx)
    simpa [bne_iff_ne] using hall
  exact hne hmodq

/-! ### Engine 4: Positive-Multiplier Annihilator Sign & Rational Exponential Sandwich Engine -/

private theorem posBound_step_identity {d K : Nat} (Mt : Mat d) (ut vt : Vec d)
    (n0 : Nat) (tau alpha beta a b : Int) (C : Fin K → Int)
    (hrec : ∀ m : Nat,
      tau ^ (m + K) * obs Mt ut vt (m + K + n0) =
        finSum K (fun j => C j * (tau ^ (m + j.val) * obs Mt ut vt (m + j.val + n0)))) :
    let D : Nat → Int := fun n => alpha * tau ^ n * b ^ n * obs Mt ut vt (n + n0) + beta * a ^ n
    ∀ m : Nat,
      D (m + K) =
        finSum K (fun j => C j * b ^ (K - j.val) * D (m + j.val)) +
        a ^ m * (beta * (a ^ K - finSum K (fun j => C j * a ^ j.val * b ^ (K - j.val)))) := by
  intro D m
  simp only [D]
  have h1 : alpha * tau ^ (m + K) * b ^ (m + K) * obs Mt ut vt (m + K + n0) =
      finSum K (fun j => C j * b ^ (K - j.val) *
        (alpha * tau ^ (m + j.val) * b ^ (m + j.val) * obs Mt ut vt (m + j.val + n0))) := by
    have hr := hrec m
    have hL : alpha * tau ^ (m + K) * b ^ (m + K) * obs Mt ut vt (m + K + n0) =
        (alpha * b ^ (m + K)) * (tau ^ (m + K) * obs Mt ut vt (m + K + n0)) := by
      calc
        alpha * tau ^ (m + K) * b ^ (m + K) * obs Mt ut vt (m + K + n0)
          = (alpha * (tau ^ (m + K) * b ^ (m + K))) * obs Mt ut vt (m + K + n0) := by
              rw [Int.mul_assoc alpha]
        _ = (alpha * (b ^ (m + K) * tau ^ (m + K))) * obs Mt ut vt (m + K + n0) := by
              rw [Int.mul_comm (tau ^ (m + K)) (b ^ (m + K))]
        _ = (alpha * b ^ (m + K)) * (tau ^ (m + K) * obs Mt ut vt (m + K + n0)) := by
              rw [← Int.mul_assoc alpha, Int.mul_assoc]
    rw [hL, hr, ← finSum_mul_left]
    apply finSum_congr; intro j
    have hexp : (K - j.val) + (m + j.val) = m + K := by omega
    have hbpow : b ^ (m + K) = b ^ (K - j.val) * b ^ (m + j.val) := by
      rw [← Int.pow_add, hexp]
    rw [hbpow]
    have hA : alpha * (b ^ (K - j.val) * b ^ (m + j.val)) =
        b ^ (K - j.val) * (alpha * b ^ (m + j.val)) := by
      rw [← Int.mul_assoc, Int.mul_comm alpha (b ^ (K - j.val)), Int.mul_assoc]
    have hB : (alpha * b ^ (m + j.val)) * (tau ^ (m + j.val) * obs Mt ut vt (m + j.val + n0)) =
        alpha * tau ^ (m + j.val) * b ^ (m + j.val) * obs Mt ut vt (m + j.val + n0) := by
      calc
        (alpha * b ^ (m + j.val)) * (tau ^ (m + j.val) * obs Mt ut vt (m + j.val + n0))
          = alpha * (b ^ (m + j.val) * tau ^ (m + j.val)) * obs Mt ut vt (m + j.val + n0) := by
              rw [Int.mul_assoc, ← Int.mul_assoc (b ^ (m + j.val)), ← Int.mul_assoc]
        _ = alpha * (tau ^ (m + j.val) * b ^ (m + j.val)) * obs Mt ut vt (m + j.val + n0) := by
              rw [Int.mul_comm (b ^ (m + j.val)) (tau ^ (m + j.val))]
        _ = alpha * tau ^ (m + j.val) * b ^ (m + j.val) * obs Mt ut vt (m + j.val + n0) := by
              rw [← Int.mul_assoc alpha]
    calc
      alpha * (b ^ (K - j.val) * b ^ (m + j.val)) *
          (C j * (tau ^ (m + j.val) * obs Mt ut vt (m + j.val + n0)))
        = C j * (alpha * (b ^ (K - j.val) * b ^ (m + j.val)) *
            (tau ^ (m + j.val) * obs Mt ut vt (m + j.val + n0))) := by
            rw [← Int.mul_assoc, Int.mul_comm (alpha * (b ^ (K - j.val) * b ^ (m + j.val))) (C j), Int.mul_assoc]
      _ = C j * b ^ (K - j.val) *
            (alpha * tau ^ (m + j.val) * b ^ (m + j.val) * obs Mt ut vt (m + j.val + n0)) := by
            rw [hA, Int.mul_assoc (b ^ (K - j.val)), hB, ← Int.mul_assoc]
  have h2 : finSum K (fun j => C j * b ^ (K - j.val) * (beta * a ^ (m + j.val))) =
      a ^ m * (beta * finSum K (fun j => C j * a ^ j.val * b ^ (K - j.val))) := by
    rw [← finSum_mul_left, ← finSum_mul_left]
    apply finSum_congr; intro j
    rw [Int.pow_add]
    calc
      C j * b ^ (K - j.val) * (beta * (a ^ m * a ^ j.val))
        = (C j * b ^ (K - j.val)) * (a ^ m * (beta * a ^ j.val)) := by
            congr 1
            rw [← Int.mul_assoc beta, Int.mul_comm beta (a ^ m), Int.mul_assoc]
      _ = a ^ m * ((C j * b ^ (K - j.val)) * (beta * a ^ j.val)) := by
            rw [← Int.mul_assoc, Int.mul_comm (C j * b ^ (K - j.val)) (a ^ m), Int.mul_assoc]
      _ = a ^ m * (beta * (C j * a ^ j.val * b ^ (K - j.val))) := by
            congr 1
            calc
              C j * b ^ (K - j.val) * (beta * a ^ j.val)
                = beta * (C j * b ^ (K - j.val) * a ^ j.val) := by
                    rw [← Int.mul_assoc, Int.mul_comm (C j * b ^ (K - j.val)) beta, Int.mul_assoc]
              _ = beta * (C j * a ^ j.val * b ^ (K - j.val)) := by
                    congr 1
                    rw [Int.mul_assoc, Int.mul_comm (b ^ (K - j.val)) (a ^ j.val), ← Int.mul_assoc]
  have h3 : finSum K (fun j => C j * b ^ (K - j.val) *
      (alpha * tau ^ (m + j.val) * b ^ (m + j.val) * obs Mt ut vt (m + j.val + n0) + beta * a ^ (m + j.val))) =
    finSum K (fun j => C j * b ^ (K - j.val) *
      (alpha * tau ^ (m + j.val) * b ^ (m + j.val) * obs Mt ut vt (m + j.val + n0))) +
    finSum K (fun j => C j * b ^ (K - j.val) * (beta * a ^ (m + j.val))) := by
    rw [← finSum_add]
    apply finSum_congr; intro j; exact Int.mul_add _ _ _
  rw [h3, ← h1, h2, Int.mul_sub, Int.mul_sub, Int.pow_add a m K]
  have hba : beta * (a ^ m * a ^ K) = a ^ m * (beta * a ^ K) := by
    rw [← Int.mul_assoc, Int.mul_comm beta (a ^ m), Int.mul_assoc]
  rw [hba]
  omega

private theorem int_pow_ne_zero {a : Int} (ha : a ≠ 0) (n : Nat) : a ^ n ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Int.pow_succ]
    exact Int.mul_ne_zero ih ha

private theorem posBound_core_setup (cert : PosBoundCert) (h : checkPosBound cert = true) :
    (0 ≤ cert.a) ∧
    (1 ≤ cert.b) ∧
    (0 ≤ cert.beta * homogEval cert.C cert.a cert.b) ∧
    (∀ j : Fin cert.C.length, 0 ≤ toVec cert.C.length cert.C j) ∧
    WFMat cert.d cert.d cert.M ∧
    cert.u.length = cert.d ∧
    cert.v.length = cert.d ∧
    (∀ m : Nat,
      cert.tau ^ (m + cert.C.length) *
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (m + cert.C.length + cert.n0) =
      finSum cert.C.length (fun j =>
        toVec cert.C.length cert.C j *
          (cert.tau ^ (m + j.val) *
            obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (m + j.val + cert.n0)))) := by
  dsimp only [checkPosBound] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨htau_pm, ha_ge⟩, hb_ge⟩, hC_nonneg⟩, hqAnn⟩, hhomog⟩, _hinit⟩ := h
  have htau_ne : cert.tau ≠ 0 := by
    simp only [Bool.or_eq_true, beq_iff_eq] at htau_pm
    rcases htau_pm with h1 | h2 <;> omega
  have ha0 : 0 ≤ cert.a := by simpa using ha_ge
  have hb1 : 1 ≤ cert.b := by simpa using hb_ge
  have hhomog0 : 0 ≤ cert.beta * homogEval cert.C cert.a cert.b := by simpa using hhomog
  have hrec_raw := quotAnn_sound ⟨cert.d, cMatScale cert.tau cert.M, cert.u, cert.v, cert.n0, cert.C, cert.r⟩ hqAnn
  obtain ⟨hMtau_wf, hu, hv⟩ := checkQuotAnn_wf hqAnn
  have hM : WFMat cert.d cert.d cert.M := by
    have hlen : cert.M.length = cert.d := by simpa [cMatScale] using hMtau_wf.1
    refine ⟨hlen, ?_⟩
    intro i
    have hrow := hMtau_wf.2 i
    simp only [cMatScale] at hrow
    rw [list_getD_map _ _ _ (by rw [hlen]; exact i.isLt) [] []] at hrow
    simpa [List.length_map] using hrow
  have hC_ge : ∀ j : Fin cert.C.length, 0 ≤ toVec cert.C.length cert.C j := by
    intro j
    have hj := cVecAll_sound (d := cert.C.length) rfl hC_nonneg j
    simpa using hj
  refine ⟨ha0, hb1, hhomog0, hC_ge, hM, hu, hv, ?_⟩
  intro m
  have hr := hrec_raw m
  rw [toMat_cMatScale cert.tau cert.M hM] at hr
  simp only [obs_scale_mat] at hr
  have htau_pow_ne : cert.tau ^ cert.n0 ≠ 0 := int_pow_ne_zero htau_ne cert.n0
  apply Int.eq_of_mul_eq_mul_left htau_pow_ne
  have hL : cert.tau ^ cert.n0 *
      (cert.tau ^ (m + cert.C.length) *
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (m + cert.C.length + cert.n0)) =
      cert.tau ^ (m + cert.n0 + cert.C.length) *
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (m + cert.n0 + cert.C.length) := by
    rw [← Int.mul_assoc, ← Int.pow_add]
    have h1 : cert.n0 + (m + cert.C.length) = m + cert.n0 + cert.C.length := by omega
    have h2 : m + cert.C.length + cert.n0 = m + cert.n0 + cert.C.length := by omega
    rw [h1, h2]
  rw [hL, hr, ← finSum_mul_left]
  apply finSum_congr; intro j
  have h1 : cert.n0 + (m + j.val) = m + cert.n0 + j.val := by omega
  have h2 : m + j.val + cert.n0 = m + cert.n0 + j.val := by omega
  rw [h2]
  calc
    toVec cert.C.length cert.C j *
        (cert.tau ^ (m + cert.n0 + j.val) *
          obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (m + cert.n0 + j.val))
      = toVec cert.C.length cert.C j *
          ((cert.tau ^ cert.n0 * cert.tau ^ (m + j.val)) *
            obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (m + cert.n0 + j.val)) := by
          rw [← Int.pow_add, h1]
    _ = cert.tau ^ cert.n0 *
          (toVec cert.C.length cert.C j *
            (cert.tau ^ (m + j.val) *
              obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (m + cert.n0 + j.val))) := by
          rw [Int.mul_assoc (cert.tau ^ cert.n0), ← Int.mul_assoc (toVec cert.C.length cert.C j),
              Int.mul_comm (toVec cert.C.length cert.C j) (cert.tau ^ cert.n0), Int.mul_assoc]

theorem posBound_sound_ge (cert : PosBoundCert) (h : checkPosBound cert = true) :
    ∀ n : Nat,
      cert.alpha * cert.tau ^ n * cert.b ^ n *
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0) +
        cert.beta * cert.a ^ n ≥ 0 := by
  obtain ⟨ha0, hb1, hhomog0, hC_ge, hM, hu, hv, hrec⟩ := posBound_core_setup cert h
  dsimp only [checkPosBound] at h
  simp only [Bool.and_eq_true] at h
  have hinit_branch := h.2
  have hinit_ge : ∀ j : Fin cert.C.length,
      cert.alpha * cert.tau ^ j.val * cert.b ^ j.val *
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (j.val + cert.n0) +
        cert.beta * cert.a ^ j.val ≥ 0 := by
    intro j
    have ho : cVecDot cert.u (cVecIter cert.M cert.v (cert.n0 + j.val)) =
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (j.val + cert.n0) := by
      rw [cVecDot_eq cert.u _ hu (cVecIter_length cert.M cert.v hM hv _),
          toVec_cVecIter cert.M cert.v hM hv _, Nat.add_comm]
      rfl
    cases hst : cert.strict
    · simp only [hst, Bool.false_eq_true, ↓reduceIte] at hinit_branch
      have hj := cCheckRange_sound hinit_branch j
      rw [← ho]; simpa using hj
    · simp only [hst, ↓reduceIte, Bool.and_eq_true] at hinit_branch
      have hj := cCheckRange_sound hinit_branch.2 j
      rw [← ho]
      have hgt : cert.alpha * cert.tau ^ j.val * cert.b ^ j.val *
          cVecDot cert.u (cVecIter cert.M cert.v (cert.n0 + j.val)) + cert.beta * cert.a ^ j.val > 0 := by
        simpa using hj
      omega
  let K := cert.C.length
  have hstep := posBound_step_identity (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v)
    cert.n0 cert.tau cert.alpha cert.beta cert.a cert.b (toVec K cert.C) hrec
  dsimp only at hstep
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hlt : n < K
    · exact hinit_ge ⟨n, hlt⟩
    · have hge : K ≤ n := Nat.le_of_not_lt hlt
      have hsp : n = (n - K) + K := (Nat.sub_add_cancel hge).symm
      rw [hsp, hstep (n - K)]
      have hsum : 0 ≤ finSum K (fun j => toVec K cert.C j * cert.b ^ (K - j.val) *
          (cert.alpha * cert.tau ^ ((n - K) + j.val) * cert.b ^ ((n - K) + j.val) *
            obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) ((n - K) + j.val + cert.n0) +
            cert.beta * cert.a ^ ((n - K) + j.val))) := by
        apply finSum_nonneg; intro j
        have hlt2 : (n - K) + j.val < n := by omega
        have h3 : 0 ≤ toVec K cert.C j * cert.b ^ (K - j.val) :=
          Int.mul_nonneg (hC_ge j) (Int.pow_nonneg (by omega))
        exact Int.mul_nonneg h3 (ih ((n - K) + j.val) hlt2)
      have hrem : 0 ≤ cert.a ^ (n - K) * (cert.beta * homogEval cert.C cert.a cert.b) :=
        Int.mul_nonneg (Int.pow_nonneg ha0) hhomog0
      simp only [homogEval] at hrem
      dsimp only [K] at hsum hrem ⊢
      omega

theorem posBound_sound_gt (cert : PosBoundCert) (h : checkPosBound cert = true)
    (hstrict : cert.strict = true) :
    ∀ n : Nat,
      cert.alpha * cert.tau ^ n * cert.b ^ n *
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0) +
        cert.beta * cert.a ^ n > 0 := by
  obtain ⟨ha0, hb1, hhomog0, hC_ge, hM, hu, hv, hrec⟩ := posBound_core_setup cert h
  dsimp only [checkPosBound] at h
  simp only [hstrict, ↓reduceIte, Bool.and_eq_true] at h
  have hCsum_pos : 0 < finSum cert.C.length (fun j => toVec cert.C.length cert.C j) := by
    simpa using h.2.1
  have hinit_gt : ∀ j : Fin cert.C.length,
      cert.alpha * cert.tau ^ j.val * cert.b ^ j.val *
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (j.val + cert.n0) +
        cert.beta * cert.a ^ j.val > 0 := by
    intro j
    have ho : cVecDot cert.u (cVecIter cert.M cert.v (cert.n0 + j.val)) =
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (j.val + cert.n0) := by
      rw [cVecDot_eq cert.u _ hu (cVecIter_length cert.M cert.v hM hv _),
          toVec_cVecIter cert.M cert.v hM hv _, Nat.add_comm]
      rfl
    have hj := cCheckRange_sound h.2.2 j
    rw [← ho]; simpa using hj
  rcases exists_pos_of_finSum_pos hC_ge hCsum_pos with ⟨j0, hj0_pos⟩
  let K := cert.C.length
  have hstep := posBound_step_identity (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v)
    cert.n0 cert.tau cert.alpha cert.beta cert.a cert.b (toVec K cert.C) hrec
  dsimp only at hstep
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hlt : n < K
    · exact hinit_gt ⟨n, hlt⟩
    · have hge : K ≤ n := Nat.le_of_not_lt hlt
      have hsp : n = (n - K) + K := (Nat.sub_add_cancel hge).symm
      rw [hsp, hstep (n - K)]
      have hsum : 0 < finSum K (fun j => toVec K cert.C j * cert.b ^ (K - j.val) *
          (cert.alpha * cert.tau ^ ((n - K) + j.val) * cert.b ^ ((n - K) + j.val) *
            obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) ((n - K) + j.val + cert.n0) +
            cert.beta * cert.a ^ ((n - K) + j.val))) := by
        apply finSum_pos_of_nonneg_of_exists_pos
        · intro j
          have hlt2 : (n - K) + j.val < n := by omega
          have h3 : 0 ≤ toVec K cert.C j * cert.b ^ (K - j.val) :=
            Int.mul_nonneg (hC_ge j) (Int.pow_nonneg (by omega))
          have hih := ih ((n - K) + j.val) hlt2
          exact Int.mul_nonneg h3 (by omega)
        · refine ⟨j0, ?_⟩
          have hlt2 : (n - K) + j0.val < n := by omega
          have hbpos : 0 < cert.b ^ (K - j0.val) := Int.pow_pos (by omega)
          have h3 : 0 < toVec K cert.C j0 * cert.b ^ (K - j0.val) := Int.mul_pos hj0_pos hbpos
          exact Int.mul_pos h3 (ih ((n - K) + j0.val) hlt2)
      have hrem : 0 ≤ cert.a ^ (n - K) * (cert.beta * homogEval cert.C cert.a cert.b) :=
        Int.mul_nonneg (Int.pow_nonneg ha0) hhomog0
      simp only [homogEval] at hrem
      dsimp only [K] at hsum hrem ⊢
      omega

/-! ### Engine 5: Scaled Integer Perron-Cone Intertwining Engine (`ConeCert`) -/

theorem cone_intertwine_pow {d m : Nat} (D : Int) (M : Mat d) (G : RMat d m) (A : Mat m)
    (h : rMatScale D (rMatMul M G) = rMatMul G A) (n : Nat) :
    rMatScale (D ^ n) (rMatMul (matPow M n) G) = rMatMul G (matPow A n) := by
  induction n with
  | zero =>
    funext i j
    simp [matPow, rMatScale, rMatMul_matId_left, rMatMul_matId_right]
  | succ n ih =>
    simp only [matPow]
    calc
      rMatScale (D ^ (n + 1)) (rMatMul (rMatMul M (matPow M n)) G)
        = rMatScale (D * D ^ n) (rMatMul M (rMatMul (matPow M n) G)) := by
            rw [Int.pow_succ, Int.mul_comm (D ^ n) D, rMatMul_assoc]
      _ = rMatMul (rMatScale D M) (rMatScale (D ^ n) (rMatMul (matPow M n) G)) := by
            rw [rMatScale_mul_left, rMatScale_mul_right]
            funext i j; simp only [rMatScale]; exact Int.mul_assoc _ _ _
      _ = rMatMul (rMatScale D M) (rMatMul G (matPow A n)) := by rw [ih]
      _ = rMatMul (rMatScale D (rMatMul M G)) (matPow A n) := by
            rw [← rMatMul_assoc, rMatScale_mul_left]
      _ = rMatMul (rMatMul G A) (matPow A n) := by rw [h]
      _ = rMatMul G (rMatMul A (matPow A n)) := rMatMul_assoc G A (matPow A n)

theorem cone_nonneg_vec_iter {m : Nat} (A : Mat m) (hA : ∀ i j, 0 ≤ A i j)
    (y : Vec m) (hy : ∀ i, 0 ≤ y i) (n : Nat) :
    ∀ i, 0 ≤ rMatVecMul (matPow A n) y i := by
  induction n with
  | zero =>
    intro i
    simp only [matPow, rMatVecMul_matId]
    exact hy i
  | succ n ih =>
    intro i
    simp only [matPow]
    rw [rMatVecMul_assoc]
    simp only [rMatVecMul]
    apply finSum_nonneg; intro j
    exact Int.mul_nonneg (hA i j) (ih j)

theorem cone_sum_ge_of_colsum {m : Nat} (A : Mat m)
    (hcol : ∀ j : Fin m, 1 ≤ finSum m (fun i => A i j))
    (y : Vec m) (hy : ∀ j, 0 ≤ y j) :
    finSum m y ≤ finSum m (rMatVecMul A y) := by
  change finSum m y ≤ finSum m (fun i => finSum m (fun j => A i j * y j))
  rw [finSum_swap m m (fun i j => A i j * y j)]
  apply finSum_le_finSum; intro j
  rw [finSum_mul_right]
  have h1 : 1 * y j ≤ finSum m (fun i => A i j) * y j :=
    Int.mul_le_mul_of_nonneg_right (hcol j) (hy j)
  omega

theorem cone_pos_and_bound_sound (cert : ConeCert) (h : checkCone cert = true) :
    (∀ n : Nat,
      obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0) > 0) ∧
    (∀ n : Nat,
      cert.D ^ n * obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0) ≥
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) cert.n0 * cert.rateNum ^ n) := by
  dsimp only [checkCone] at h
  simp only [Bool.and_eq_true, wfVecBool, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hM_b, hu⟩, hv⟩, hG_b⟩, hA_b⟩, hy0⟩, hDpos⟩, hD0pos⟩, hrate0⟩, hA_nn⟩, hy0_nn⟩, hy0_sum⟩, huG_pos⟩, hA_col⟩, hinter⟩, hinit⟩, hperron⟩ := h
  have hM := wfMat_of_bool hM_b
  have hG := wfMat_of_bool hG_b
  have hA := wfMat_of_bool hA_b
  have hDpos' : 0 < cert.D := by simpa using hDpos
  have hD0pos' : 0 < cert.D0 := by simpa using hD0pos
  have hrate0' : 0 ≤ cert.rateNum := by simpa using hrate0
  let Mt := toMat cert.d cert.d cert.M
  let ut := toVec cert.d cert.u
  let vt := toVec cert.d cert.v
  let Gt := toMat cert.d cert.m cert.G
  let At := toMat cert.m cert.m cert.A
  let y0t := toVec cert.m cert.y0
  have hA_ge : ∀ i j, 0 ≤ At i j := fun i j => by
    have h1 := cMatAll_sound hA hA_nn i j; simpa using h1
  have hy0_ge : ∀ i, 0 ≤ y0t i := fun i => by
    have h1 := cVecAll_sound hy0 hy0_nn i; simpa using h1
  have hy0_sum_pos : 0 < finSum cert.m y0t := by simpa using hy0_sum
  have huG_len : (cVecMatMul cert.m cert.u cert.G).length = cert.m := cVecMatMul_length cert.u cert.G
  have huG_eq : toVec cert.m (cVecMatMul cert.m cert.u cert.G) = vecRMatMul ut Gt :=
    toVec_cVecMatMul cert.u cert.G hu hG
  have huG_gt : ∀ j : Fin cert.m, 0 < vecRMatMul ut Gt j := by
    intro j
    rw [← huG_eq]
    have h1 := cVecAll_sound huG_len huG_pos j
    simpa using h1
  have hcol_ge : ∀ j : Fin cert.m, 1 ≤ finSum cert.m (fun i => At i j) := by
    intro j
    have hAt_wf := cMatTranspose_wf cert.A hA
    have hj_lt : j.val < (cMatTranspose cert.m cert.A).length := by rw [hAt_wf.1]; exact j.isLt
    have hrow := (List.all_eq_true.mp hA_col) ((cMatTranspose cert.m cert.A)[j.val]) (List.getElem_mem hj_lt)
    have hrow' : 1 ≤ finSum cert.m (fun i => toVec cert.m ((cMatTranspose cert.m cert.A).getD j.val []) i) := by
      rw [list_getD_eq_getElem _ _ hj_lt []]
      simpa using hrow
    rw [finSum_congr (g := fun i => toVec cert.m ((cMatTranspose cert.m cert.A).getD j.val []) i)]
    · exact hrow'
    · intro i
      exact (toMat_cMatTranspose cert.A hA j i).symm
  have hinter_mat : rMatScale cert.D (rMatMul Mt Gt) = rMatMul Gt At := by
    have heq := congrArg (toMat cert.d cert.m) hinter
    rw [toMat_cMatScale cert.D _ (cMatMul_wf cert.M cert.G hM hG),
        toMat_cMatMul cert.M cert.G hM hG,
        toMat_cMatMul cert.G cert.A hG hA] at heq
    exact heq
  have hinit_vec : vecScale cert.D0 (rMatVecMul (matPow Mt cert.n0) vt) = rMatVecMul Gt y0t := by
    have heq := congrArg (toVec cert.d) hinit
    rw [toVec_cVecScale cert.D0 _ (cVecIter_length cert.M cert.v hM hv cert.n0),
        toVec_cVecIter cert.M cert.v hM hv cert.n0,
        toVec_cMatVecMul cert.G cert.y0 hG hy0] at heq
    exact heq
  have hobs_id : ∀ n : Nat,
      cert.D ^ n * (cert.D0 * obs Mt ut vt (n + cert.n0)) =
        vecDot (vecRMatMul ut Gt) (rMatVecMul (matPow At n) y0t) := by
    intro n
    calc
      cert.D ^ n * (cert.D0 * obs Mt ut vt (n + cert.n0))
        = vecDot ut (vecScale (cert.D ^ n) (rMatVecMul (matPow Mt n) (vecScale cert.D0 (rMatVecMul (matPow Mt cert.n0) vt)))) := by
            simp only [obs]
            rw [matPow_add, rMatVecMul_assoc, rMatVecMul_scale, vecDot_scale_right, vecDot_scale_right]
      _ = vecDot ut (vecScale (cert.D ^ n) (rMatVecMul (matPow Mt n) (rMatVecMul Gt y0t))) := by rw [hinit_vec]
      _ = vecDot ut (rMatVecMul (rMatScale (cert.D ^ n) (rMatMul (matPow Mt n) Gt)) y0t) := by
            rw [← rMatVecMul_assoc, rMatScale_vecMul]
      _ = vecDot ut (rMatVecMul (rMatMul Gt (matPow At n)) y0t) := by
            rw [cone_intertwine_pow cert.D Mt Gt At hinter_mat n]
      _ = vecDot (vecRMatMul ut Gt) (rMatVecMul (matPow At n) y0t) := by
            rw [rMatVecMul_assoc, vecDot_rMatVecMul]
  have hsum_pos : ∀ n : Nat, finSum cert.m y0t ≤ finSum cert.m (rMatVecMul (matPow At n) y0t) := by
    intro n
    induction n with
    | zero =>
      simp only [matPow, rMatVecMul_matId]
      exact Int.le_refl _
    | succ n ih =>
      simp only [matPow, rMatVecMul_assoc]
      have hge := cone_nonneg_vec_iter At hA_ge y0t hy0_ge n
      have hstep := cone_sum_ge_of_colsum At hcol_ge (rMatVecMul (matPow At n) y0t) hge
      omega
  have hPart1 : ∀ n : Nat, obs Mt ut vt (n + cert.n0) > 0 := by
    intro n
    have hnn := cone_nonneg_vec_iter At hA_ge y0t hy0_ge n
    have hspos : 0 < finSum cert.m (rMatVecMul (matPow At n) y0t) := by
      have h1 := hsum_pos n; omega
    rcases exists_pos_of_finSum_pos hnn hspos with ⟨j0, hj0⟩
    have hdot_pos : 0 < vecDot (vecRMatMul ut Gt) (rMatVecMul (matPow At n) y0t) := by
      simp only [vecDot]
      apply finSum_pos_of_nonneg_of_exists_pos
      · intro j
        exact Int.mul_nonneg (by have := huG_gt j; omega) (hnn j)
      · exact ⟨j0, Int.mul_pos (huG_gt j0) hj0⟩
    rw [← hobs_id n, ← Int.mul_assoc] at hdot_pos
    exact int_pos_of_mul_pos_left (Int.mul_pos (Int.pow_pos hDpos') hD0pos') hdot_pos
  have hperron_vec : ∀ j : Fin cert.m,
      cert.rateNum * vecRMatMul ut Gt j ≤ vecRMatMul (vecRMatMul ut Gt) At j := by
    intro j
    have hj := cCheckRange_sound hperron j
    have huGA_eq : toVec cert.m (cVecMatMul cert.m (cVecMatMul cert.m cert.u cert.G) cert.A) =
        vecRMatMul (vecRMatMul ut Gt) At := by
      rw [toVec_cVecMatMul _ cert.A huG_len hA, huG_eq]
    have hL : (cVecMatMul cert.m (cVecMatMul cert.m cert.u cert.G) cert.A).getD j.val 0 =
        vecRMatMul (vecRMatMul ut Gt) At j := congrFun huGA_eq j
    have hR : (cVecMatMul cert.m cert.u cert.G).getD j.val 0 = vecRMatMul ut Gt j :=
      congrFun huG_eq j
    rw [hL, hR] at hj
    simpa using hj
  have hPart2 : ∀ n : Nat,
      cert.D ^ n * obs Mt ut vt (n + cert.n0) ≥ obs Mt ut vt cert.n0 * cert.rateNum ^ n := by
    have hdot_ge : ∀ n : Nat,
        vecDot (vecRMatMul ut Gt) y0t * cert.rateNum ^ n ≤
          vecDot (vecRMatMul ut Gt) (rMatVecMul (matPow At n) y0t) := by
      intro n
      induction n with
      | zero => simp [matPow, rMatVecMul_matId]
      | succ n ih =>
        simp only [matPow, rMatVecMul_assoc]
        rw [vecDot_rMatVecMul]
        have hnn := cone_nonneg_vec_iter At hA_ge y0t hy0_ge n
        have hstep : vecDot (vecScale cert.rateNum (vecRMatMul ut Gt)) (rMatVecMul (matPow At n) y0t) ≤
            vecDot (vecRMatMul (vecRMatMul ut Gt) At) (rMatVecMul (matPow At n) y0t) := by
          simp only [vecDot, vecScale]
          apply finSum_le_finSum; intro j
          exact Int.mul_le_mul_of_nonneg_right (hperron_vec j) (hnn j)
        have hsc : vecDot (vecScale cert.rateNum (vecRMatMul ut Gt)) (rMatVecMul (matPow At n) y0t) =
            cert.rateNum * vecDot (vecRMatMul ut Gt) (rMatVecMul (matPow At n) y0t) := by
          simp only [vecDot, vecScale]
          rw [← finSum_mul_left]
          apply finSum_congr; intro j; exact Int.mul_assoc _ _ _
        rw [hsc] at hstep
        have hmul : cert.rateNum * (vecDot (vecRMatMul ut Gt) y0t * cert.rateNum ^ n) ≤
            cert.rateNum * vecDot (vecRMatMul ut Gt) (rMatVecMul (matPow At n) y0t) :=
          Int.mul_le_mul_of_nonneg_left ih hrate0'
        have hpow : vecDot (vecRMatMul ut Gt) y0t * cert.rateNum ^ (n + 1) =
            cert.rateNum * (vecDot (vecRMatMul ut Gt) y0t * cert.rateNum ^ n) := by
          rw [Int.pow_succ, ← Int.mul_assoc, Int.mul_comm (vecDot (vecRMatMul ut Gt) y0t * cert.rateNum ^ n) cert.rateNum]
        omega
    intro n
    have h0 := hobs_id 0
    simp only [Int.pow_zero, Int.one_mul, Nat.zero_add, matPow, rMatVecMul_matId] at h0
    have hn := hobs_id n
    have hge := hdot_ge n
    rw [← h0, ← hn] at hge
    have hL : cert.D0 * (obs Mt ut vt cert.n0 * cert.rateNum ^ n) =
        cert.D0 * obs Mt ut vt cert.n0 * cert.rateNum ^ n := (Int.mul_assoc _ _ _).symm
    have hR : cert.D0 * (cert.D ^ n * obs Mt ut vt (n + cert.n0)) =
        cert.D ^ n * (cert.D0 * obs Mt ut vt (n + cert.n0)) := by
      rw [← Int.mul_assoc, Int.mul_comm cert.D0 (cert.D ^ n), Int.mul_assoc]
    rw [← hL, ← hR] at hge
    exact int_le_of_mul_le_left hD0pos' hge
  exact ⟨hPart1, hPart2⟩

/-! ## Section 3: Pure-Silicon Bit-Level Primitives & Exact Transfer-Matrix Semantic Bridges -/

theorem popcountAux_congr (n f1 f2 : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    popcountAux f1 n = popcountAux f2 n := by
  induction n using Nat.strongRecOn generalizing f1 f2 with
  | ind n ih =>
    cases n with
    | zero => cases f1 <;> cases f2 <;> simp [popcountAux]
    | succ m =>
      cases f1 with
      | zero => omega
      | succ f1' =>
        cases f2 with
        | zero => omega
        | succ f2' =>
          simp only [popcountAux, Nat.succ_ne_zero, ↓reduceIte]
          rw [ih ((m + 1) / 2) (by omega) f1' f2' (by omega) (by omega)]

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_bit (q b : Nat) (hb : b < 2) : popcount (2 * q + b) = b + popcount q := by
  by_cases h0 : 2 * q + b = 0
  · have hq : q = 0 := by omega
    have hb0 : b = 0 := by omega
    subst hq; subst hb0; rfl
  · simp only [popcount]
    rw [popcountAux_congr (2 * q + b) (2 * q + b) ((2 * q + b) + 1) (by omega) (by omega)]
    simp only [popcountAux, h0, ↓reduceIte]
    have hmod : (2 * q + b) % 2 = b := by omega
    have hdiv : (2 * q + b) / 2 = q := by omega
    rw [hmod, hdiv, popcountAux_congr q (2 * q + b) q (by omega) (by omega)]

theorem popcount_two_mul (q : Nat) : popcount (2 * q) = popcount q := by
  have h := popcount_bit q 0 (by omega)
  simpa using h

private theorem nat_testBit_zero_eq (n : Nat) : n.testBit 0 = decide (n % 2 = 1) := by
  simp only [Nat.testBit, Nat.shiftRight_zero]
  cases h : (n % 2 == 1)
  · have hne : n % 2 ≠ 1 := by simpa [beq_iff_eq] using h
    simp [hne]
  · have heq : n % 2 = 1 := beq_iff_eq.mp h
    simp [heq]

private theorem nat_xor_mod2 (a b : Nat) : (a ^^^ b) % 2 = (a % 2 + b % 2) % 2 := by
  have h := Nat.testBit_xor a b 0
  rw [nat_testBit_zero_eq, nat_testBit_zero_eq, nat_testBit_zero_eq] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hx : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hx with hx | hx <;>
    simp_all

private theorem nat_and_mod2 (a b : Nat) : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
  have h := Nat.testBit_and a b 0
  rw [nat_testBit_zero_eq, nat_testBit_zero_eq, nat_testBit_zero_eq] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hx : (a &&& b) % 2 = 0 ∨ (a &&& b) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hx with hx | hx <;>
    simp_all

theorem popcount_xor_mod2 (a b : Nat) :
    popcount (a ^^^ b) % 2 = (popcount a + popcount b) % 2 := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha; simp [popcount_zero]
    · have ha_div : a / 2 < a := by omega
      have hdiv : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
        rw [← Nat.shiftRight_eq_div_pow _ 1, ← Nat.shiftRight_eq_div_pow _ 1,
            ← Nat.shiftRight_eq_div_pow _ 1, Nat.shiftRight_xor_distrib]
      have hmod := nat_xor_mod2 a b
      have hpa : popcount a = a % 2 + popcount (a / 2) := by
        have h := popcount_bit (a / 2) (a % 2) (by omega)
        have heq : 2 * (a / 2) + a % 2 = a := by omega
        rw [heq] at h; exact h
      have hpb : popcount b = b % 2 + popcount (b / 2) := by
        have h := popcount_bit (b / 2) (b % 2) (by omega)
        have heq : 2 * (b / 2) + b % 2 = b := by omega
        rw [heq] at h; exact h
      have hpx : popcount (a ^^^ b) = (a ^^^ b) % 2 + popcount ((a ^^^ b) / 2) := by
        have h := popcount_bit ((a ^^^ b) / 2) ((a ^^^ b) % 2) (by omega)
        have heq : 2 * ((a ^^^ b) / 2) + (a ^^^ b) % 2 = a ^^^ b := by omega
        rw [heq] at h; exact h
      have hih := ih (a / 2) ha_div (b / 2)
      rw [hpx, hdiv, hpa, hpb]
      omega

theorem clmulAux_congr (a b f1 f2 : Nat) (h1 : b ≤ f1) (h2 : b ≤ f2) :
    clmulAux f1 a b = clmulAux f2 a b := by
  induction b using Nat.strongRecOn generalizing f1 f2 with
  | ind b ih =>
    cases b with
    | zero => cases f1 <;> cases f2 <;> simp [clmulAux]
    | succ m =>
      cases f1 with
      | zero => omega
      | succ f1' =>
        cases f2 with
        | zero => omega
        | succ f2' =>
          simp only [clmulAux, Nat.succ_ne_zero, ↓reduceIte]
          rw [ih ((m + 1) / 2) (by omega) f1' f2' (by omega) (by omega)]

theorem clmul_eq_step (a b : Nat) :
    clmul a b = if b = 0 then 0 else (if b % 2 = 1 then a else 0) ^^^ (2 * clmul a (b / 2)) := by
  by_cases hb : b = 0
  · subst hb; rfl
  · simp only [clmul, hb, ↓reduceIte]
    rw [clmulAux_congr a b b (b + 1) (by omega) (by omega)]
    simp only [clmulAux, hb, ↓reduceIte]
    rw [clmulAux_congr a (b / 2) b (b / 2) (by omega) (by omega)]

theorem popcount_clmul_mod2 (a b : Nat) :
    popcount (clmul a b) % 2 = (popcount a * popcount b) % 2 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    rw [clmul_eq_step]
    by_cases hb : b = 0
    · subst hb; simp [popcount_zero]
    · simp only [hb, ↓reduceIte]
      have hlt : b / 2 < b := by omega
      have hih := ih (b / 2) hlt
      rw [popcount_xor_mod2, popcount_two_mul]
      have hpb : popcount b = b % 2 + popcount (b / 2) := by
        have h := popcount_bit (b / 2) (b % 2) (by omega)
        have heq : 2 * (b / 2) + b % 2 = b := by omega
        rw [heq] at h; exact h
      rw [hpb]
      by_cases hodd : b % 2 = 1
      · simp only [hodd, ↓reduceIte]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · have hev : b % 2 = 0 := by omega
        simp only [hev, Nat.zero_add]
        have hne : (0 : Nat) ≠ 1 := by decide
        simp only [hne, ↓reduceIte, popcount_zero, Nat.zero_add]
        omega

theorem pm1_congr {a b : Nat} (h : a % 2 = b % 2) : pm1 a = pm1 b := by
  simp only [pm1, h]

theorem pm1_add (a b : Nat) : pm1 (a + b) = pm1 a * pm1 b := by
  simp only [pm1]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hab : (a + b) % 2 = 0 := by omega
    simp [ha, hb, hab]
  · have hab : (a + b) % 2 = 1 := by omega
    simp [ha, hb, hab]
  · have hab : (a + b) % 2 = 1 := by omega
    simp [ha, hb, hab]
  · have hab : (a + b) % 2 = 0 := by omega
    simp [ha, hb, hab]

theorem noAdjOnes_bit (q b : Nat) (hb : b < 2) :
    noAdjOnes (2 * q + b) = (noAdjOnes q && !(b == 1 && q % 2 == 1)) := by
  simp only [noAdjOnes]
  have hsr : (2 * q + b) >>> 1 = q := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  rw [hsr]
  have hdiv : ((2 * q + b) &&& q) / 2 = q &&& (q >>> 1) := by
    rw [← Nat.shiftRight_eq_div_pow _ 1, Nat.shiftRight_and_distrib, hsr]
  have hmod : ((2 * q + b) &&& q) % 2 = b &&& (q % 2) := by
    rw [nat_and_mod2]
    have hm : (2 * q + b) % 2 = b := by omega
    rw [hm]
  have hzero : ((2 * q + b) &&& q) = 0 ↔ (b &&& (q % 2) = 0 ∧ q &&& (q >>> 1) = 0) := by
    rw [← hdiv, ← hmod]; omega
  have hb_cases : b = 0 ∨ b = 1 := by omega
  have hq_cases : q % 2 = 0 ∨ q % 2 = 1 := by omega
  cases h : (q &&& (q >>> 1) == 0)
  · simp only [Bool.false_and]
    have hne : q &&& (q >>> 1) ≠ 0 := by simpa [beq_iff_eq] using h
    have hne2 : (2 * q + b) &&& q ≠ 0 := fun hz => hne (hzero.mp hz).2
    simpa [beq_iff_eq] using hne2
  · simp only [Bool.true_and]
    have hq0 : q &&& (q >>> 1) = 0 := beq_iff_eq.mp h
    rcases hb_cases with rfl | rfl <;> rcases hq_cases with hq2 | hq2
    · have hz : (2 * q + 0) &&& q = 0 := hzero.mpr ⟨by simp [hq2], hq0⟩
      simp only [Nat.add_zero] at hz
      simp [hq2, hz]
    · have hz : (2 * q + 0) &&& q = 0 := hzero.mpr ⟨by simp [hq2], hq0⟩
      simp only [Nat.add_zero] at hz
      simp [hq2, hz]
    · have hz : (2 * q + 1) &&& q = 0 := hzero.mpr ⟨by simp [hq2], hq0⟩
      simp [hq2, hz]
    · have hne : (2 * q + 1) &&& q ≠ 0 := by
        intro hz
        have h1 := (hzero.mp hz).1
        rw [hq2] at h1
        exact absurd h1 (by decide)
      simp [hq2, hne]

theorem sumRange_congr {N : Nat} {f g : Nat → Int} (h : ∀ x < N, f x = g x) :
    sumRange N f = sumRange N g := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange]
    rw [ih (fun x hx => h x (by omega)), h n (by omega)]

theorem sumRange_add (N : Nat) (f g : Nat → Int) :
    sumRange N (fun x => f x + g x) = sumRange N f + sumRange N g := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange]
    rw [ih]; omega

theorem sumRange_mul_left (N : Nat) (a : Int) (f : Nat → Int) :
    sumRange N (fun x => a * f x) = a * sumRange N f := by
  induction N with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange]
    rw [ih, Int.mul_add]

/-- Universal LSB-splitting law for sums over `[0, 2*N)`. -/
theorem sumRange_two_mul (N : Nat) (f : Nat → Int) :
    sumRange (2 * N) f = sumRange N (fun q => f (2 * q) + f (2 * q + 1)) := by
  induction N with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h2]
    simp only [sumRange]
    rw [ih]
    omega

/-- Universal row-vector transfer-matrix semantic lifting lemma. -/
theorem obs_eq_of_row_step {d : Nat} (M : Mat d) (u : Vec d) (F : Nat → Fin d → Int)
    (h0 : ∀ c, F 0 c = u c)
    (hstep : ∀ n c, F (n + 1) c = finSum d (fun c' => F n c' * M c' c))
    (c0 : Fin d) :
    ∀ n : Nat, F n c0 = obs M u (fun i => if i = c0 then 1 else 0) n := by
  have hall : ∀ n : Nat, F n = vecRMatMul u (matPow M n) := by
    intro n
    induction n with
    | zero =>
      funext c
      rw [h0 c]
      simp only [vecRMatMul, matPow, matId]
      rw [finSum_congr (g := fun i => if i = c then u c else 0)]
      · exact (finSum_single_eq d c (u c)).symm
      · intro i
        by_cases h : i = c
        · subst h; simp
        · simp [h]
    | succ n ih =>
      funext c
      rw [hstep n c, ih]
      simp only [vecRMatMul, matPow_succ_right, rMatMul]
      calc
        finSum d (fun c' => finSum d (fun i => u i * matPow M n i c') * M c' c)
          = finSum d (fun c' => finSum d (fun i => (u i * matPow M n i c') * M c' c)) := by
              apply finSum_congr; intro c'; rw [← finSum_mul_right]
        _ = finSum d (fun i => finSum d (fun c' => (u i * matPow M n i c') * M c' c)) :=
              finSum_swap d d _
        _ = finSum d (fun i => u i * finSum d (fun c' => matPow M n i c' * M c' c)) := by
              apply finSum_congr; intro i
              rw [← finSum_mul_left]
              apply finSum_congr; intro c'; exact Int.mul_assoc _ _ _
  intro n
  unfold obs
  rw [vecDot_rMatVecMul, ← hall n]
  unfold vecDot
  rw [finSum_congr (g := fun i => if i = c0 then F n c0 else 0)]
  · exact (finSum_single_eq d c0 (F n c0)).symm
  · intro i
    by_cases h : i = c0
    · subst h; simp
    · simp [h]

/-! ### Semantic Bridge 1: `k`-Way Binary Carry-Parity Sum `C_k(n)` -/

theorem sumBinom_congr {k : Nat} {f g : Nat → Int} (h : ∀ s ≤ k, f s = g s) :
    sumBinom k f = sumBinom k g := by
  induction k generalizing f g with
  | zero => exact h 0 (by omega)
  | succ k ih =>
    simp only [sumBinom]
    rw [ih (fun s hs => h s (by omega)), ih (fun s hs => h (s + 1) (by omega))]

theorem sumBinom_add (k : Nat) (f g : Nat → Int) :
    sumBinom k (fun s => f s + g s) = sumBinom k f + sumBinom k g := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
    simp only [sumBinom]
    rw [ih, ih]; omega

theorem sumBinom_mul_left (k : Nat) (a : Int) (f : Nat → Int) :
    sumBinom k (fun s => a * f s) = a * sumBinom k f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    simp only [sumBinom]
    rw [ih, ih, Int.mul_add]

theorem sumRange_sumBinom_swap (N k : Nat) (f : Nat → Nat → Int) :
    sumRange N (fun q => sumBinom k (fun s => f q s)) =
    sumBinom k (fun s => sumRange N (fun q => f q s)) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    simp only [sumBinom]
    rw [sumRange_add, ih, ih]

theorem carrySumKWith_step (k n c : Nat) :
    carrySumKWith k (n + 1) c = pm1 c * sumBinom k (fun s => carrySumKWith k n ((c + s) / 2)) := by
  induction k generalizing c with
  | zero =>
    simp only [carrySumKWith, sumBinom, Nat.add_zero]
    have hpc : popcount c = c % 2 + popcount (c / 2) := by
      have h := popcount_bit (c / 2) (c % 2) (by omega)
      have heq : 2 * (c / 2) + c % 2 = c := by omega
      rw [heq] at h; exact h
    rw [hpc, pm1_add]
    have hpm : pm1 (c % 2) = pm1 c := by apply pm1_congr; omega
    rw [hpm]
  | succ k ih =>
    simp only [carrySumKWith]
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, sumRange_two_mul]
    have hbody : ∀ q,
        pm1 (popcount (2 * q)) * carrySumKWith k (n + 1) (2 * q + c) +
        pm1 (popcount (2 * q + 1)) * carrySumKWith k (n + 1) (2 * q + 1 + c) =
        pm1 c * (
          pm1 (popcount q) * sumBinom k (fun s => carrySumKWith k n (q + (c + s) / 2)) +
          pm1 (popcount q) * sumBinom k (fun s => carrySumKWith k n (q + (c + (s + 1)) / 2))) := by
      intro q
      rw [ih (2 * q + c), ih (2 * q + 1 + c)]
      have hp0 : popcount (2 * q) = popcount q := popcount_two_mul q
      have hp1 : popcount (2 * q + 1) = 1 + popcount q := popcount_bit q 1 (by omega)
      have hpm0 : pm1 (2 * q + c) = pm1 c := by apply pm1_congr; omega
      have hpm1 : pm1 (1 + popcount q) * pm1 (2 * q + 1 + c) = pm1 (popcount q) * pm1 c := by
        rw [← pm1_add, ← pm1_add]
        apply pm1_congr; omega
      have hsb0 : sumBinom k (fun s => carrySumKWith k n ((2 * q + c + s) / 2)) =
          sumBinom k (fun s => carrySumKWith k n (q + (c + s) / 2)) :=
        sumBinom_congr (fun s _ => congrArg (carrySumKWith k n) (by omega))
      have hsb1 : sumBinom k (fun s => carrySumKWith k n ((2 * q + 1 + c + s) / 2)) =
          sumBinom k (fun s => carrySumKWith k n (q + (c + (s + 1)) / 2)) :=
        sumBinom_congr (fun s _ => congrArg (carrySumKWith k n) (by omega))
      rw [hp0, hp1, hpm0, hsb0, hsb1]
      rw [← Int.mul_assoc (pm1 (1 + popcount q)), hpm1, ← Int.mul_assoc (pm1 (popcount q))]
      have hc1 : pm1 (popcount q) * pm1 c = pm1 c * pm1 (popcount q) := Int.mul_comm _ _
      rw [hc1, Int.mul_assoc, Int.mul_assoc, Int.mul_add]
    rw [sumRange_congr (fun q _ => hbody q), sumRange_mul_left, sumRange_add]
    have hswap : ∀ f : Nat → Nat → Int,
        sumRange (2 ^ n) (fun q => pm1 (popcount q) * sumBinom k (fun s => f q s)) =
        sumBinom k (fun s => sumRange (2 ^ n) (fun q => pm1 (popcount q) * f q s)) := by
      intro f
      rw [sumRange_congr (fun q _ => (sumBinom_mul_left k (pm1 (popcount q)) (fun s => f q s)).symm)]
      exact sumRange_sumBinom_swap (2 ^ n) k (fun q s => pm1 (popcount q) * f q s)
    rw [hswap (fun q s => carrySumKWith k n (q + (c + s) / 2)),
        hswap (fun q s => carrySumKWith k n (q + (c + (s + 1)) / 2))]
    rfl

theorem carrySumKWith_zero (k c : Nat) : carrySumKWith k 0 c = pm1 (popcount c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp [carrySumKWith, sumRange, popcount_zero, pm1, ih]

theorem carrySumK_step_mat (k : Nat) (_hk : 1 ≤ k) (n : Nat) (c : Fin k) :
    carrySumKWith k (n + 1) c.val =
      finSum k (fun c' => carrySumKWith k n c'.val * carryMat k c' c) := by
  rw [carrySumKWith_step]
  simp only [carryMat]
  have h1 : finSum k (fun c' => carrySumKWith k n c'.val * (pm1 c.val * sumBinom k (fun s => if (c.val + s) / 2 = c'.val then 1 else 0))) =
      pm1 c.val * finSum k (fun c' => sumBinom k (fun s => if (c.val + s) / 2 = c'.val then carrySumKWith k n c'.val else 0)) := by
    rw [← finSum_mul_left]
    apply finSum_congr; intro c'
    rw [← Int.mul_assoc, Int.mul_comm (carrySumKWith k n c'.val) (pm1 c.val), Int.mul_assoc]
    congr 1
    rw [← sumBinom_mul_left]
    apply sumBinom_congr; intro s _
    by_cases h : (c.val + s) / 2 = c'.val <;> simp [h]
  rw [h1]
  congr 1
  have hswap : ∀ (m : Nat) (g : Fin k → Nat → Int),
      finSum k (fun c' => sumBinom m (fun s => g c' s)) =
      sumBinom m (fun s => finSum k (fun c' => g c' s)) := by
    intro m
    induction m with
    | zero => intro g; rfl
    | succ m ihm =>
      intro g
      simp only [sumBinom]
      rw [finSum_add, ihm, ihm]
  rw [hswap k]
  apply sumBinom_congr; intro s hs
  have hlt : (c.val + s) / 2 < k := by omega
  let idx : Fin k := ⟨(c.val + s) / 2, hlt⟩
  rw [finSum_congr (g := fun c' => if c' = idx then carrySumKWith k n idx.val else 0)]
  · exact (finSum_single_eq k idx (carrySumKWith k n idx.val)).symm
  · intro c'
    by_cases h : c' = idx
    · subst h; simp [idx]
    · have hne : (c.val + s) / 2 ≠ c'.val := fun heq => h (Fin.ext heq.symm)
      simp [h, hne]

/-- Exact semantic bridge for ALL `k ≥ 1` and ALL `n : Nat`. -/
theorem carrySumK_eq_obs (k : Nat) (hk : 1 ≤ k) (n : Nat) :
    carrySumK k n =
      obs (carryMat k) (fun c : Fin k => pm1 (popcount c.val))
          (fun c : Fin k => if c = ⟨0, hk⟩ then 1 else 0) n :=
  obs_eq_of_row_step (carryMat k) (fun c : Fin k => pm1 (popcount c.val))
    (fun m c => carrySumKWith k m c.val)
    (fun c => carrySumKWith_zero k c.val)
    (fun m c => carrySumK_step_mat k hk m c)
    ⟨0, hk⟩ n

/-! ### Semantic Bridge 2: Carried-vs-Carryless Parity Correlation `K_c(n)` -/

theorem K_corr_eq_with (c n : Nat) : K_corr c n = K_corrWith c n 0 := by
  simp only [K_corr, K_corrWith]
  apply sumRange_congr; intro x _
  rw [Nat.add_zero]
  apply pm1_congr
  have hcl := popcount_clmul_mod2 c x
  omega

theorem K_corrWith_zero (c q : Nat) : K_corrWith c 0 q = pm1 (popcount q) := by
  simp [K_corrWith, sumRange, popcount_zero]

theorem K_corrWith_step (c n q : Nat) :
    K_corrWith c (n + 1) q =
      pm1 (q % 2) * K_corrWith c n (q / 2) +
      pm1 ((q + c) % 2 + popcount c) * K_corrWith c n ((q + c) / 2) := by
  simp only [K_corrWith]
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow, sumRange_two_mul, sumRange_add, ← sumRange_mul_left, ← sumRange_mul_left]
  congr 1
  · apply sumRange_congr; intro x _
    have hmul : c * (2 * x) = 2 * (c * x) := by rw [← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]
    have h1 : c * (2 * x) + q = 2 * (c * x + q / 2) + q % 2 := by rw [hmul]; omega
    rw [h1, popcount_bit (c * x + q / 2) (q % 2) (by omega), popcount_two_mul, ← pm1_add]
    apply pm1_congr; omega
  · apply sumRange_congr; intro x _
    have hmul : c * (2 * x + 1) = 2 * (c * x) + c := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]
    have h1 : c * (2 * x + 1) + q = 2 * (c * x + (q + c) / 2) + (q + c) % 2 := by rw [hmul]; omega
    rw [h1, popcount_bit (c * x + (q + c) / 2) ((q + c) % 2) (by omega),
        popcount_bit x 1 (by omega), Nat.mul_add, Nat.mul_one, ← pm1_add]
    apply pm1_congr; omega

theorem K_corr_eq_obs (c : Nat) (hc : 1 ≤ c) (n : Nat) :
    K_corr c n =
      obs (kMat c) (fun q : Fin c => pm1 (popcount q.val))
          (fun q : Fin c => if q = ⟨0, hc⟩ then 1 else 0) n := by
  rw [K_corr_eq_with]
  apply obs_eq_of_row_step (kMat c) (fun q : Fin c => pm1 (popcount q.val))
    (fun m q => K_corrWith c m q.val)
    (fun q => K_corrWith_zero c q.val)
    ?_ ⟨0, hc⟩ n
  intro m q
  rw [K_corrWith_step]
  simp only [kMat]
  rw [finSum_congr (g := fun q' =>
        K_corrWith c m q'.val * (if q.val / 2 = q'.val then pm1 (q.val % 2) else 0) +
        K_corrWith c m q'.val * (if (q.val + c) / 2 = q'.val then pm1 ((q.val + c) % 2 + popcount c) else 0))]
  · rw [finSum_add]
    have h1lt : q.val / 2 < c := by omega
    have h2lt : (q.val + c) / 2 < c := by omega
    let q1 : Fin c := ⟨q.val / 2, h1lt⟩
    let q2 : Fin c := ⟨(q.val + c) / 2, h2lt⟩
    congr 1
    · rw [finSum_congr (g := fun q' => if q' = q1 then pm1 (q.val % 2) * K_corrWith c m q1.val else 0)]
      · exact (finSum_single_eq c q1 _).symm
      · intro q'
        by_cases h : q' = q1
        · subst h; simp [q1, Int.mul_comm]
        · have hne : q.val / 2 ≠ q'.val := fun heq => h (Fin.ext heq.symm)
          simp [h, hne]
    · rw [finSum_congr (g := fun q' => if q' = q2 then pm1 ((q.val + c) % 2 + popcount c) * K_corrWith c m q2.val else 0)]
      · exact (finSum_single_eq c q2 _).symm
      · intro q'
        by_cases h : q' = q2
        · subst h; simp [q2, Int.mul_comm]
        · have hne : (q.val + c) / 2 ≠ q'.val := fun heq => h (Fin.ext heq.symm)
          simp [h, hne]
  · intro q'; exact Int.mul_add _ _ _

/-! ### Semantic Bridge 3: Zeckendorf (No-Adjacent-1s) Carried Multiply Parity `Z_c(n)` -/

theorem Z_corr_eq_with (c n : Nat) : Z_corr c n = Z_corrWith c n 0 0 := by
  simp only [Z_corr, Z_corrWith]
  apply sumRange_congr; intro y _
  simp [Nat.add_zero]

theorem Z_corrWith_zero (c q lb : Nat) : Z_corrWith c 0 q lb = pm1 (popcount q) := by
  have hno : noAdjOnes 0 = true := by decide
  simp [Z_corrWith, sumRange, hno]

theorem Z_corrWith_step (c n q lb : Nat) (hlb : lb < 2) :
    Z_corrWith c (n + 1) q lb =
      pm1 (q % 2) * Z_corrWith c n (q / 2) 0 +
      (if lb = 0 then pm1 ((q + c) % 2) * Z_corrWith c n ((q + c) / 2) 1 else 0) := by
  simp only [Z_corrWith]
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow, sumRange_two_mul, sumRange_add, ← sumRange_mul_left]
  congr 1
  · apply sumRange_congr; intro y _
    have hna := noAdjOnes_bit y 0 (by omega)
    have hmod0 : (2 * y) % 2 = 0 := by omega
    simp only [Nat.add_zero] at hna
    rw [hna, hmod0]
    have hb_simp : ((noAdjOnes y && !(0 == 1 && y % 2 == 1)) && !(lb == 1 && 0 == 1)) =
        (noAdjOnes y && !(0 == 1 && y % 2 == 1)) := by
      cases noAdjOnes y <;> simp
    rw [hb_simp]
    cases (noAdjOnes y && !(0 == 1 && y % 2 == 1))
    · simp
    · simp only [↓reduceIte]
      have hmul : c * (2 * y) = 2 * (c * y) := by rw [← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]
      have h1 : c * (2 * y) + q = 2 * (c * y + q / 2) + q % 2 := by rw [hmul]; omega
      rw [h1, popcount_bit (c * y + q / 2) (q % 2) (by omega), pm1_add]
  · by_cases hlb0 : lb = 0
    · subst hlb0
      simp only [↓reduceIte, ← sumRange_mul_left]
      apply sumRange_congr; intro y _
      have hna := noAdjOnes_bit y 1 (by omega)
      rw [hna]
      have h0ne1 : (0 == 1) = false := rfl
      simp only [h0ne1, Bool.false_and, Bool.not_false, Bool.and_true]
      cases (noAdjOnes y && !(1 == 1 && y % 2 == 1))
      · simp
      · simp only [↓reduceIte]
        have hmul : c * (2 * y + 1) = 2 * (c * y) + c := by
          rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]
        have h1 : c * (2 * y + 1) + q = 2 * (c * y + (q + c) / 2) + (q + c) % 2 := by rw [hmul]; omega
        rw [h1, popcount_bit (c * y + (q + c) / 2) ((q + c) % 2) (by omega), pm1_add]
    · have hlb1 : lb = 1 := by omega
      subst hlb1
      simp only [Nat.one_ne_zero, ↓reduceIte]
      have hz : ∀ y, (if noAdjOnes (2 * y + 1) && !(1 == 1 && (2 * y + 1) % 2 == 1)
          then pm1 (popcount (c * (2 * y + 1) + q)) else 0) = 0 := by
        intro y
        have hm1 : (2 * y + 1) % 2 = 1 := by omega
        simp [hm1]
      rw [sumRange_congr (fun y _ => hz y)]
      clear hz
      induction (2 ^ n) with
      | zero => rfl
      | succ m ihm => simp [sumRange, ihm]

theorem Z_corr_eq_obs (c : Nat) (hc : 1 ≤ c) (n : Nat) :
    Z_corr c n =
      obs (zMat c) (fun idx : Fin (2 * c) => pm1 (popcount (idx.val / 2)))
          (fun idx : Fin (2 * c) => if idx = ⟨0, by omega⟩ then 1 else 0) n := by
  rw [Z_corr_eq_with]
  have hmain := obs_eq_of_row_step (zMat c) (fun idx : Fin (2 * c) => pm1 (popcount (idx.val / 2)))
    (fun m idx => Z_corrWith c m (idx.val / 2) (idx.val % 2))
    (fun idx => Z_corrWith_zero c (idx.val / 2) (idx.val % 2))
    ?_ ⟨0, by omega⟩ n
  · simpa using hmain
  · intro m idx
    rw [Z_corrWith_step c m (idx.val / 2) (idx.val % 2) (by omega)]
    simp only [zMat]
    rw [finSum_congr (g := fun idx' =>
          Z_corrWith c m (idx'.val / 2) (idx'.val % 2) *
            (if 2 * (idx.val / 2 / 2) = idx'.val then pm1 (idx.val / 2 % 2) else 0) +
          Z_corrWith c m (idx'.val / 2) (idx'.val % 2) *
            (if idx.val % 2 = 0 ∧ 2 * ((idx.val / 2 + c) / 2) + 1 = idx'.val then pm1 ((idx.val / 2 + c) % 2) else 0))]
    · rw [finSum_add]
      have h1lt : 2 * (idx.val / 2 / 2) < 2 * c := by omega
      have h2lt : 2 * ((idx.val / 2 + c) / 2) + 1 < 2 * c := by omega
      let i1 : Fin (2 * c) := ⟨2 * (idx.val / 2 / 2), h1lt⟩
      let i2 : Fin (2 * c) := ⟨2 * ((idx.val / 2 + c) / 2) + 1, h2lt⟩
      congr 1
      · rw [finSum_congr (g := fun idx' => if idx' = i1 then pm1 (idx.val / 2 % 2) * Z_corrWith c m (idx.val / 2 / 2) 0 else 0)]
        · exact (finSum_single_eq (2 * c) i1 _).symm
        · intro idx'
          by_cases h : idx' = i1
          · subst h
            have hd : (2 * (idx.val / 2 / 2)) / 2 = idx.val / 2 / 2 := by omega
            have hm : (2 * (idx.val / 2 / 2)) % 2 = 0 := by omega
            simp [i1, hd, hm, Int.mul_comm]
          · have hne : 2 * (idx.val / 2 / 2) ≠ idx'.val := fun heq => h (Fin.ext heq.symm)
            simp [h, hne]
      · by_cases hlb : idx.val % 2 = 0
        · simp only [hlb, ↓reduceIte, true_and]
          rw [finSum_congr (g := fun idx' => if idx' = i2 then pm1 ((idx.val / 2 + c) % 2) * Z_corrWith c m ((idx.val / 2 + c) / 2) 1 else 0)]
          · exact (finSum_single_eq (2 * c) i2 _).symm
          · intro idx'
            by_cases h : idx' = i2
            · subst h
              have hd : (2 * ((idx.val / 2 + c) / 2) + 1) / 2 = (idx.val / 2 + c) / 2 := by omega
              have hm : (2 * ((idx.val / 2 + c) / 2) + 1) % 2 = 1 := by omega
              simp [i2, hd, hm, Int.mul_comm]
            · have hne : 2 * ((idx.val / 2 + c) / 2) + 1 ≠ idx'.val := fun heq => h (Fin.ext heq.symm)
              simp [h, hne]
        · simp only [hlb, ↓reduceIte, false_and, Int.mul_zero]
          exact (finSum_zero (2 * c)).symm
    · intro idx'; exact Int.mul_add _ _ _

/-! ## Section 4: Concrete Pure-Data Certificates & Novel Infinite Binary Theorems -/

private theorem eq_mat_of_forall {d : Nat} {A B : Mat d} (h : ∀ i j : Fin d, A i j = B i j) : A = B := by
  funext i j; exact h i j

private theorem eq_vec_of_forall {d : Nat} {u v : Vec d} (h : ∀ i : Fin d, u i = v i) : u = v := by
  funext i; exact h i

theorem carrySum3_eq_obs (n : Nat) :
    carrySumK 3 n = obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n := by
  rw [carrySumK_eq_obs 3 (by omega) n]
  have hM : carryMat 3 = toMat 3 3 M_C3 := eq_mat_of_forall (by decide)
  have hu : (fun c : Fin 3 => pm1 (popcount c.val)) = toVec 3 u_C3 := eq_vec_of_forall (by decide)
  have hv : (fun c : Fin 3 => if c = ⟨0, by omega⟩ then (1 : Int) else 0) = toVec 3 v_C3 := eq_vec_of_forall (by decide)
  rw [hM, hu, hv]

theorem carrySum4_eq_obs (n : Nat) :
    carrySumK 4 n = obs (toMat 4 4 M_C4) (toVec 4 u_C4) (toVec 4 v_C4) n := by
  rw [carrySumK_eq_obs 4 (by omega) n]
  have hM : carryMat 4 = toMat 4 4 M_C4 := eq_mat_of_forall (by decide)
  have hu : (fun c : Fin 4 => pm1 (popcount c.val)) = toVec 4 u_C4 := eq_vec_of_forall (by decide)
  have hv : (fun c : Fin 4 => if c = ⟨0, by omega⟩ then (1 : Int) else 0) = toVec 4 v_C4 := eq_vec_of_forall (by decide)
  rw [hM, hu, hv]

theorem carrySum5_eq_obs (n : Nat) :
    carrySumK 5 n = obs (toMat 5 5 M_C5) (toVec 5 u_C5) (toVec 5 v_C5) n := by
  rw [carrySumK_eq_obs 5 (by omega) n]
  have hM : carryMat 5 = toMat 5 5 M_C5 := eq_mat_of_forall (by decide)
  have hu : (fun c : Fin 5 => pm1 (popcount c.val)) = toVec 5 u_C5 := eq_vec_of_forall (by decide)
  have hv : (fun c : Fin 5 => if c = ⟨0, by omega⟩ then (1 : Int) else 0) = toVec 5 v_C5 := eq_vec_of_forall (by decide)
  rw [hM, hu, hv]

theorem K_corr7_eq_obs (n : Nat) :
    K_corr 7 n = obs (toMat 7 7 M_K7) (toVec 7 u_K7) (toVec 7 v_K7) n := by
  rw [K_corr_eq_obs 7 (by omega) n]
  have hM : kMat 7 = toMat 7 7 M_K7 := eq_mat_of_forall (by decide)
  have hu : (fun q : Fin 7 => pm1 (popcount q.val)) = toVec 7 u_K7 := eq_vec_of_forall (by decide)
  have hv : (fun q : Fin 7 => if q = ⟨0, by omega⟩ then (1 : Int) else 0) = toVec 7 v_K7 := eq_vec_of_forall (by decide)
  rw [hM, hu, hv]

theorem Z_corr5_eq_obs (n : Nat) :
    Z_corr 5 n = obs (toMat 10 10 M_Z5) (toVec 10 u_Z5) (toVec 10 v_Z5) n := by
  rw [Z_corr_eq_obs 5 (by omega) n]
  have hM : zMat 5 = toMat 10 10 M_Z5 := eq_mat_of_forall (by decide)
  have hu : (fun idx : Fin 10 => pm1 (popcount (idx.val / 2))) = toVec 10 u_Z5 := eq_vec_of_forall (by decide)
  have hv : (fun idx : Fin 10 => if idx = ⟨0, by omega⟩ then (1 : Int) else 0) = toVec 10 v_Z5 := eq_vec_of_forall (by decide)
  rw [hM, hu, hv]

/-! ### Exact Diagonal Closed-Form Helper for `M_diag4` -/

theorem obs_diag4_closed (n : Nat) :
    obs (toMat 4 4 M_diag4) (toVec 4 u_diag4) (toVec 4 v_diag4) n =
      8 * (8 : Int) ^ n + 12 * (-8 : Int) ^ n - 9 * (4 : Int) ^ n + (-4 : Int) ^ n := by
  have hpow : ∀ k : Nat,
      rMatVecMul (matPow (toMat 4 4 M_diag4) k) (toVec 4 v_diag4) =
      fun i : Fin 4 =>
        match i.val with
        | 0 => (8 : Int) ^ k
        | 1 => (-8 : Int) ^ k
        | 2 => (4 : Int) ^ k
        | _ => (-4 : Int) ^ k := by
    intro k
    induction k with
    | zero =>
      simp only [matPow, rMatVecMul_matId]
      funext i
      rcases i with ⟨v, hv⟩
      match v with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | 3 => rfl
    | succ k ih =>
      simp only [matPow, rMatVecMul_assoc, ih]
      funext i
      rcases i with ⟨v, hv⟩
      match v with
      | 0 =>
        simp only [rMatVecMul, finSum, Fin.val_castSucc, Fin.val_last, toMat, M_diag4,
                   List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
                   Int.pow_succ]; omega
      | 1 =>
        simp only [rMatVecMul, finSum, Fin.val_castSucc, Fin.val_last, toMat, M_diag4,
                   List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
                   Int.pow_succ]; omega
      | 2 =>
        simp only [rMatVecMul, finSum, Fin.val_castSucc, Fin.val_last, toMat, M_diag4,
                   List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
                   Int.pow_succ]; omega
      | 3 =>
        simp only [rMatVecMul, finSum, Fin.val_castSucc, Fin.val_last, toMat, M_diag4,
                   List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
                   Int.pow_succ]; omega
  simp only [obs, hpow n, vecDot, finSum, Fin.val_castSucc, Fin.val_last, toVec, u_diag4,
             List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  omega

/-! ### Concrete Certified Infinite Theorems (All Discharged by `decide` + CHKAE!) -/

theorem cert_K7_eq_2Z5_ok : checkIdentity cert_K7_eq_2Z5 = true := by decide

/-- **THEOREM 1 (Cross-Automaton Collapse):**
    For ALL `n : Nat`, `K_corr 7 (n + 3) = 2 * Z_corr 5 n`. -/
theorem thm_K7_eq_2Z5 : ∀ n : Nat, K_corr 7 (n + 3) = 2 * Z_corr 5 n := by
  intro n
  have h := identity_sound cert_K7_eq_2Z5 cert_K7_eq_2Z5_ok n
  simp only [cert_K7_eq_2Z5, Int.one_mul, Nat.add_zero] at h
  rw [K_corr7_eq_obs, Z_corr5_eq_obs]
  exact h

theorem cert_Z5_pos_ok : checkPosBound cert_Z5_pos = true := by decide
theorem cert_K7_pos_ok : checkPosBound cert_K7_pos = true := by decide

/-- **THEOREM 2a (Strict Positivity of `Z_5` and `K_7`):**
    For ALL `n : Nat`, both `Z_corr 5 n > 0` and `K_corr 7 n > 0`. -/
theorem thm_Z5_and_K7_pos : ∀ n : Nat, Z_corr 5 n > 0 ∧ K_corr 7 n > 0 := by
  intro n
  have hz := posBound_sound_gt cert_Z5_pos cert_Z5_pos_ok rfl n
  have hk := posBound_sound_gt cert_K7_pos cert_K7_pos_ok rfl n
  simp only [cert_Z5_pos, cert_K7_pos, Int.one_pow, Int.one_mul,
             Int.zero_mul, Int.add_zero, Nat.add_zero] at hz hk
  rw [Z_corr5_eq_obs, K_corr7_eq_obs]
  exact ⟨hz, hk⟩

theorem cert_Z5_lower_ok : checkPosBound cert_Z5_lower = true := by decide
theorem cert_Z5_upper_ok : checkPosBound cert_Z5_upper = true := by decide

/-- **THEOREM 2b (Sharp Irrational-Rate Exponential Sandwich for `Z_5`):**
    For ALL `n : Nat`, `17^n * Z_5(n) ≥ 23^n` AND `3 * 14^n * Z_5(n) ≤ 5 * 19^n`. -/
theorem thm_Z5_sandwich : ∀ n : Nat,
    (17 : Int) ^ n * Z_corr 5 n ≥ (23 : Int) ^ n ∧
    3 * (14 : Int) ^ n * Z_corr 5 n ≤ 5 * (19 : Int) ^ n := by
  intro n
  have hl := posBound_sound_ge cert_Z5_lower cert_Z5_lower_ok n
  have hu := posBound_sound_ge cert_Z5_upper cert_Z5_upper_ok n
  simp only [cert_Z5_lower, cert_Z5_upper, Int.one_pow, Int.one_mul, Int.mul_one,
             Int.neg_mul, Nat.add_zero] at hl hu
  rw [Z_corr5_eq_obs]
  omega

theorem cert_Z5_mod2_ok : checkScaledVal cert_Z5_mod2 = true := by decide

/-- **THEOREM 2c (Exact Mod-2 Periodicity of `Z_5` & Mod-4 Periodicity of `K_7`):**
    For ALL `n : Nat`, `Z_5(n) % 2 = if n % 3 = 1 then 0 else 1`,
    and `K_7(n + 3) % 4 = if n % 3 = 1 then 0 else 2`. -/
theorem thm_Z5_K7_parity_period : ∀ n : Nat,
    Z_corr 5 n % 2 = (if n % 3 = 1 then 0 else 1) ∧
    K_corr 7 (n + 3) % 4 = (if n % 3 = 1 then 0 else 2) := by
  intro n
  have h := scaledVal_sound cert_Z5_mod2 cert_Z5_mod2_ok n
  simp only [cert_Z5_mod2, Int.one_pow, Int.one_mul, Nat.add_zero] at h
  rcases h with ⟨heq, hmod⟩
  rw [Z_corr5_eq_obs, heq]
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hz_mod : quotSeq [2, -1, 1] [1, 2, 3] n % 2 = (if n % 3 = 1 then 0 else 1) := by
    rw [hmod]
    rcases h3 with h0 | h1 | h2
    · simp [h0]
    · simp [h1]
    · simp [h2]
  refine ⟨hz_mod, ?_⟩
  rw [thm_K7_eq_2Z5 n, Z_corr5_eq_obs, heq]
  omega

theorem cert_C3_val_ok : checkScaledVal cert_C3_val = true := by decide
theorem cert_C3_odd_mod4_ok : checkScaledVal cert_C3_odd_mod4 = true := by decide

/-- **THEOREM 3a (Exact 2-adic Valuation & Odd-Part Mod-4 Law for 3-Way Carry-Parity `C_3`):** -/
theorem thm_C3_exact_v2 : ∀ n : Nat, n ≥ 2 →
    (2 : Int) ^ (n + 1) ∣ carrySumK 3 n ∧ ¬ ((2 : Int) ^ (n + 2) ∣ carrySumK 3 n) := by
  intro n hn
  have hv := scaledVal_exact_valuation cert_C3_val cert_C3_val_ok ⟨1, rfl⟩ (by decide) (n - 2)
  simp only [cert_C3_val] at hv
  have h1 : (n - 2) + 2 = n := by omega
  have h2 : (n - 2) + 3 = n + 1 := by omega
  rw [h1, h2] at hv
  rw [carrySum3_eq_obs]
  exact hv

theorem thm_C3_odd_part_mod4 : ∀ n : Nat, n ≥ 3 →
    ∃ t : Int, carrySumK 3 n = (2 : Int) ^ (n + 1) * t ∧
      t % 4 = (if n % 2 = 0 then 1 else 3) := by
  intro n hn
  have h := scaledVal_sound cert_C3_odd_mod4 cert_C3_odd_mod4_ok (n - 3)
  simp only [cert_C3_odd_mod4] at h
  rcases h with ⟨heq, hmod⟩
  have h1 : (n - 3) + 3 = n := by omega
  have h2 : (n - 3) + 4 = n + 1 := by omega
  rw [h1, h2] at heq
  refine ⟨quotSeq [-8, 6, 1] [-1, 17, -13] (n - 3), ?_, ?_⟩
  · rw [carrySum3_eq_obs]; exact heq
  · rw [hmod]
    have hp : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hp with hp | hp
    · have hm : (n - 3) % 2 = 1 := by omega
      simp [hp, hm]
    · have hm : (n - 3) % 2 = 0 := by omega
      simp [hp, hm]

theorem cert_C3_alt_sign_ok : checkPosBound cert_C3_alt_sign = true := by decide
theorem cert_C3_lower_ok : checkPosBound cert_C3_lower = true := by decide
theorem cert_C3_upper_ok : checkPosBound cert_C3_upper = true := by decide

/-- **THEOREM 3b & 3c (Alternating Sign & Sharp Sandwich Around `1 + sqrt(17)` for `C_3`):** -/
theorem thm_C3_sign_and_sandwich : ∀ n : Nat, n ≥ 2 →
    (-1 : Int) ^ n * carrySumK 3 n > 0 ∧
    9 * (25 : Int) ^ n * ((-1 : Int) ^ n * carrySumK 3 n) ≥ (128 : Int) ^ n ∧
    (8 : Int) ^ n * ((-1 : Int) ^ n * carrySumK 3 n) ≤ (41 : Int) ^ n := by
  intro n hn
  have hsign := posBound_sound_gt cert_C3_alt_sign cert_C3_alt_sign_ok rfl (n - 2)
  have hlo := posBound_sound_ge cert_C3_lower cert_C3_lower_ok (n - 2)
  have hhi := posBound_sound_ge cert_C3_upper cert_C3_upper_ok (n - 2)
  simp only [cert_C3_alt_sign, cert_C3_lower, cert_C3_upper, Int.one_pow, Int.one_mul,
             Int.mul_one, Int.add_zero] at hsign hlo hhi
  have hadd : (n - 2) + 2 = n := by omega
  have hpm : (-1 : Int) ^ n = (-1 : Int) ^ (n - 2) := by
    have h1 : (-1 : Int) ^ ((n - 2) + 2) = (-1 : Int) ^ (n - 2) * (-1 : Int) ^ 2 := Int.pow_add _ _ _
    rw [hadd] at h1
    have hsq : (-1 : Int) ^ 2 = 1 := by decide
    rw [hsq, Int.mul_one] at h1
    exact h1
  have h25 : (25 : Int) ^ n = 625 * (25 : Int) ^ (n - 2) := by
    have h1 := Int.pow_add (25 : Int) (n - 2) 2
    rw [hadd, Int.mul_comm] at h1; exact h1
  have h128 : (128 : Int) ^ n = 16384 * (128 : Int) ^ (n - 2) := by
    have h1 := Int.pow_add (128 : Int) (n - 2) 2
    rw [hadd, Int.mul_comm] at h1; exact h1
  have h8 : (8 : Int) ^ n = 64 * (8 : Int) ^ (n - 2) := by
    have h1 := Int.pow_add (8 : Int) (n - 2) 2
    rw [hadd, Int.mul_comm] at h1; exact h1
  have h41 : (41 : Int) ^ n = 1681 * (41 : Int) ^ (n - 2) := by
    have h1 := Int.pow_add (41 : Int) (n - 2) 2
    rw [hadd, Int.mul_comm] at h1; exact h1
  rw [hadd] at hsign hlo hhi
  rw [carrySum3_eq_obs, hpm]
  refine ⟨hsign, ?_, ?_⟩
  · rw [h25, h128]
    have hL : 9 * (625 * (25 : Int) ^ (n - 2)) * ((-1 : Int) ^ (n - 2) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n) =
        5625 * (-1 : Int) ^ (n - 2) * (25 : Int) ^ (n - 2) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n := by
      have h1 : 9 * (625 * (25 : Int) ^ (n - 2)) = 5625 * (25 : Int) ^ (n - 2) := by omega
      rw [h1]
      calc
        5625 * (25 : Int) ^ (n - 2) * ((-1 : Int) ^ (n - 2) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n)
          = 5625 * ((25 : Int) ^ (n - 2) * (-1 : Int) ^ (n - 2)) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n := by
              rw [Int.mul_assoc 5625, ← Int.mul_assoc ((25 : Int) ^ (n - 2)), ← Int.mul_assoc 5625]
        _ = 5625 * ((-1 : Int) ^ (n - 2) * (25 : Int) ^ (n - 2)) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n := by
              rw [Int.mul_comm ((25 : Int) ^ (n - 2)) ((-1 : Int) ^ (n - 2))]
        _ = 5625 * (-1 : Int) ^ (n - 2) * (25 : Int) ^ (n - 2) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n := by
              rw [← Int.mul_assoc 5625]
    rw [hL]; omega
  · rw [h8, h41]
    have hU : 64 * (8 : Int) ^ (n - 2) * ((-1 : Int) ^ (n - 2) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n) =
        -((-64) * (-1 : Int) ^ (n - 2) * (8 : Int) ^ (n - 2) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n) := by
      calc
        64 * (8 : Int) ^ (n - 2) * ((-1 : Int) ^ (n - 2) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n)
          = 64 * ((8 : Int) ^ (n - 2) * (-1 : Int) ^ (n - 2)) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n := by
              rw [Int.mul_assoc 64, ← Int.mul_assoc ((8 : Int) ^ (n - 2)), ← Int.mul_assoc 64]
        _ = 64 * ((-1 : Int) ^ (n - 2) * (8 : Int) ^ (n - 2)) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n := by
              rw [Int.mul_comm ((8 : Int) ^ (n - 2)) ((-1 : Int) ^ (n - 2))]
        _ = -((-64) * (-1 : Int) ^ (n - 2) * (8 : Int) ^ (n - 2) * obs (toMat 3 3 M_C3) (toVec 3 u_C3) (toVec 3 v_C3) n) := by
              simp only [Int.neg_mul, Int.neg_neg, Int.mul_assoc]
    rw [hU]; omega

theorem cert_C4_closed_ok : checkIdentity cert_C4_closed = true := by decide

/-- **THEOREM 4 (Exact Closed Form for 4-Way Carry-Parity `C_4`):** -/
theorem thm_C4_closed_form : ∀ n : Nat,
    12 * carrySumK 4 n =
      8 * (8 : Int) ^ n + 12 * (-8 : Int) ^ n - 9 * (4 : Int) ^ n + (-4 : Int) ^ n := by
  intro n
  have h := identity_sound cert_C4_closed cert_C4_closed_ok n
  simp only [cert_C4_closed, Int.one_mul, Nat.add_zero] at h
  rw [carrySum4_eq_obs, h, obs_diag4_closed]

theorem cert_C5_val_mod8_ok : checkScaledVal cert_C5_val_mod8 = true := by decide

/-- **THEOREM 5a (Exact 2-adic Valuation & Odd-Part Mod-8 Law for 5-Way Carry-Parity `C_5`):** -/
theorem thm_C5_exact_v2_and_mod8 : ∀ n : Nat, n ≥ 3 →
    ((2 : Int) ^ (n + 2) ∣ carrySumK 5 n ∧ ¬ ((2 : Int) ^ (n + 3) ∣ carrySumK 5 n)) ∧
    (∃ t : Int, carrySumK 5 n = (2 : Int) ^ (n + 2) * t ∧
      t % 8 = (if n % 2 = 0 then 7 else 3)) := by
  intro n hn
  have hv := scaledVal_exact_valuation cert_C5_val_mod8 cert_C5_val_mod8_ok ⟨4, rfl⟩ (by decide) (n - 3)
  have hm := scaledVal_sound cert_C5_val_mod8 cert_C5_val_mod8_ok (n - 3)
  simp only [cert_C5_val_mod8] at hv hm
  have h1 : (n - 3) + 3 = n := by omega
  have h2 : (n - 3) + 5 = n + 2 := by omega
  rw [h1, h2] at hv hm
  rw [carrySum5_eq_obs]
  refine ⟨hv, ⟨quotSeq [1024, -640, -48, 60, 1] [-45, 863, -941, 37639, -10965] (n - 3), hm.1, ?_⟩⟩
  rw [hm.2]
  have hp : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hp with hp | hp
  · have hrem : (n - 3) % 2 = 1 := by omega
    simp [hp, hrem]
  · have hrem : (n - 3) % 2 = 0 := by omega
    simp [hp, hrem]

theorem cert_C5_cone_ok : checkCone cert_C5_cone = true := by decide

private theorem cObs_eq_obs (d : Nat) (M : CMat) (u v : CVec)
    (hM : wfMatBool d d M = true) (hu : u.length = d) (hv : v.length = d) (n : Nat) :
    cVecDot u (cVecIter M v n) = obs (toMat d d M) (toVec d u) (toVec d v) n := by
  have hM' := wfMat_of_bool hM
  rw [cVecDot_eq u _ hu (cVecIter_length M v hM' hv n), toVec_cVecIter M v hM' hv n]
  rfl

/-- **THEOREM 5b (Eventual Strict Positivity of `C_5` Beyond Descartes' Rule of Signs):** -/
theorem thm_C5_pos_for_all_ge_8 : ∀ n : Nat, n ≥ 8 → carrySumK 5 n > 0 := by
  have hcone := (cone_pos_and_bound_sound cert_C5_cone cert_C5_cone_ok).1
  simp only [cert_C5_cone] at hcone
  have h8  : obs (toMat 5 5 M_C5) (toVec 5 u_C5) (toVec 5 v_C5) 8 > 0 := by
    rw [← cObs_eq_obs 5 M_C5 u_C5 v_C5 (by decide) rfl rfl 8]; decide
  have h9  : obs (toMat 5 5 M_C5) (toVec 5 u_C5) (toVec 5 v_C5) 9 > 0 := by
    rw [← cObs_eq_obs 5 M_C5 u_C5 v_C5 (by decide) rfl rfl 9]; decide
  have h10 : obs (toMat 5 5 M_C5) (toVec 5 u_C5) (toVec 5 v_C5) 10 > 0 := by
    rw [← cObs_eq_obs 5 M_C5 u_C5 v_C5 (by decide) rfl rfl 10]; decide
  have h11 : obs (toMat 5 5 M_C5) (toVec 5 u_C5) (toVec 5 v_C5) 11 > 0 := by
    rw [← cObs_eq_obs 5 M_C5 u_C5 v_C5 (by decide) rfl rfl 11]; decide
  intro n hn
  rw [carrySum5_eq_obs]
  by_cases h12 : n ≥ 12
  · have h := hcone (n - 12)
    have heq : (n - 12) + 12 = n := by omega
    rw [heq] at h
    exact h
  · have hcases : n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact h8
    · exact h9
    · exact h10
    · exact h11

theorem thm_C5_perron_lower_bound : ∀ m : Nat,
    (3 : Int) ^ m * carrySumK 5 (m + 12) ≥ carrySumK 5 12 * (8 : Int) ^ m := by
  have hbd := (cone_pos_and_bound_sound cert_C5_cone cert_C5_cone_ok).2
  simp only [cert_C5_cone] at hbd
  intro m
  have hm := hbd m
  rw [← carrySum5_eq_obs, ← carrySum5_eq_obs] at hm
  have h925 : (925968 : Int) = 308656 * 3 := by decide
  have h246 : (2469248 : Int) = 308656 * 8 := by decide
  rw [h925, h246, Int.mul_pow, Int.mul_pow] at hm
  have hpos : (0 : Int) < (308656 : Int) ^ m := Int.pow_pos (by decide)
  have hL : (308656 : Int) ^ m * (carrySumK 5 12 * (8 : Int) ^ m) =
      carrySumK 5 12 * ((308656 : Int) ^ m * (8 : Int) ^ m) := by
    rw [← Int.mul_assoc, Int.mul_comm ((308656 : Int) ^ m), Int.mul_assoc]
  have hR2 : (308656 : Int) ^ m * ((3 : Int) ^ m * carrySumK 5 (m + 12)) =
      (308656 : Int) ^ m * (3 : Int) ^ m * carrySumK 5 (m + 12) := (Int.mul_assoc _ _ _).symm
  rw [← hL, ← hR2] at hm
  exact int_le_of_mul_le_left hpos hm

theorem cert_MatAnn_C3_ok : checkMatAnn cert_MatAnn_C3 = true := by decide
theorem cert_MatAnn_C5_ok : checkMatAnn cert_MatAnn_C5 = true := by decide

theorem thm_C3_universal_recurrence (u v : Vec 3) : ∀ n : Nat,
    obs (toMat 3 3 M_C3) u v (n + 3) =
      (-64) * obs (toMat 3 3 M_C3) u v n +
      24 * obs (toMat 3 3 M_C3) u v (n + 1) +
      2 * obs (toMat 3 3 M_C3) u v (n + 2) := by
  intro n
  have h := matAnn_sound cert_MatAnn_C3 u v cert_MatAnn_C3_ok n
  dsimp [cert_MatAnn_C3, finSum, toVec] at h
  have hc0 : ([-64, 24, 2] : List Int).getD 0 0 = -64 := rfl
  have hc1 : ([-64, 24, 2] : List Int).getD 1 0 = 24 := rfl
  have hc2 : ([-64, 24, 2] : List Int).getD 2 0 = 2 := rfl
  rw [hc0, hc1, hc2] at h
  omega

/-! ## Section 5: Kernel-Checked Non-Vacuity & Sharpness / Falsification Witnesses -/

/-- Non-vacuity witness: concrete values of `K_corr 7`, `Z_corr 5`, `carrySumK 3/4/5`. -/
theorem witness_nonvacuity_values :
    K_corr 7 3 = 2 ∧ Z_corr 5 0 = 1 ∧ K_corr 7 4 = 4 ∧ Z_corr 5 1 = 2 ∧
    carrySumK 3 2 = 24 ∧ carrySumK 4 2 = 96 ∧ carrySumK 5 2 = 320 := by
  decide

/-- **Sharpness Witness 1 (Carried-vs-Carryless Positivity Fails at `c = 23`!):** -/
theorem sharpness_K23_fails : K_corr 23 3 = 0 ∧ K_corr 23 4 = -4 := by
  decide

/-- **Sharpness Witness 2 (`C_3` bound `n ≥ 2` is sharp):** `C_3(1) = 0`. -/
theorem sharpness_C3_at_1 : carrySumK 3 1 = 0 := by
  decide

/-- **Sharpness Witness 3 (`C_5` deceptive alternation breaks at `n = 9`; `n ≥ 8` is sharp):** -/
theorem sharpness_C5_alternation_break :
    carrySumK 5 7 = -5614080 ∧ carrySumK 5 8 = 1734802432 ∧ carrySumK 5 9 = 1465391104 := by
  rw [carrySum5_eq_obs, carrySum5_eq_obs, carrySum5_eq_obs,
      ← cObs_eq_obs 5 M_C5 u_C5 v_C5 (by decide) rfl rfl 7,
      ← cObs_eq_obs 5 M_C5 u_C5 v_C5 (by decide) rfl rfl 8,
      ← cObs_eq_obs 5 M_C5 u_C5 v_C5 (by decide) rfl rfl 9]
  decide

/-- **Sharpness Witness 4 (`C_5` valuation `n ≥ 3` is sharp):** `2^6 ∣ C_5(2) = 320`. -/
theorem sharpness_C5_v2_at_2 : (2 : Int) ^ 6 ∣ carrySumK 5 2 := by
  have h : carrySumK 5 2 = 320 := by decide
  rw [h]; exact ⟨5, by decide⟩

/-- **Sharpness Witness 5 (`+3` shift in `K_7(n+3) = 2*Z_5(n)` is sharp):** -/
theorem sharpness_K7_Z5_shift : K_corr 7 2 ≠ 2 * Z_corr 5 2 := by
  decide

/-! ## Section 6: Kernel-Checked Negative / Hostile Mutation Tests (`check* bad = false`) -/

theorem mut01_matAnn_bad_coeff :
    checkMatAnn { cert_MatAnn_C3 with c := [-64, 24, 3] } = false := by decide

theorem mut02_quotAnn_empty_defect_on_K7 :
    checkQuotAnn { d := 7, M := M_K7, u := u_K7, v := v_K7, n0 := 3, c := [2, -1, 1], r := [] } = false := by decide

theorem mut03_quotAnn_wrong_defect_r :
    checkQuotAnn { d := 7, M := M_K7, u := u_K7, v := v_K7, n0 := 3, c := [2, -1, 1], r := [2] } = false := by decide

theorem mut04_identity_wrong_shift :
    checkIdentity { cert_K7_eq_2Z5 with off1 := 2 } = false := by decide

theorem mut05_identity_wrong_scale :
    checkIdentity { cert_K7_eq_2Z5 with scale2 := 3 } = false := by decide

theorem mut06_scaledVal_overstrong_preshift :
    checkScaledVal { cert_C3_val with preShift := 4 } = false := by decide

theorem mut07_scaledVal_corrupted_period_table :
    checkScaledVal { cert_C5_val_mod8 with periodTable := [3, 5] } = false := by decide

theorem mut08_posBound_tau_zero_blocked :
    checkPosBound { cert_C3_alt_sign with tau := 0 } = false := by decide

theorem mut09_posBound_negative_C_coeff :
    checkPosBound { cert_Z5_pos with C := [2, -1, 1] } = false := by decide

theorem mut10_posBound_invalid_lower_base :
    checkPosBound { cert_Z5_lower with a := 24 } = false := by decide

theorem mut11_posBound_invalid_upper_base :
    checkPosBound { cert_Z5_upper with a := 23, b := 17 } = false := by decide

theorem mut12_cone_negative_A_entry :
    checkCone { cert_C5_cone with
      A := [-1, 11989452, 0, 0, 0, 456108, 0, 0] :: A_C5.tail } = false := by decide

theorem mut13_cone_perturbed_G_breaks_intertwining :
    checkCone { cert_C5_cone with
      G := [1, 1, 0, 1, -14, 15, -5, 6] :: G_C5.tail } = false := by decide

theorem mut14_cone_invalid_n0_at_7 :
    checkCone { cert_C5_cone with n0 := 7 } = false := by decide

theorem mut15_cone_overtight_perron_rate :
    checkCone { cert_C5_cone with rateNum := 2469249 } = false := by decide

end CHKAE
