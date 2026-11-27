import FenwickPortalParitySchur.Defs

namespace SpecMat7
section CRingLemmas
variable {R : Type} [CRing R]

theorem add_right_neg (a : R) : a +ᵣ (-ᵣa) = zᵣ := by
  rw [CRing.add_comm, CRing.add_left_neg]

theorem mul_one (a : R) : a *ᵣ eᵣ = a := by
  rw [CRing.mul_comm, CRing.one_mul]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a +ᵣ b = zᵣ) : -ᵣa = b := by
  apply add_left_cancel (a := a)
  rw [add_right_neg, h]

theorem neg_zero : -ᵣ(zᵣ : R) = zᵣ :=
  neg_eq_of_add_eq_zero (CRing.zero_add zᵣ)

theorem neg_neg (a : R) : -ᵣ(-ᵣa) = a :=
  neg_eq_of_add_eq_zero (CRing.add_left_neg a)

theorem neg_add (a b : R) : -ᵣ(a +ᵣ b) = (-ᵣa) +ᵣ (-ᵣb) := by
  apply neg_eq_of_add_eq_zero
  calc (a +ᵣ b) +ᵣ ((-ᵣa) +ᵣ (-ᵣb))
      = (a +ᵣ (-ᵣa)) +ᵣ (b +ᵣ (-ᵣb)) := by
        rw [CRing.add_assoc, ← CRing.add_assoc b (-ᵣa), CRing.add_comm b (-ᵣa),
            CRing.add_assoc (-ᵣa) b, ← CRing.add_assoc]
    _ = zᵣ +ᵣ zᵣ := by rw [add_right_neg, add_right_neg]
    _ = zᵣ := CRing.zero_add zᵣ

theorem mul_neg (a b : R) : a *ᵣ (-ᵣb) = -ᵣ(a *ᵣ b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← CRing.left_distrib, add_right_neg, mul_zero]

theorem neg_mul (a b : R) : (-ᵣa) *ᵣ b = -ᵣ(a *ᵣ b) := by
  rw [CRing.mul_comm, mul_neg, CRing.mul_comm]

theorem neg_mul_neg (a b : R) : (-ᵣa) *ᵣ (-ᵣb) = a *ᵣ b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem add_left_comm (a b c : R) : a +ᵣ (b +ᵣ c) = b +ᵣ (a +ᵣ c) := by
  rw [← CRing.add_assoc, CRing.add_comm a b, CRing.add_assoc]

theorem mul_left_comm (a b c : R) : a *ᵣ (b *ᵣ c) = b *ᵣ (a *ᵣ c) := by
  rw [← CRing.mul_assoc, CRing.mul_comm a b, CRing.mul_assoc]

theorem rsign_zero : rsign (R := R) 0 = eᵣ := rfl

theorem rsign_one : rsign (R := R) 1 = -ᵣeᵣ := rfl

theorem rsign_succ (n : Nat) : rsign (R := R) (n + 1) = -ᵣ(rsign (R := R) n) := by
  unfold rsign
  by_cases h : n % 2 = 0
  · have h1 : (n + 1) % 2 ≠ 0 := by omega
    simp [h, h1]
  · have h1 : (n + 1) % 2 = 0 := by omega
    simp [h, h1, neg_neg]

theorem rsign_add (a b : Nat) : rsign (R := R) (a + b) = rsign (R := R) a *ᵣ rsign (R := R) b := by
  unfold rsign
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0
  · have hab : (a + b) % 2 = 0 := by omega
    simp [ha, hb, hab, CRing.one_mul]
  · have hab : (a + b) % 2 ≠ 0 := by omega
    simp [ha, hb, hab, CRing.one_mul]
  · have hab : (a + b) % 2 ≠ 0 := by omega
    simp [ha, hb, hab, mul_one]
  · have hab : (a + b) % 2 = 0 := by omega
    simp [ha, hb, hab, neg_mul_neg, CRing.one_mul]

theorem rsign_mul_self (n : Nat) : rsign (R := R) n *ᵣ rsign (R := R) n = eᵣ := by
  rw [← rsign_add]
  unfold rsign
  have h : (n + n) % 2 = 0 := by omega
  simp [h]

theorem sumFin_neg {n : Nat} (f : Fin n → R) :
    sumFin (fun i => -ᵣ(f i)) = -ᵣ(sumFin f) := by
  induction n with
  | zero => simp [sumFin_zero, neg_zero]
  | succ m ih => simp only [sumFin_succ, ih, neg_add]

theorem sumFin_comm {m n : Nat} (f : Fin m → Fin n → R) :
    sumFin (fun i => sumFin (fun j => f i j)) =
    sumFin (fun j => sumFin (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumFin_zero]
    symm
    exact sumFin_const_zero
  | succ k ih =>
    simp only [sumFin_succ, ih, ← sumFin_add]

theorem sumFin_append {a b : Nat} (f : Fin (a + b) → R) :
    sumFin f =
      sumFin (fun i : Fin a => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩) +ᵣ
      sumFin (fun j : Fin b => f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) := by
  induction b with
  | zero =>
    simp only [sumFin_zero, add_zero]
    exact sumFin_congr (fun _ => rfl)
  | succ k ih =>
    calc sumFin f
        = sumFin (fun i : Fin (a + k) => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +ᵣ
          f ⟨a + k, Nat.lt_succ_self (a + k)⟩ := sumFin_succ_last f
      _ = (sumFin (fun i : Fin a => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a (k + 1))⟩) +ᵣ
           sumFin (fun j : Fin k => f ⟨a + j.val, Nat.lt_succ_of_lt (Nat.add_lt_add_left j.isLt a)⟩)) +ᵣ
          f ⟨a + k, Nat.lt_succ_self (a + k)⟩ := by
            rw [ih (fun i : Fin (a + k) => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
      _ = sumFin (fun i : Fin a => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a (k + 1))⟩) +ᵣ
          (sumFin (fun j : Fin k => f ⟨a + j.val, Nat.lt_succ_of_lt (Nat.add_lt_add_left j.isLt a)⟩) +ᵣ
           f ⟨a + k, Nat.lt_succ_self (a + k)⟩) := CRing.add_assoc _ _ _
      _ = sumFin (fun i : Fin a => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a (k + 1))⟩) +ᵣ
          sumFin (fun j : Fin (k + 1) => f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) := by
            rw [sumFin_succ_last (fun j : Fin (k + 1) => f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩)]

end CRingLemmas
namespace FPS
end FPS
section DetTheory
variable {R : Type} [CRing R]

theorem skipIdx_zero {n : Nat} (i : Fin n) :
    skipIdx ⟨0, Nat.zero_lt_succ n⟩ i = i.succ := by
  unfold skipIdx
  have h : ¬ (i.val < 0) := Nat.not_lt_zero _
  simp [h, Fin.succ]

theorem skipIdx_zero' {n : Nat} (i : Fin n) :
    skipIdx (0 : Fin (n + 1)) i = i.succ :=
  skipIdx_zero i

theorem skipIdx_last {n : Nat} (i : Fin n) :
    skipIdx ⟨n, Nat.lt_succ_self n⟩ i = ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
  unfold skipIdx
  simp [i.isLt]

theorem det_zero_dim (M : Mat 0 R) : det M = eᵣ := rfl

theorem det_succ {n : Nat} (M : Mat (n + 1) R) :
    det M = sumFin (fun j : Fin (n + 1) =>
      rsign j.val *ᵣ M ⟨0, Nat.zero_lt_succ n⟩ j *ᵣ det (minor M ⟨0, Nat.zero_lt_succ n⟩ j)) := rfl

theorem det_congr {n : Nat} {M N : Mat n R} (h : ∀ i j, M i j = N i j) : det M = det N := by
  have heq : M = N := by funext i j; exact h i j
  rw [heq]

theorem det_cast {m n : Nat} (h : m = n) (M : Mat m R) :
    det M = det (fun i j : Fin n => M ⟨i.val, h ▸ i.isLt⟩ ⟨j.val, h ▸ j.isLt⟩) := by
  subst h; rfl

theorem updateRow_self {n : Nat} (M : Mat n R) (r : Fin n) :
    updateRow M r (fun j => M r j) = M := by
  funext i j; unfold updateRow; split <;> simp_all

omit [CRing R] in
theorem minor_updateRow_zero {n : Nat} (M : Mat (n + 1) R) (v : Fin (n + 1) → R) (j : Fin (n + 1)) :
    minor (updateRow M (0 : Fin (n + 1)) v) ⟨0, Nat.zero_lt_succ n⟩ j =
    minor M ⟨0, Nat.zero_lt_succ n⟩ j := by
  funext i c
  unfold minor updateRow
  rw [skipIdx_zero]
  have hne : i.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero i
  simp [hne]

omit [CRing R] in
theorem minor_updateRow_succ {n : Nat} (M : Mat (n + 1) R) (r : Fin n) (v : Fin (n + 1) → R)
    (j : Fin (n + 1)) :
    minor (updateRow M r.succ v) ⟨0, Nat.zero_lt_succ n⟩ j =
    updateRow (minor M ⟨0, Nat.zero_lt_succ n⟩ j) r (fun c => v (skipIdx j c)) := by
  funext i c
  unfold minor updateRow
  simp only [skipIdx_zero]
  by_cases h : i = r
  · subst h; simp
  · have hne : i.succ ≠ r.succ := fun heq => h (Fin.succ_inj.mp heq)
    simp [h, hne]

/-- Row additivity of `det` at any row `r`. -/
theorem det_updateRow_add {n : Nat} (M : Mat n R) (r : Fin n) (u v : Fin n → R) :
    det (updateRow M r (fun j => u j +ᵣ v j)) =
    det (updateRow M r u) +ᵣ det (updateRow M r v) := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ m ih =>
    cases r using Fin.cases with
    | zero =>
      simp only [det_succ, minor_updateRow_zero]
      rw [← sumFin_add]
      apply sumFin_congr; intro j
      have h0 : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = 0 := rfl
      simp only [updateRow, h0, ↓reduceIte]
      rw [CRing.left_distrib, right_distrib]
    | succ r' =>
      simp only [det_succ, minor_updateRow_succ]
      rw [← sumFin_add]
      apply sumFin_congr; intro j
      have hne : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) ≠ r'.succ := Ne.symm (Fin.succ_ne_zero r')
      simp only [updateRow, hne, ↓reduceIte]
      rw [ih (minor M ⟨0, Nat.zero_lt_succ m⟩ j) r' (fun c => u (skipIdx j c)) (fun c => v (skipIdx j c))]
      rw [CRing.left_distrib]

/-- Row scalar homogeneity of `det` at any row `r`. -/
theorem det_updateRow_smul {n : Nat} (M : Mat n R) (r : Fin n) (s : R) (v : Fin n → R) :
    det (updateRow M r (fun j => s *ᵣ v j)) = s *ᵣ det (updateRow M r v) := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ m ih =>
    cases r using Fin.cases with
    | zero =>
      simp only [det_succ, minor_updateRow_zero]
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro j
      have h0 : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = 0 := rfl
      simp only [updateRow, h0, ↓reduceIte]
      calc rsign j.val *ᵣ (s *ᵣ v j) *ᵣ det (minor M 0 j)
          = (rsign j.val *ᵣ s) *ᵣ v j *ᵣ det (minor M 0 j) := by rw [← CRing.mul_assoc (rsign j.val) s (v j)]
        _ = (s *ᵣ rsign j.val) *ᵣ v j *ᵣ det (minor M 0 j) := by rw [CRing.mul_comm (rsign j.val) s]
        _ = s *ᵣ (rsign j.val *ᵣ v j *ᵣ det (minor M 0 j)) := by simp only [CRing.mul_assoc]
    | succ r' =>
      simp only [det_succ, minor_updateRow_succ]
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro j
      have hne : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) ≠ r'.succ := Ne.symm (Fin.succ_ne_zero r')
      simp only [updateRow, hne, ↓reduceIte]
      rw [ih (minor M ⟨0, Nat.zero_lt_succ m⟩ j) r' (fun c => v (skipIdx j c))]
      rw [mul_left_comm]

theorem det_updateRow_zero {n : Nat} (M : Mat n R) (r : Fin n) :
    det (updateRow M r (fun _ => zᵣ)) = zᵣ := by
  have h : (fun _ : Fin n => (zᵣ : R)) = (fun _ => zᵣ *ᵣ (zᵣ : R)) := by
    funext _; exact (zero_mul zᵣ).symm
  rw [h, det_updateRow_smul, zero_mul]

private theorem skipIdx_skipIdx_comm {m : Nat} (j : Fin (m + 2)) (k : Fin (m + 1)) (i : Fin m) :
    (if h : k.val < j.val then
      skipIdx j (skipIdx k i) =
      skipIdx ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ (skipIdx ⟨j.val - 1, by omega⟩ i)
    else
      skipIdx j (skipIdx k i) =
      skipIdx ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ (skipIdx ⟨j.val, by omega⟩ i)) := by
  split
  · rename_i hkj
    unfold skipIdx; apply Fin.ext
    by_cases h1 : i.val < k.val
    · have h2 : i.val < j.val - 1 := by omega
      have h3 : i.val < j.val := by omega
      simp [h1, h2, h3]
    · by_cases h2 : i.val < j.val - 1
      · have h3 : i.val + 1 < j.val := by omega
        simp [h1, h2, h3]
      · have h3 : ¬ (i.val + 1 < j.val) := by omega
        have h4 : ¬ (i.val + 1 < k.val) := by omega
        simp [h1, h2, h3, h4]
  · rename_i hkj
    unfold skipIdx; apply Fin.ext
    by_cases h1 : i.val < j.val
    · have h2 : i.val < k.val := by omega
      have h3 : i.val < k.val + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : i.val < k.val
      · have h3 : i.val + 1 < k.val + 1 := by omega
        simp [h1, h2, h3]
      · have h3 : ¬ (i.val + 1 < j.val) := by omega
        have h4 : ¬ (i.val + 1 < k.val + 1) := by omega
        simp [h1, h2, h3, h4]

private theorem pairInv_invol_j {m : Nat} (j : Fin (m + 2)) (k : Fin (m + 1)) :
    pairInvJ (pairInvJ j k) (pairInvK j k) = j := by
  unfold pairInvJ pairInvK skipIdx
  apply Fin.ext
  split <;> split <;> simp_all <;> omega

private theorem pairInv_sign {m : Nat} (j : Fin (m + 2)) (k : Fin (m + 1)) :
    rsign (R := R) (pairInvJ j k).val *ᵣ rsign (R := R) (pairInvK j k).val =
    -ᵣ(rsign (R := R) j.val *ᵣ rsign (R := R) k.val) := by
  rw [← rsign_add, ← rsign_add]
  unfold pairInvJ pairInvK skipIdx
  by_cases h : k.val < j.val
  · simp only [h, ↓reduceDIte]
    have hsum : k.val + (j.val - 1) + 1 = j.val + k.val := by omega
    rw [← hsum, rsign_succ, neg_neg]
  · simp only [h, ↓reduceDIte]
    have hsum : k.val + 1 + j.val = (j.val + k.val) + 1 := by omega
    rw [hsum, rsign_succ]

omit [CRing R] in
private theorem pairInv_minor {m : Nat} (M : Mat (m + 2) R) (j : Fin (m + 2)) (k : Fin (m + 1)) :
    minor (minor M ⟨0, by omega⟩ (pairInvJ j k)) ⟨0, by omega⟩ (pairInvK j k) =
    minor (minor M ⟨0, by omega⟩ j) ⟨0, by omega⟩ k := by
  funext a b
  unfold minor
  simp only [skipIdx_zero]
  have hcol := skipIdx_skipIdx_comm j k b
  unfold pairInvJ pairInvK
  by_cases h : k.val < j.val
  · simp only [h, ↓reduceDIte] at hcol ⊢
    have h1 : skipIdx j k = ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ := by
      unfold skipIdx; simp [h]
    rw [h1, ← hcol]
  · simp only [h, ↓reduceDIte] at hcol ⊢
    have h1 : skipIdx j k = ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ := by
      unfold skipIdx; simp [h]
    rw [h1, ← hcol]

private theorem sumFin_skip_zero {n : Nat} (p : Fin (n + 1)) (g : Fin (n + 1) → R) (hp : g p = zᵣ) :
    sumFin g = sumFin (fun k : Fin n => g (skipIdx p k)) := by
  induction n with
  | zero =>
    simp only [sumFin_succ, sumFin_zero, add_zero]
    have hp0 : p = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [← hp0, hp]
  | succ t iht =>
    cases p using Fin.cases with
    | zero =>
      rw [sumFin_succ]
      have h0 : g ⟨0, Nat.zero_lt_succ (t + 1)⟩ = zᵣ := hp
      rw [h0, CRing.zero_add]
      apply sumFin_congr; intro k; rw [skipIdx_zero']
    | succ p' =>
      rw [sumFin_succ g, sumFin_succ (fun k : Fin (t + 1) => g (skipIdx p'.succ k))]
      have h0 : skipIdx p'.succ ⟨0, Nat.zero_lt_succ t⟩ = ⟨0, Nat.zero_lt_succ (t + 1)⟩ := by
        unfold skipIdx; simp [Fin.succ]
      rw [h0]
      apply congrArg (CRing.add _)
      rw [iht p' (fun i => g i.succ) hp]
      apply sumFin_congr; intro k
      congr 1; unfold skipIdx; apply Fin.ext; simp only [Fin.succ]
      by_cases hlt : k.val < p'.val
      · have hlt2 : k.val + 1 < p'.val + 1 := by omega
        simp [hlt, hlt2]
      · have hlt2 : ¬ (k.val + 1 < p'.val + 1) := by omega
        simp [hlt, hlt2]

private theorem sumFin_pairInv {m : Nat} (F : Fin (m + 2) → Fin (m + 1) → R) :
    sumFin (fun j : Fin (m + 2) => sumFin (fun k : Fin (m + 1) => F (pairInvJ j k) (pairInvK j k))) =
    sumFin (fun j : Fin (m + 2) => sumFin (fun k : Fin (m + 1) => F j k)) := by
  let G : Fin (m + 2) → Fin (m + 2) → R := fun a b =>
    if h : a.val < b.val then F a ⟨b.val - 1, by omega⟩
    else if h2 : b.val < a.val then F a ⟨b.val, by omega⟩
    else zᵣ
  have h1 : ∀ j : Fin (m + 2),
      sumFin (fun k : Fin (m + 1) => F j k) = sumFin (fun b : Fin (m + 2) => G j b) := by
    intro j
    rw [sumFin_skip_zero j (G j) (by simp [G])]
    apply sumFin_congr; intro k
    unfold G skipIdx
    by_cases h : k.val < j.val
    · have hlt : ¬ (j.val < k.val) := by omega
      simp [h, hlt]
    · have hgt : j.val < k.val + 1 := by omega
      simp [h, hgt]
  have h2 : ∀ j : Fin (m + 2),
      sumFin (fun k : Fin (m + 1) => F (pairInvJ j k) (pairInvK j k)) =
      sumFin (fun b : Fin (m + 2) => G b j) := by
    intro j
    rw [sumFin_skip_zero j (fun b => G b j) (by simp [G])]
    apply sumFin_congr; intro k
    unfold G pairInvJ pairInvK skipIdx
    by_cases h : k.val < j.val
    · simp [h]
    · have h1' : ¬ (k.val + 1 < j.val) := by omega
      have h2' : j.val < k.val + 1 := by omega
      simp [h, h1', h2']
  calc sumFin (fun j => sumFin (fun k => F (pairInvJ j k) (pairInvK j k)))
      = sumFin (fun j => sumFin (fun b => G b j)) := sumFin_congr h2
    _ = sumFin (fun b => sumFin (fun j => G b j)) := sumFin_comm (fun j b => G b j)
    _ = sumFin (fun b => sumFin (fun k => F b k)) := sumFin_congr (fun b => (h1 b).symm)

theorem det_swapRow01 {m : Nat} (M : Mat (m + 2) R) : det (swapRow01 M) = -ᵣ(det M) := by
  rw [det_succ (swapRow01 M), det_succ M]
  have hExpand : ∀ (A : Mat (m + 2) R),
      sumFin (fun j : Fin (m + 2) => rsign j.val *ᵣ A ⟨0, by omega⟩ j *ᵣ det (minor A ⟨0, by omega⟩ j)) =
      sumFin (fun j : Fin (m + 2) => sumFin (fun k : Fin (m + 1) =>
        (rsign j.val *ᵣ rsign k.val) *ᵣ
        (A ⟨0, by omega⟩ j *ᵣ A ⟨1, by omega⟩ (skipIdx j k)) *ᵣ
        det (minor (minor A ⟨0, by omega⟩ j) ⟨0, by omega⟩ k))) := by
    intro A
    apply sumFin_congr; intro j
    rw [det_succ, ← sumFin_mul_left]
    apply sumFin_congr; intro k
    have hm : minor A ⟨0, by omega⟩ j ⟨0, by omega⟩ k = A ⟨1, by omega⟩ (skipIdx j k) := by
      unfold minor; rw [skipIdx_zero]; rfl
    rw [hm]
    simp only [CRing.mul_assoc]
    rw [mul_left_comm (A ⟨0, by omega⟩ j) (rsign k.val)]
  rw [hExpand (swapRow01 M), hExpand M]
  rw [← sumFin_neg]
  rw [← sumFin_pairInv (fun j k =>
    (rsign j.val *ᵣ rsign k.val) *ᵣ
    (swapRow01 M ⟨0, by omega⟩ j *ᵣ swapRow01 M ⟨1, by omega⟩ (skipIdx j k)) *ᵣ
    det (minor (minor (swapRow01 M) ⟨0, by omega⟩ j) ⟨0, by omega⟩ k))]
  apply sumFin_congr; intro j
  rw [← sumFin_neg]
  apply sumFin_congr; intro k
  have hmin_eq :
      minor (minor (swapRow01 M) ⟨0, by omega⟩ (pairInvJ j k)) ⟨0, by omega⟩ (pairInvK j k) =
      minor (minor M ⟨0, by omega⟩ j) ⟨0, by omega⟩ k := by
    rw [pairInv_minor]
    funext a b
    unfold minor swapRow01
    simp only [skipIdx_zero, Fin.succ]
    have h0 : ¬ (a.val + 1 + 1 = 0) := by omega
    have h1 : ¬ (a.val + 1 + 1 = 1) := by omega
    simp only [h0, h1, ↓reduceIte]
  rw [hmin_eq, pairInv_sign]
  have hrow0 : swapRow01 M ⟨0, by omega⟩ (pairInvJ j k) = M ⟨1, by omega⟩ (skipIdx j k) := rfl
  have hrow1 : swapRow01 M ⟨1, by omega⟩ (skipIdx (pairInvJ j k) (pairInvK j k)) = M ⟨0, by omega⟩ j := by
    change M ⟨0, by omega⟩ (pairInvJ (pairInvJ j k) (pairInvK j k)) = M ⟨0, by omega⟩ j
    rw [pairInv_invol_j]
  rw [hrow0, hrow1, CRing.mul_comm (M ⟨1, by omega⟩ (skipIdx j k)), neg_mul, neg_mul]

theorem det_swapRowAdj {n : Nat} (M : Mat n R) (r : Nat) (hr : r + 1 < n) :
    det (swapRowAdj M r hr) = -ᵣ(det M) := by
  induction n generalizing r with
  | zero => omega
  | succ m ih =>
    cases r with
    | zero =>
      cases m with
      | zero => omega
      | succ m' => exact det_swapRow01 M
    | succ r' =>
      simp only [det_succ]
      rw [← sumFin_neg]
      apply sumFin_congr; intro j
      have h0 : swapRowAdj M (r' + 1) hr ⟨0, Nat.zero_lt_succ m⟩ j = M ⟨0, Nat.zero_lt_succ m⟩ j := by
        unfold swapRowAdj; simp
      rw [h0]
      have hmin : minor (swapRowAdj M (r' + 1) hr) ⟨0, Nat.zero_lt_succ m⟩ j =
                  swapRowAdj (minor M ⟨0, Nat.zero_lt_succ m⟩ j) r' (by omega) := by
        funext a b
        unfold minor swapRowAdj
        simp only [skipIdx_zero, Fin.succ]
        by_cases ha : a.val = r'
        · simp only [ha, ↓reduceIte]
        · by_cases ha1 : a.val = r' + 1
          · have hne1 : r' + 1 + 1 ≠ r' + 1 := by omega
            have hne2 : r' + 1 ≠ r' := by omega
            simp only [ha1, hne1, hne2, ↓reduceIte]
          · have hne1 : a.val + 1 ≠ r' + 1 := by omega
            have hne2 : a.val + 1 ≠ r' + 1 + 1 := by omega
            simp only [ha, ha1, hne1, hne2, ↓reduceIte]
      rw [hmin, ih (minor M ⟨0, Nat.zero_lt_succ m⟩ j) r' (by omega), mul_neg]

theorem det_moveRowToZero {n : Nat} (M : Mat (n + 1) R) (r : Fin (n + 1)) :
    det (moveRowToZero M r) = rsign r.val *ᵣ det M := by
  rcases r with ⟨rv, hrv⟩
  induction rv generalizing M with
  | zero =>
    rw [rsign_zero, CRing.one_mul]
    apply det_congr; intro i j
    unfold moveRowToZero skipIdx
    by_cases h0 : i.val = 0
    · simp only [h0, ↓reduceDIte]; congr 1; exact Fin.ext h0.symm
    · have hlt : ¬ (i.val - 1 < 0) := Nat.not_lt_zero _
      simp only [h0, hlt, ↓reduceDIte]
      congr 1; apply Fin.ext; simp; omega
  | succ k ih =>
    have hsw : moveRowToZero M ⟨k + 1, hrv⟩ =
               moveRowToZero (swapRowAdj M k hrv) ⟨k, Nat.lt_of_succ_lt hrv⟩ := by
      funext i j
      unfold moveRowToZero swapRowAdj skipIdx
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceDIte]
        by_cases h1 : i.val - 1 < k
        · have h2 : i.val - 1 < k + 1 := by omega
          have hne1 : i.val - 1 ≠ k := by omega
          have hne2 : i.val - 1 ≠ k + 1 := by omega
          simp only [h1, h2, hne1, hne2, ↓reduceDIte, ↓reduceIte]
        · by_cases h2 : i.val - 1 = k
          · simp only [h2]
            have hne1 : ¬ (k < k) := Nat.lt_irrefl k
            simp [hne1]
          · have hlt : ¬ (i.val - 1 < k + 1) := by omega
            have hne1 : i.val - 1 + 1 ≠ k := by omega
            have hne2 : i.val - 1 + 1 ≠ k + 1 := by omega
            simp only [h1, hlt, hne1, hne2, ↓reduceDIte, ↓reduceIte]
    rw [hsw, ih (swapRowAdj M k hrv) (Nat.lt_of_succ_lt hrv), det_swapRowAdj,
        mul_neg, rsign_succ, neg_mul]

/-- General Laplace expansion along ANY row `r : Fin (n + 1)`. -/
theorem det_laplace_row {n : Nat} (M : Mat (n + 1) R) (r : Fin (n + 1)) :
    det M = rsign r.val *ᵣ
      sumFin (fun j : Fin (n + 1) => rsign j.val *ᵣ M r j *ᵣ det (minor M r j)) := by
  have h := det_moveRowToZero M r
  have h1 : rsign r.val *ᵣ det (moveRowToZero M r) = det M := by
    rw [h, ← CRing.mul_assoc, rsign_mul_self, CRing.one_mul]
  rw [← h1]
  apply congrArg (CRing.mul (rsign r.val))
  rw [det_succ]
  apply sumFin_congr; intro j
  have hrow : moveRowToZero M r ⟨0, Nat.zero_lt_succ n⟩ j = M r j := by
    unfold moveRowToZero; simp
  have hmin : minor (moveRowToZero M r) ⟨0, Nat.zero_lt_succ n⟩ j = minor M r j := by
    funext a b
    unfold minor moveRowToZero
    rw [skipIdx_zero]
    simp [Fin.succ]
  rw [hrow, hmin]

theorem det_single_entry_row {n : Nat} (M : Mat (n + 1) R) (r c : Fin (n + 1)) (s : R)
    (hrow : ∀ j : Fin (n + 1), M r j = if j = c then s else zᵣ) :
    det M = rsign (r.val + c.val) *ᵣ s *ᵣ det (minor M r c) := by
  rw [det_laplace_row M r]
  rw [sumFin_single c]
  · simp only [hrow c, ↓reduceIte, rsign_add, CRing.mul_assoc]
  · intro j hj
    simp only [hrow j, hj, ↓reduceIte, mul_zero, zero_mul]

/-- If two distinct rows are equal, `det M = 0` (without dividing by 2!). -/
theorem det_eq_zero_of_row_eq {n : Nat} (M : Mat n R) (r1 r2 : Fin n)
    (hne : r1 ≠ r2) (heq : ∀ j, M r1 j = M r2 j) : det M = zᵣ := by
  cases n with
  | zero => exact Fin.elim0 r1
  | succ m =>
    cases m with
    | zero => exact absurd (Fin.ext (by omega)) hne
    | succ m' =>
      have h01 : ∀ (A : Mat (m' + 2) R), (∀ j, A ⟨0, by omega⟩ j = A ⟨1, by omega⟩ j) → det A = zᵣ := by
        intro A hA
        have hskew : ∀ (t : Nat) (F : Fin (t + 1) → Fin (t + 1) → R),
            (∀ a, F a a = zᵣ) → (∀ a b, F b a = -ᵣ(F a b)) →
            sumFin (fun a => sumFin (fun b => F a b)) = zᵣ := by
          intro t
          induction t with
          | zero =>
            intro F hdiag _
            simp only [sumFin_succ, sumFin_zero, hdiag, add_zero]
          | succ u ihu =>
            intro F hdiag hanti
            rw [sumFin_succ]
            rw [sumFin_succ (fun b => F ⟨0, by omega⟩ b), hdiag ⟨0, by omega⟩, CRing.zero_add]
            have hrest :
                sumFin (fun a : Fin (u + 1) => sumFin (fun b : Fin (u + 2) => F a.succ b)) =
                sumFin (fun a : Fin (u + 1) => F a.succ ⟨0, by omega⟩) +ᵣ
                sumFin (fun a : Fin (u + 1) => sumFin (fun b : Fin (u + 1) => F a.succ b.succ)) := by
              rw [← sumFin_add]
              apply sumFin_congr; intro a
              rw [sumFin_succ]
            rw [hrest, ihu (fun a b => F a.succ b.succ) (fun a => hdiag a.succ) (fun a b => hanti a.succ b.succ),
                add_zero]
            have hneg : sumFin (fun a : Fin (u + 1) => F a.succ ⟨0, by omega⟩) =
                        -ᵣ(sumFin (fun b : Fin (u + 1) => F ⟨0, by omega⟩ b.succ)) := by
              rw [← sumFin_neg]
              apply sumFin_congr; intro a
              exact hanti ⟨0, by omega⟩ a.succ
            rw [hneg, add_right_neg]
        let F : Fin (m' + 2) → Fin (m' + 2) → R := fun a b =>
          if h1 : a.val < b.val then
            (rsign a.val *ᵣ rsign (b.val - 1)) *ᵣ (A ⟨0, by omega⟩ a *ᵣ A ⟨1, by omega⟩ b) *ᵣ
            det (minor (minor A ⟨0, by omega⟩ a) ⟨0, by omega⟩ ⟨b.val - 1, by omega⟩)
          else if h2 : b.val < a.val then
            (rsign a.val *ᵣ rsign b.val) *ᵣ (A ⟨0, by omega⟩ a *ᵣ A ⟨1, by omega⟩ b) *ᵣ
            det (minor (minor A ⟨0, by omega⟩ a) ⟨0, by omega⟩ ⟨b.val, by omega⟩)
          else zᵣ
        have hdetF : det A = sumFin (fun a => sumFin (fun b => F a b)) := by
          rw [det_succ]
          apply sumFin_congr; intro a
          rw [det_succ, ← sumFin_mul_left]
          rw [sumFin_skip_zero a (F a) (by simp [F])]
          apply sumFin_congr; intro k
          have hm : minor A ⟨0, by omega⟩ a ⟨0, by omega⟩ k = A ⟨1, by omega⟩ (skipIdx a k) := by
            unfold minor; rw [skipIdx_zero]; rfl
          rw [hm]
          unfold F skipIdx
          by_cases hk : k.val < a.val
          · have hnot : ¬ (a.val < k.val) := by omega
            simp only [hk, hnot, ↓reduceDIte]
            simp only [CRing.mul_assoc]
            rw [mul_left_comm (A ⟨0, by omega⟩ a) (rsign k.val)]
          · have hlt : a.val < k.val + 1 := by omega
            simp only [hk, hlt, ↓reduceDIte]
            have hsub : k.val + 1 - 1 = k.val := by omega
            simp only [hsub, CRing.mul_assoc]
            rw [mul_left_comm (A ⟨0, by omega⟩ a) (rsign k.val)]
        rw [hdetF]
        apply hskew (m' + 1) F (fun a => by simp [F])
        intro a b
        unfold F
        by_cases h1 : a.val < b.val
        · have h1' : ¬ (b.val < a.val) := by omega
          simp only [h1, h1', ↓reduceDIte]
          have hsign : rsign (R := R) b.val *ᵣ rsign (R := R) a.val =
                       -ᵣ(rsign (R := R) a.val *ᵣ rsign (R := R) (b.val - 1)) := by
            rw [← rsign_add, ← rsign_add]
            have hsum : b.val + a.val = (a.val + (b.val - 1)) + 1 := by omega
            rw [hsum, rsign_succ]
          have hval : A ⟨0, by omega⟩ b *ᵣ A ⟨1, by omega⟩ a = A ⟨0, by omega⟩ a *ᵣ A ⟨1, by omega⟩ b := by
            rw [hA a, hA b, CRing.mul_comm]
          have hmin : minor (minor A ⟨0, by omega⟩ b) ⟨0, by omega⟩ ⟨a.val, by omega⟩ =
                      minor (minor A ⟨0, by omega⟩ a) ⟨0, by omega⟩ ⟨b.val - 1, by omega⟩ := by
            have hp := pairInv_minor A b ⟨a.val, by omega⟩
            have hj : pairInvJ b ⟨a.val, by omega⟩ = a := by
              unfold pairInvJ skipIdx; apply Fin.ext; simp [h1]
            have hk : pairInvK b ⟨a.val, by omega⟩ = ⟨b.val - 1, by omega⟩ := by
              unfold pairInvK; apply Fin.ext; simp [h1]
            rw [hj, hk] at hp
            exact hp.symm
          rw [hsign, hval, hmin, neg_mul, neg_mul]
        · by_cases h2 : b.val < a.val
          · simp only [h1, h2, ↓reduceDIte]
            have hsign : rsign (R := R) b.val *ᵣ rsign (R := R) (a.val - 1) =
                         -ᵣ(rsign (R := R) a.val *ᵣ rsign (R := R) b.val) := by
              rw [← rsign_add, ← rsign_add]
              have hsum : (b.val + (a.val - 1)) + 1 = a.val + b.val := by omega
              rw [← hsum, rsign_succ, neg_neg]
            have hval : A ⟨0, by omega⟩ b *ᵣ A ⟨1, by omega⟩ a = A ⟨0, by omega⟩ a *ᵣ A ⟨1, by omega⟩ b := by
              rw [hA a, hA b, CRing.mul_comm]
            have hmin : minor (minor A ⟨0, by omega⟩ b) ⟨0, by omega⟩ ⟨a.val - 1, by omega⟩ =
                        minor (minor A ⟨0, by omega⟩ a) ⟨0, by omega⟩ ⟨b.val, by omega⟩ := by
              have hp := pairInv_minor A a ⟨b.val, by omega⟩
              have hj : pairInvJ a ⟨b.val, by omega⟩ = b := by
                unfold pairInvJ skipIdx; apply Fin.ext; simp [h2]
              have hk : pairInvK a ⟨b.val, by omega⟩ = ⟨a.val - 1, by omega⟩ := by
                unfold pairInvK; apply Fin.ext; simp [h2]
              rw [hj, hk] at hp
              exact hp
            rw [hsign, hval, hmin, neg_mul, neg_mul]
          · simp only [h1, h2, ↓reduceDIte, neg_zero]
      let A1 := moveRowToZero M r1
      have hdet1 : det A1 = rsign r1.val *ᵣ det M := det_moveRowToZero M r1
      let r2' : Fin (m' + 1) :=
        if h : r2.val < r1.val then ⟨r2.val, by omega⟩ else ⟨r2.val - 1, by omega⟩
      have hr2' : skipIdx r1 r2' = r2 := by
        unfold r2' skipIdx
        apply Fin.ext
        by_cases h : r2.val < r1.val
        · simp [h]
        · have hne' : r2.val ≠ r1.val := fun hv => hne (Fin.ext hv.symm)
          have hnot : ¬ (r2.val - 1 < r1.val) := by omega
          simp [h, hnot]; omega
      let A2 := moveRowToZero A1 r2'.succ
      have hdet2 : det A2 = rsign r2'.succ.val *ᵣ det A1 := det_moveRowToZero A1 r2'.succ
      have hA2_eq : ∀ j, A2 ⟨0, by omega⟩ j = A2 ⟨1, by omega⟩ j := by
        intro j
        have hL : A2 ⟨0, by omega⟩ j = M r2 j := by
          unfold A2 moveRowToZero
          simp only [↓reduceDIte]
          unfold A1 moveRowToZero
          have hne0 : r2'.succ.val ≠ 0 := by simp [Fin.succ]
          simp only [hne0, ↓reduceDIte]
          have hsub : ⟨r2'.succ.val - 1, by omega⟩ = r2' := Fin.ext (by simp [Fin.succ])
          rw [hsub, hr2']
        have hR : A2 ⟨1, by omega⟩ j = M r1 j := by
          unfold A2 moveRowToZero
          have hne0 : (1 : Nat) ≠ 0 := by omega
          simp only [hne0, ↓reduceDIte]
          have hsk : skipIdx r2'.succ ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
            unfold skipIdx; apply Fin.ext; simp [Fin.succ]
          rw [hsk]
          unfold A1 moveRowToZero; simp
        rw [hL, hR, heq j]
      have hzero : det A2 = zᵣ := h01 A2 hA2_eq
      rw [hdet2, hdet1] at hzero
      have hmul : rsign r1.val *ᵣ (rsign r2'.succ.val *ᵣ (rsign r2'.succ.val *ᵣ (rsign r1.val *ᵣ det M))) = zᵣ := by
        rw [hzero, mul_zero, mul_zero]
      rw [← CRing.mul_assoc (rsign r2'.succ.val), rsign_mul_self, CRing.one_mul,
          ← CRing.mul_assoc (rsign r1.val), rsign_mul_self, CRing.one_mul] at hmul
      exact hmul

/-- Block lower-triangular determinant:
if `M i j = 0` whenever `i < a` and `a ≤ j`, then `det M = det M_TL * det M_BR`. -/
theorem det_blockLower {a b : Nat} (M : Mat (a + b) R)
    (hzero : ∀ (i : Fin a) (j : Fin b),
      M ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩
        ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩ = zᵣ) :
    det M =
      det (fun i j : Fin a =>
        M ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right a b)⟩) *ᵣ
      det (fun i j : Fin b =>
        M ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩
          ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) := by
  induction a with
  | zero =>
    rw [det_zero_dim, CRing.one_mul, det_cast (Nat.zero_add b) M]
    apply det_congr; intro i j
    congr 1 <;> (apply Fin.ext; simp)
  | succ k ih =>
    have heq : k + 1 + b = (k + b) + 1 := by omega
    rw [det_cast heq M, det_succ]
    rw [sumFin_cast (by omega : (k + b) + 1 = (k + 1) + b)]
    rw [sumFin_append]
    have hright :
        sumFin (fun j : Fin b =>
          rsign (k + 1 + j.val) *ᵣ
          M ⟨0, by omega⟩ ⟨k + 1 + j.val, by omega⟩ *ᵣ
          det (minor (fun i c : Fin ((k + b) + 1) => M ⟨i.val, by omega⟩ ⟨c.val, by omega⟩)
                ⟨0, by omega⟩ ⟨k + 1 + j.val, by omega⟩)) = zᵣ := by
      rw [sumFin_congr (g := fun _ => zᵣ)]
      · exact sumFin_const_zero
      · intro j
        have hz := hzero ⟨0, Nat.zero_lt_succ k⟩ j
        rw [hz, mul_zero, zero_mul]
    rw [hright, add_zero]
    rw [det_succ, ← sumFin_mul_right]
    apply sumFin_congr; intro j
    let M' : Mat (k + b) R :=
      minor (fun i c : Fin ((k + b) + 1) => M ⟨i.val, by omega⟩ ⟨c.val, by omega⟩)
        ⟨0, by omega⟩ ⟨j.val, by have := j.isLt; omega⟩
    have hM'zero : ∀ (i : Fin k) (c : Fin b),
        M' ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right k b)⟩
           ⟨k + c.val, Nat.add_lt_add_left c.isLt k⟩ = zᵣ := by
      intro i c
      unfold M' minor
      rw [skipIdx_zero]
      have hsk : skipIdx ⟨j.val, by have := j.isLt; omega⟩ ⟨k + c.val, Nat.add_lt_add_left c.isLt k⟩ =
                 ⟨k + 1 + c.val, by have := c.isLt; omega⟩ := by
        unfold skipIdx; apply Fin.ext
        have hjlt : j.val < k + 1 := j.isLt
        have hnot : ¬ (k + c.val < j.val) := by omega
        simp [hnot]; omega
      rw [hsk]
      exact hzero ⟨i.val + 1, by omega⟩ c
    have hih := ih M' hM'zero
    have hTL :
        det (fun a1 a2 : Fin k => M' ⟨a1.val, Nat.lt_of_lt_of_le a1.isLt (Nat.le_add_right k b)⟩
                                     ⟨a2.val, Nat.lt_of_lt_of_le a2.isLt (Nat.le_add_right k b)⟩) =
        det (minor (fun i c : Fin (k + 1) =>
          M ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right (k + 1) b)⟩
            ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.le_add_right (k + 1) b)⟩) ⟨0, Nat.zero_lt_succ k⟩ j) := by
      apply det_congr; intro a1 a2
      unfold M' minor
      rw [skipIdx_zero, skipIdx_zero]
      unfold skipIdx
      by_cases hlt : a2.val < j.val
      · simp [hlt]
      · simp [hlt]
    have hBR :
        det (fun b1 b2 : Fin b => M' ⟨k + b1.val, Nat.add_lt_add_left b1.isLt k⟩
                                     ⟨k + b2.val, Nat.add_lt_add_left b2.isLt k⟩) =
        det (fun b1 b2 : Fin b =>
          M ⟨k + 1 + b1.val, Nat.add_lt_add_left b1.isLt (k + 1)⟩
            ⟨k + 1 + b2.val, Nat.add_lt_add_left b2.isLt (k + 1)⟩) := by
      apply det_congr; intro b1 b2
      unfold M' minor
      rw [skipIdx_zero]
      have hsk : skipIdx ⟨j.val, by have := j.isLt; omega⟩ ⟨k + b2.val, Nat.add_lt_add_left b2.isLt k⟩ =
                 ⟨k + 1 + b2.val, by have := b2.isLt; omega⟩ := by
        unfold skipIdx; apply Fin.ext
        have hjlt : j.val < k + 1 := j.isLt
        have hnot : ¬ (k + b2.val < j.val) := by omega
        simp [hnot]; omega
      rw [hsk]
      have hrow : (⟨k + b1.val, Nat.add_lt_add_left b1.isLt k⟩ : Fin (k + b)).succ.val = k + 1 + b1.val := by
        simp [Fin.succ]; omega
      dsimp only
      congr 1; exact Fin.ext hrow
    rw [hTL, hBR] at hih
    have hres := congrArg (CRing.mul (rsign j.val *ᵣ M ⟨0, by omega⟩ ⟨j.val, by have := j.isLt; omega⟩)) hih
    rw [← CRing.mul_assoc] at hres
    exact hres

/-- Block upper-triangular determinant:
if `M i j = 0` whenever `a ≤ i` and `j < a`, then `det M = det M_TL * det M_BR`. -/
theorem det_blockUpper {a b : Nat} (M : Mat (a + b) R)
    (hzero : ∀ (i : Fin b) (j : Fin a),
      M ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩
        ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right a b)⟩ = zᵣ) :
    det M =
      det (fun i j : Fin a =>
        M ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right a b)⟩) *ᵣ
      det (fun i j : Fin b =>
        M ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩
          ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) := by
  induction b with
  | zero =>
    rw [det_zero_dim, mul_one]
    exact det_congr (fun _ _ => rfl)
  | succ k ih =>
    have ha_lt : a < a + (k + 1) := by omega
    rw [det_laplace_row M ⟨a, ha_lt⟩]
    rw [sumFin_append (a := a) (b := k + 1)]
    have hleft :
        sumFin (fun j : Fin a =>
          rsign j.val *ᵣ M ⟨a, ha_lt⟩ ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right a (k + 1))⟩ *ᵣ
          det (minor M ⟨a, ha_lt⟩ ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right a (k + 1))⟩)) = zᵣ := by
      rw [sumFin_congr (g := fun _ => zᵣ)]
      · exact sumFin_const_zero
      · intro j
        have hz := hzero ⟨0, Nat.zero_lt_succ k⟩ j
        simp only [Nat.add_zero] at hz
        rw [hz, mul_zero, zero_mul]
    rw [hleft, CRing.zero_add]
    rw [det_succ (fun i j : Fin (k + 1) =>
      M ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩ ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩)]
    rw [← sumFin_mul_left, ← sumFin_mul_left]
    apply sumFin_congr; intro j
    have hsign : rsign (R := R) a *ᵣ rsign (R := R) (a + j.val) = rsign (R := R) j.val := by
      rw [rsign_add, ← CRing.mul_assoc, rsign_mul_self, CRing.one_mul]
    let M' : Mat (a + k) R := minor M ⟨a, ha_lt⟩ ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩
    have hM'zero : ∀ (i : Fin k) (c : Fin a),
        M' ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩
           ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.le_add_right a k)⟩ = zᵣ := by
      intro i c
      unfold M' minor
      have hskR : skipIdx ⟨a, ha_lt⟩ ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩ =
                  ⟨a + (i.val + 1), Nat.add_lt_add_left (Nat.succ_lt_succ i.isLt) a⟩ := by
        unfold skipIdx; apply Fin.ext
        have hnot : ¬ (a + i.val < a) := by omega
        simp [hnot]; omega
      have hskC : skipIdx ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩
                    ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.le_add_right a k)⟩ =
                  ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.le_add_right a (k + 1))⟩ := by
        unfold skipIdx; apply Fin.ext
        have hlt : c.val < a + j.val := by have := c.isLt; omega
        simp [hlt]
      rw [hskR, hskC]
      exact hzero ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ c
    have hih := ih M' hM'zero
    have hTL :
        (fun i c : Fin a =>
          M' ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a k)⟩
             ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.le_add_right a k)⟩) =
        (fun i c : Fin a =>
          M ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a (k + 1))⟩
            ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.le_add_right a (k + 1))⟩) := by
      funext i c; unfold M' minor skipIdx
      have h1 : i.val < a := i.isLt
      have h2 : c.val < a + j.val := by have := c.isLt; omega
      simp [h1, h2]
    have hBR :
        (fun i c : Fin k =>
          M' ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩
             ⟨a + c.val, Nat.add_lt_add_left c.isLt a⟩) =
        minor (fun i c : Fin (k + 1) =>
          M ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩
            ⟨a + c.val, Nat.add_lt_add_left c.isLt a⟩) ⟨0, Nat.zero_lt_succ k⟩ j := by
      funext i c; unfold M' minor
      rw [skipIdx_zero]
      unfold skipIdx
      have hnot : ¬ (a + i.val < a) := by omega
      simp only [hnot, ↓reduceDIte]
      by_cases hc : c.val < j.val
      · have hca : a + c.val < a + j.val := by omega
        simp only [hc, hca, ↓reduceDIte]
        congr 1
      · have hca : ¬ (a + c.val < a + j.val) := by omega
        simp only [hc, hca, ↓reduceDIte]
        congr 1
    rw [hTL, hBR] at hih
    change rsign a *ᵣ (rsign (a + j.val) *ᵣ M ⟨a, ha_lt⟩ ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩ *ᵣ det M') = _
    rw [hih]
    have hM0 : M ⟨a + 0, by omega⟩ ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩ =
               M ⟨a, ha_lt⟩ ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩ := rfl
    rw [hM0]
    let dTL := det (fun i c : Fin a =>
      M ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a (k + 1))⟩
        ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.le_add_right a (k + 1))⟩)
    let dBR := det (minor (fun i c : Fin (k + 1) =>
      M ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩
        ⟨a + c.val, Nat.add_lt_add_left c.isLt a⟩) ⟨0, Nat.zero_lt_succ k⟩ j)
    let mVal := M ⟨a, ha_lt⟩ ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩
    change rsign a *ᵣ (rsign (a + j.val) *ᵣ mVal *ᵣ (dTL *ᵣ dBR)) =
           dTL *ᵣ (rsign j.val *ᵣ mVal *ᵣ dBR)
    calc rsign a *ᵣ (rsign (a + j.val) *ᵣ mVal *ᵣ (dTL *ᵣ dBR))
        = (rsign a *ᵣ rsign (a + j.val)) *ᵣ (mVal *ᵣ (dTL *ᵣ dBR)) := by
          simp only [CRing.mul_assoc]
      _ = rsign j.val *ᵣ (mVal *ᵣ (dTL *ᵣ dBR)) := by rw [hsign]
      _ = dTL *ᵣ (rsign j.val *ᵣ mVal *ᵣ dBR) := by
          simp only [CRing.mul_assoc]
          rw [mul_left_comm mVal dTL, mul_left_comm (rsign j.val) dTL]

end DetTheory
section PortalTransfer
variable {R : Type} [CRing R]

private theorem fin_ne {n : Nat} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b :=
  fun heq => h (congrArg Fin.val heq)

/-- Master Junction-Splitting Identity:
For any `(a + 1 + b) × (a + 1 + b)` matrix `K` whose top-right `a × b` and bottom-left `b × a`
blocks vanish, if `K` is built by gluing `L : Mat (a + 1) R` and `U : Mat (b + 1) R` at index `a`
with junction shift `s`, then:
  `det K = det L * det U_{>0} + det L_{<a} * det U + s * det L_{<a} * det U_{>0}`. -/
theorem det_junction {a b : Nat} (L : Mat (a + 1) R) (U : Mat (b + 1) R) (s : R) :
    let K : Mat (a + 1 + b) R := fun i j =>
      if hi1 : i.val < a then
        if hj1 : j.val ≤ a then L ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ else zᵣ
      else if hi2 : i.val = a then
        if hj1 : j.val < a then L ⟨a, by omega⟩ ⟨j.val, by omega⟩
        else if _hj2 : j.val = a then L ⟨a, by omega⟩ ⟨a, by omega⟩ +ᵣ U ⟨0, by omega⟩ ⟨0, by omega⟩ +ᵣ s
        else U ⟨0, by omega⟩ ⟨j.val - a, by omega⟩
      else
        if hj1 : j.val < a then zᵣ else U ⟨i.val - a, by omega⟩ ⟨j.val - a, by omega⟩
    det K =
      det L *ᵣ det (minor U ⟨0, Nat.zero_lt_succ b⟩ ⟨0, Nat.zero_lt_succ b⟩) +ᵣ
      det (minor L ⟨a, Nat.lt_succ_self a⟩ ⟨a, Nat.lt_succ_self a⟩) *ᵣ det U +ᵣ
      s *ᵣ (det (minor L ⟨a, Nat.lt_succ_self a⟩ ⟨a, Nat.lt_succ_self a⟩) *ᵣ
            det (minor U ⟨0, Nat.zero_lt_succ b⟩ ⟨0, Nat.zero_lt_succ b⟩)) := by
  intro K
  let rowA : Fin (a + 1 + b) := ⟨a, by omega⟩
  let v1 : Fin (a + 1 + b) → R := fun j =>
    if hj : j.val ≤ a then L ⟨a, by omega⟩ ⟨j.val, by omega⟩ else zᵣ
  let v2 : Fin (a + 1 + b) → R := fun j =>
    if hj : j.val < a then zᵣ else U ⟨0, by omega⟩ ⟨j.val - a, by omega⟩
  let v3 : Fin (a + 1 + b) → R := fun j => if j = rowA then s else zᵣ
  have hKsplit : K = updateRow K rowA (fun j => (v1 j +ᵣ v2 j) +ᵣ v3 j) := by
    funext i j
    unfold updateRow
    by_cases hir : i = rowA
    · subst hir
      simp only [↓reduceIte]
      unfold K v1 v2 v3 rowA
      have h1 : ¬ (a < a) := Nat.lt_irrefl a
      simp only [h1, ↓reduceDIte]
      by_cases hja : j.val < a
      · have hle : j.val ≤ a := by omega
        have hne : j ≠ ⟨a, by omega⟩ := fin_ne (by simp; omega)
        simp only [hja, hle, hne, ↓reduceDIte, ↓reduceIte, add_zero]
      · by_cases hje : j.val = a
        · have heq : j = ⟨a, by omega⟩ := Fin.ext hje
          simp only [heq, ↓reduceIte]
          have hsub : a - a = 0 := Nat.sub_self a
          have hna : ¬ (a < a) := Nat.lt_irrefl a
          have hale : a ≤ a := Nat.le_refl a
          simp only [hna, hale, hsub, ↓reduceDIte]
        · have hle : ¬ (j.val ≤ a) := by omega
          have hne : j ≠ ⟨a, by omega⟩ := fin_ne (by simp; omega)
          simp only [hja, hje, hle, hne, ↓reduceDIte, ↓reduceIte, CRing.zero_add, add_zero]
    · simp [hir]
  rw [hKsplit, det_updateRow_add, det_updateRow_add]
  -- Term 1: updateRow K rowA v1 is block lower-triangular with blocks (a+1) and b!
  have hT1 : det (updateRow K rowA v1) =
      det L *ᵣ det (minor U ⟨0, Nat.zero_lt_succ b⟩ ⟨0, Nat.zero_lt_succ b⟩) := by
    rw [det_blockLower (a := a + 1) (b := b)]
    · have hL :
          (fun i j : Fin (a + 1) =>
            updateRow K rowA v1 ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right (a + 1) b)⟩
                                ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right (a + 1) b)⟩) = L := by
        funext i j
        unfold updateRow K v1 rowA
        by_cases hia : i.val = a
        · have heq : (⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right (a + 1) b)⟩ : Fin (a + 1 + b)) =
                     ⟨a, by omega⟩ := Fin.ext hia
          have hjle : j.val ≤ a := by have := j.isLt; omega
          simp only [heq, ↓reduceIte, hjle, ↓reduceDIte]
          congr 1; exact Fin.ext hia.symm
        · have hne : (⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right (a + 1) b)⟩ : Fin (a + 1 + b)) ≠
                     ⟨a, by omega⟩ := fin_ne (by simp; omega)
          have hilt : i.val < a := by have := i.isLt; omega
          have hjle : j.val ≤ a := by have := j.isLt; omega
          simp only [hne, ↓reduceIte, hilt, hjle, ↓reduceDIte]
      have hU :
          (fun i j : Fin b =>
            updateRow K rowA v1 ⟨a + 1 + i.val, Nat.add_lt_add_left i.isLt (a + 1)⟩
                                ⟨a + 1 + j.val, Nat.add_lt_add_left j.isLt (a + 1)⟩) =
          minor U ⟨0, Nat.zero_lt_succ b⟩ ⟨0, Nat.zero_lt_succ b⟩ := by
        funext i j
        unfold updateRow K minor rowA
        rw [skipIdx_zero, skipIdx_zero]
        have hne : (⟨a + 1 + i.val, Nat.add_lt_add_left i.isLt (a + 1)⟩ : Fin (a + 1 + b)) ≠ ⟨a, by omega⟩ :=
          fin_ne (by simp; omega)
        have h1 : ¬ (a + 1 + i.val < a) := by omega
        have h2 : ¬ (a + 1 + i.val = a) := by omega
        have h3 : ¬ (a + 1 + j.val < a) := by omega
        simp only [hne, ↓reduceIte, h1, h2, h3, ↓reduceDIte]
        congr 1 <;> (apply Fin.ext; simp [Fin.succ]; omega)
      rw [hL, hU]
    · intro i j
      unfold updateRow K v1 rowA
      by_cases hia : i.val = a
      · have heq : (⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right (a + 1) b)⟩ : Fin (a + 1 + b)) =
                   ⟨a, by omega⟩ := Fin.ext hia
        have hnot : ¬ (a + 1 + j.val ≤ a) := by omega
        simp only [heq, ↓reduceIte, hnot, ↓reduceDIte]
      · have hne : (⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right (a + 1) b)⟩ : Fin (a + 1 + b)) ≠
                   ⟨a, by omega⟩ := fin_ne (by simp; omega)
        have hilt : i.val < a := by have := i.isLt; omega
        have hnot : ¬ (a + 1 + j.val ≤ a) := by omega
        simp only [hne, ↓reduceIte, hilt, hnot, ↓reduceDIte]
  -- Term 2: updateRow K rowA v2 is block upper-triangular with blocks a and (b+1)!
  have hT2 : det (updateRow K rowA v2) =
      det (minor L ⟨a, Nat.lt_succ_self a⟩ ⟨a, Nat.lt_succ_self a⟩) *ᵣ det U := by
    have hsz : a + 1 + b = a + (b + 1) := by omega
    rw [det_cast hsz (updateRow K rowA v2)]
    rw [det_blockUpper (a := a) (b := b + 1)]
    · have hL :
          (fun i j : Fin a =>
            updateRow K rowA v2 ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩) =
          minor L ⟨a, Nat.lt_succ_self a⟩ ⟨a, Nat.lt_succ_self a⟩ := by
        funext i j
        unfold updateRow K minor rowA
        rw [skipIdx_last, skipIdx_last]
        have hilt : i.val < a := i.isLt
        have hjle : j.val ≤ a := by have := j.isLt; omega
        have hne : (⟨i.val, by omega⟩ : Fin (a + 1 + b)) ≠ ⟨a, by omega⟩ := fin_ne (by simp; omega)
        simp only [hne, ↓reduceIte, hilt, hjle, ↓reduceDIte]
      have hU :
          (fun i j : Fin (b + 1) =>
            updateRow K rowA v2 ⟨a + i.val, by have := i.isLt; omega⟩ ⟨a + j.val, by have := j.isLt; omega⟩) = U := by
        funext i j
        unfold updateRow K v2 rowA
        by_cases hi0 : i.val = 0
        · have heq : (⟨a + i.val, by have := i.isLt; omega⟩ : Fin (a + 1 + b)) = ⟨a, by omega⟩ :=
            Fin.ext (by simp [hi0])
          have hnot : ¬ (a + j.val < a) := by omega
          simp only [heq, ↓reduceIte, hnot, ↓reduceDIte]
          congr 1
          · exact Fin.ext hi0.symm
          · apply Fin.ext; simp
        · have hne : (⟨a + i.val, by have := i.isLt; omega⟩ : Fin (a + 1 + b)) ≠ ⟨a, by omega⟩ :=
            fin_ne (by dsimp only; omega)
          have h1 : ¬ (a + i.val < a) := by omega
          have h2 : ¬ (a + i.val = a) := by intro h; exact hi0 (by omega)
          have h3 : ¬ (a + j.val < a) := by omega
          simp only [hne, ↓reduceIte, h1, h2, h3, ↓reduceDIte]
          congr 1 <;> (apply Fin.ext; simp)
      rw [hL, hU]
    · intro i j
      unfold updateRow K v2 rowA
      by_cases hi0 : i.val = 0
      · have heq : (⟨a + i.val, by have := i.isLt; omega⟩ : Fin (a + 1 + b)) = ⟨a, by omega⟩ :=
          Fin.ext (by simp [hi0])
        have hjlt : j.val < a := j.isLt
        simp only [heq, ↓reduceIte, hjlt, ↓reduceDIte]
      · have hne : (⟨a + i.val, by have := i.isLt; omega⟩ : Fin (a + 1 + b)) ≠ ⟨a, by omega⟩ :=
          fin_ne (by dsimp only; omega)
        have h1 : ¬ (a + i.val < a) := by omega
        have h2 : ¬ (a + i.val = a) := by intro h; exact hi0 (by omega)
        have hjlt : j.val < a := j.isLt
        simp only [hne, ↓reduceIte, h1, h2, hjlt, ↓reduceDIte]
  -- Term 3: updateRow K rowA v3 has single entry `s` at (a, a)!
  have hT3 : det (updateRow K rowA v3) =
      s *ᵣ (det (minor L ⟨a, Nat.lt_succ_self a⟩ ⟨a, Nat.lt_succ_self a⟩) *ᵣ
            det (minor U ⟨0, Nat.zero_lt_succ b⟩ ⟨0, Nat.zero_lt_succ b⟩)) := by
    have hsz : a + 1 + b = (a + b) + 1 := by omega
    rw [det_cast hsz (updateRow K rowA v3)]
    let rowA' : Fin ((a + b) + 1) := ⟨a, by omega⟩
    rw [det_single_entry_row (r := rowA') (c := rowA') (s := s)]
    · have hsign : rsign (R := R) (rowA'.val + rowA'.val) = eᵣ := by
        unfold rsign; have h : (a + a) % 2 = 0 := by omega
        simp only [rowA', h, ↓reduceIte]
      rw [hsign, CRing.one_mul]
      apply congrArg (CRing.mul s)
      rw [det_blockLower (a := a) (b := b)]
      · have hL :
            (fun i j : Fin a =>
              minor (fun r c : Fin ((a + b) + 1) => updateRow K rowA v3 ⟨r.val, by omega⟩ ⟨c.val, by omega⟩)
                rowA' rowA' ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩
                            ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right a b)⟩) =
            minor L ⟨a, Nat.lt_succ_self a⟩ ⟨a, Nat.lt_succ_self a⟩ := by
          funext i j
          unfold minor skipIdx updateRow K rowA rowA'
          have hi : i.val < a := i.isLt
          have hj : j.val < a := j.isLt
          have hjle : j.val ≤ a := by omega
          have hne : (⟨i.val, by omega⟩ : Fin (a + 1 + b)) ≠ ⟨a, by omega⟩ := fin_ne (by simp; omega)
          simp only [hi, hj, hjle, hne, ↓reduceDIte, ↓reduceIte]
        have hU :
            (fun i j : Fin b =>
              minor (fun r c : Fin ((a + b) + 1) => updateRow K rowA v3 ⟨r.val, by omega⟩ ⟨c.val, by omega⟩)
                rowA' rowA' ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩
                            ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) =
            minor U ⟨0, Nat.zero_lt_succ b⟩ ⟨0, Nat.zero_lt_succ b⟩ := by
          funext i j
          unfold minor skipIdx updateRow K rowA rowA'
          have hni : ¬ (a + i.val < a) := by omega
          have hnj : ¬ (a + j.val < a) := by omega
          have hne : (⟨a + i.val + 1, by omega⟩ : Fin (a + 1 + b)) ≠ ⟨a, by omega⟩ := fin_ne (by simp; omega)
          have h1 : ¬ (a + i.val + 1 < a) := by omega
          have h2 : ¬ (a + i.val + 1 = a) := by omega
          have h3 : ¬ (a + j.val + 1 < a) := by omega
          have h0i : ¬ (i.val < 0) := Nat.not_lt_zero _
          have h0j : ¬ (j.val < 0) := Nat.not_lt_zero _
          simp only [hni, hnj, hne, h1, h2, h3, h0i, h0j, ↓reduceDIte, ↓reduceIte]
          congr 1 <;> (apply Fin.ext; simp; omega)
        rw [hL, hU]
      · intro i j
        unfold minor skipIdx updateRow K rowA rowA'
        have hi : i.val < a := i.isLt
        have hnj : ¬ (a + j.val < a) := by omega
        have hne : (⟨i.val, by omega⟩ : Fin (a + 1 + b)) ≠ ⟨a, by omega⟩ := fin_ne (by simp; omega)
        have hnotle : ¬ (a + j.val + 1 ≤ a) := by omega
        simp only [hi, hnj, hne, hnotle, ↓reduceDIte, ↓reduceIte]
    · intro j
      unfold updateRow v3 rowA rowA'
      simp only [↓reduceIte]
      by_cases hj : j = ⟨a, by omega⟩
      · subst hj; simp
      · have hne : (⟨j.val, by omega⟩ : Fin (a + 1 + b)) ≠ ⟨a, by omega⟩ :=
          fin_ne (fun hv => hj (Fin.ext (by simp at hv; exact hv)))
        simp [hj, hne]
  rw [hT1, hT2, hT3]

/-! ### Theorem A1: Portal Perturbation Transfer Law (Exact, Division-Free, Any CRing R) -/

theorem portalTuple_perturb {n : Nat} (M : Mat (n + 2) R) (p q1 q2 r : R) :
    portalTuple (perturb M p q1 q2 r) = stepPerturb (portalTuple M) p q1 q2 r := by
  have hn0 : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have hdLR :
      det (minor (minor (perturb M p q1 q2 r) ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n, by omega⟩ ⟨n, by omega⟩) =
      det (minor (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n, by omega⟩ ⟨n, by omega⟩) := by
    apply det_congr; intro i j
    unfold minor perturb
    simp only [skipIdx_last, skipIdx_zero, Fin.succ]
    have h1 : i.val + 1 ≠ 0 := by omega
    have h2 : i.val + 1 ≠ n + 1 := by have := i.isLt; omega
    simp only [h1, h2, false_and, ↓reduceIte, add_zero]
  have hdL :
      det (minor (perturb M p q1 q2 r) ⟨0, by omega⟩ ⟨0, by omega⟩) =
      det (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) +ᵣ
      r *ᵣ det (minor (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n, by omega⟩ ⟨n, by omega⟩) := by
    let A := minor M ⟨0, by omega⟩ ⟨0, by omega⟩
    let lastN : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    have hEq : minor (perturb M p q1 q2 r) ⟨0, by omega⟩ ⟨0, by omega⟩ =
               updateRow A lastN (fun j => A lastN j +ᵣ (if j = lastN then r else zᵣ)) := by
      funext i j
      unfold updateRow A lastN
      by_cases hi : i.val = n
      · have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi
        rw [hieq]
        simp only [↓reduceIte]
        unfold minor perturb
        simp only [skipIdx_zero, Fin.succ]
        have h3 : j.val + 1 ≠ 0 := by omega
        by_cases hj : j.val = n
        · have hjeq : j = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hj
          rw [hjeq]
          simp only [↓reduceIte, hn0, false_and, and_false, and_self]
        · have hjne : j ≠ ⟨n, Nat.lt_succ_self n⟩ := fin_ne hj
          have hj2 : j.val + 1 ≠ n + 1 := by omega
          simp only [hjne, hn0, h3, hj2, and_false, ↓reduceIte]
      · have hine : i ≠ ⟨n, Nat.lt_succ_self n⟩ := fin_ne hi
        simp only [hine, ↓reduceIte]
        unfold minor perturb
        simp only [skipIdx_zero, Fin.succ]
        have h1 : i.val + 1 ≠ 0 := by omega
        have h2 : i.val + 1 ≠ n + 1 := by omega
        simp only [h1, h2, false_and, ↓reduceIte, add_zero]
    rw [hEq, det_updateRow_add, updateRow_self]
    apply congrArg (CRing.add _)
    rw [det_single_entry_row (r := lastN) (c := lastN) (s := r)]
    · have hsign : rsign (R := R) (lastN.val + lastN.val) = eᵣ := by
        unfold rsign; have h : (n + n) % 2 = 0 := by omega
        simp only [lastN, h, ↓reduceIte]
      rw [hsign, CRing.one_mul]
      apply congrArg (CRing.mul r)
      apply det_congr; intro a b
      unfold minor updateRow A lastN
      rw [skipIdx_last, skipIdx_last]
      have hne : (⟨a.val, Nat.lt_succ_of_lt a.isLt⟩ : Fin (n + 1)) ≠ ⟨n, Nat.lt_succ_self n⟩ :=
        fin_ne (by simp; have := a.isLt; omega)
      simp only [hne, ↓reduceIte]
      rfl
    · intro j; unfold updateRow; simp
  have hdR :
      det (minor (perturb M p q1 q2 r) ⟨n + 1, by omega⟩ ⟨n + 1, by omega⟩) =
      det (minor M ⟨n + 1, by omega⟩ ⟨n + 1, by omega⟩) +ᵣ
      p *ᵣ det (minor (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n, by omega⟩ ⟨n, by omega⟩) := by
    let A := minor M ⟨n + 1, by omega⟩ ⟨n + 1, by omega⟩
    let fstN : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    have hEq : minor (perturb M p q1 q2 r) ⟨n + 1, by omega⟩ ⟨n + 1, by omega⟩ =
               updateRow A fstN (fun j => A fstN j +ᵣ (if j = fstN then p else zᵣ)) := by
      funext i j
      unfold updateRow A fstN
      by_cases hi : i.val = 0
      · have hieq : i = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hi
        rw [hieq]
        simp only [↓reduceIte]
        unfold minor perturb
        simp only [skipIdx_last]
        have h2 : j.val ≠ n + 1 := by have := j.isLt; omega
        by_cases hj : j.val = 0
        · have hjeq : j = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hj
          rw [hjeq]
          simp only [↓reduceIte, and_self]
        · have hjne : j ≠ ⟨0, Nat.zero_lt_succ n⟩ := fin_ne hj
          simp only [hjne, hj, h2, hn0.symm, and_false, ↓reduceIte]
      · have hine : i ≠ ⟨0, Nat.zero_lt_succ n⟩ := fin_ne hi
        simp only [hine, ↓reduceIte]
        unfold minor perturb
        simp only [skipIdx_last]
        have h2 : i.val ≠ n + 1 := by have := i.isLt; omega
        simp only [hi, h2, false_and, ↓reduceIte, add_zero]
    rw [hEq, det_updateRow_add, updateRow_self]
    apply congrArg (CRing.add _)
    rw [det_single_entry_row (r := fstN) (c := fstN) (s := p)]
    · have hsign : rsign (R := R) (fstN.val + fstN.val) = eᵣ := rfl
      rw [hsign, CRing.one_mul]
      apply congrArg (CRing.mul p)
      apply det_congr; intro a b
      unfold minor updateRow A fstN
      simp only [skipIdx_zero, skipIdx_last]
      have hne : a.succ ≠ ⟨0, Nat.zero_lt_succ n⟩ := Fin.succ_ne_zero a
      simp only [hne, ↓reduceIte]
      unfold minor
      simp only [skipIdx_last, Fin.succ]
    · intro j; unfold updateRow; simp
  have hd0R :
      rsign (n + 1) *ᵣ det (minor (perturb M p q1 q2 r) ⟨0, by omega⟩ ⟨n + 1, by omega⟩) =
      rsign (n + 1) *ᵣ det (minor M ⟨0, by omega⟩ ⟨n + 1, by omega⟩) -ᵣ
      q2 *ᵣ det (minor (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n, by omega⟩ ⟨n, by omega⟩) := by
    let A := minor M ⟨0, by omega⟩ ⟨n + 1, by omega⟩
    let lastN : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let fstN : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    have hEq : minor (perturb M p q1 q2 r) ⟨0, by omega⟩ ⟨n + 1, by omega⟩ =
               updateRow A lastN (fun j => A lastN j +ᵣ (if j = fstN then q2 else zᵣ)) := by
      funext i j
      unfold updateRow A lastN fstN
      by_cases hi : i.val = n
      · have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi
        rw [hieq]
        simp only [↓reduceIte]
        unfold minor perturb
        simp only [skipIdx_zero, skipIdx_last, Fin.succ]
        have h3 : j.val ≠ n + 1 := by have := j.isLt; omega
        by_cases hj : j.val = 0
        · have hjeq : j = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hj
          rw [hjeq]
          simp only [↓reduceIte, hn0, false_and, and_self]
        · have hjne : j ≠ ⟨0, Nat.zero_lt_succ n⟩ := fin_ne hj
          simp only [hjne, hn0, hj, h3, and_false, ↓reduceIte]
      · have hine : i ≠ ⟨n, Nat.lt_succ_self n⟩ := fin_ne hi
        simp only [hine, ↓reduceIte]
        unfold minor perturb
        simp only [skipIdx_zero, skipIdx_last, Fin.succ]
        have h1 : i.val + 1 ≠ 0 := by omega
        have h2 : i.val + 1 ≠ n + 1 := by omega
        simp only [h1, h2, false_and, ↓reduceIte, add_zero]
    rw [hEq, det_updateRow_add, updateRow_self, CRing.left_distrib]
    unfold rsub
    apply congrArg (CRing.add _)
    rw [det_single_entry_row (r := lastN) (c := fstN) (s := q2)]
    · have hsign : rsign (R := R) (n + 1) *ᵣ rsign (R := R) (lastN.val + fstN.val) = -ᵣeᵣ := by
        rw [← rsign_add]; unfold rsign lastN fstN
        have hodd : (n + 1 + (n + 0)) % 2 ≠ 0 := by omega
        simp only [hodd, ↓reduceIte]
      have hmin :
          det (minor (updateRow A lastN (fun j => if j = fstN then q2 else zᵣ)) lastN fstN) =
          det (minor (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n, by omega⟩ ⟨n, by omega⟩) := by
        apply det_congr; intro a b
        unfold minor updateRow A lastN fstN
        simp only [skipIdx_zero, skipIdx_last]
        have hne : (⟨a.val, Nat.lt_succ_of_lt a.isLt⟩ : Fin (n + 1)) ≠ ⟨n, Nat.lt_succ_self n⟩ :=
          fin_ne (by simp; have := a.isLt; omega)
        simp only [hne, ↓reduceIte]
        unfold minor
        simp only [skipIdx_zero, skipIdx_last, Fin.succ]
      rw [hmin, ← CRing.mul_assoc, ← CRing.mul_assoc, hsign, neg_mul, CRing.one_mul, neg_mul]
    · intro j; unfold updateRow; simp
  have hdR0 :
      rsign (n + 1) *ᵣ det (minor (perturb M p q1 q2 r) ⟨n + 1, by omega⟩ ⟨0, by omega⟩) =
      rsign (n + 1) *ᵣ det (minor M ⟨n + 1, by omega⟩ ⟨0, by omega⟩) -ᵣ
      q1 *ᵣ det (minor (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n, by omega⟩ ⟨n, by omega⟩) := by
    let A := minor M ⟨n + 1, by omega⟩ ⟨0, by omega⟩
    let lastN : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let fstN : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    have hEq : minor (perturb M p q1 q2 r) ⟨n + 1, by omega⟩ ⟨0, by omega⟩ =
               updateRow A fstN (fun j => A fstN j +ᵣ (if j = lastN then q1 else zᵣ)) := by
      funext i j
      unfold updateRow A lastN fstN
      by_cases hi : i.val = 0
      · have hieq : i = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hi
        rw [hieq]
        simp only [↓reduceIte]
        unfold minor perturb
        simp only [skipIdx_zero, skipIdx_last, Fin.succ]
        have h2 : j.val + 1 ≠ 0 := by omega
        by_cases hj : j.val = n
        · have hjeq : j = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hj
          rw [hjeq]
          simp only [↓reduceIte, hn0, and_false, and_self]
        · have hjne : j ≠ ⟨n, Nat.lt_succ_self n⟩ := fin_ne hj
          have hj2 : j.val + 1 ≠ n + 1 := by omega
          simp only [hjne, hn0.symm, h2, hj2, and_false, ↓reduceIte]
      · have hine : i ≠ ⟨0, Nat.zero_lt_succ n⟩ := fin_ne hi
        simp only [hine, ↓reduceIte]
        unfold minor perturb
        simp only [skipIdx_zero, skipIdx_last, Fin.succ]
        have h2 : i.val ≠ n + 1 := by have := i.isLt; omega
        simp only [hi, h2, false_and, ↓reduceIte, add_zero]
    rw [hEq, det_updateRow_add, updateRow_self, CRing.left_distrib]
    unfold rsub
    apply congrArg (CRing.add _)
    rw [det_single_entry_row (r := fstN) (c := lastN) (s := q1)]
    · have hsign : rsign (R := R) (n + 1) *ᵣ rsign (R := R) (fstN.val + lastN.val) = -ᵣeᵣ := by
        rw [← rsign_add]; unfold rsign lastN fstN
        have hodd : (n + 1 + (0 + n)) % 2 ≠ 0 := by omega
        simp only [hodd, ↓reduceIte]
      have hmin :
          det (minor (updateRow A fstN (fun j => if j = lastN then q1 else zᵣ)) fstN lastN) =
          det (minor (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n, by omega⟩ ⟨n, by omega⟩) := by
        apply det_congr; intro a b
        unfold minor updateRow A lastN fstN
        simp only [skipIdx_zero, skipIdx_last]
        have hne : a.succ ≠ ⟨0, Nat.zero_lt_succ n⟩ := Fin.succ_ne_zero a
        simp only [hne, ↓reduceIte]
        unfold minor
        simp only [skipIdx_zero, skipIdx_last, Fin.succ]
      rw [hmin, ← CRing.mul_assoc, ← CRing.mul_assoc, hsign, neg_mul, CRing.one_mul, neg_mul]
    · intro j; unfold updateRow; simp
  have hd0 :
      det (perturb M p q1 q2 r) =
      (portalTuple M).d0 +ᵣ p *ᵣ (portalTuple M).dL +ᵣ r *ᵣ (portalTuple M).dR +ᵣ
      (p *ᵣ r -ᵣ q1 *ᵣ q2) *ᵣ (portalTuple M).dLR +ᵣ
      q1 *ᵣ (portalTuple M).d0R +ᵣ q2 *ᵣ (portalTuple M).dR0 := by
    let idx0 : Fin (n + 2) := ⟨0, by omega⟩
    let idxL : Fin (n + 2) := ⟨n + 1, by omega⟩
    let M1 : Mat (n + 2) R := perturb M p q1 zᵣ zᵣ
    have hstep2 : perturb M p q1 q2 r =
        updateRow M1 idxL (fun j => (M1 idxL j +ᵣ (if j = idx0 then q2 else zᵣ)) +ᵣ (if j = idxL then r else zᵣ)) := by
      funext i j
      unfold updateRow M1 idx0 idxL
      by_cases hi : i.val = n + 1
      · have hieq : i = ⟨n + 1, by omega⟩ := Fin.ext hi
        rw [hieq]
        simp only [↓reduceIte]
        unfold perturb
        by_cases hj0 : j.val = 0
        · have hj0e : j = ⟨0, by omega⟩ := Fin.ext hj0
          rw [hj0e]
          have hjne : (⟨0, by omega⟩ : Fin (n + 2)) ≠ ⟨n + 1, by omega⟩ := fin_ne (by simp)
          simp only [hjne, hn0, hn0.symm, false_and, and_self, ↓reduceIte, add_zero]
        · have hj0n : j ≠ ⟨0, by omega⟩ := fin_ne hj0
          by_cases hjL : j.val = n + 1
          · have hjLe : j = ⟨n + 1, by omega⟩ := Fin.ext hjL
            rw [hjLe]
            have hneL0 : (⟨n + 1, by omega⟩ : Fin (n + 2)) ≠ ⟨0, by omega⟩ := fin_ne (by simp)
            simp only [hneL0, hn0, false_and, and_false, and_self, ↓reduceIte, add_zero]
          · have hjLn : j ≠ ⟨n + 1, by omega⟩ := fin_ne hjL
            simp only [hj0n, hj0, hjLn, hjL, hn0, and_false, ↓reduceIte, add_zero]
      · have hine : i ≠ ⟨n + 1, by omega⟩ := fin_ne hi
        simp only [hine, ↓reduceIte]
        unfold perturb
        simp only [hi, false_and, ↓reduceIte]
    have hstep1 : M1 =
        updateRow M idx0 (fun j => (M idx0 j +ᵣ (if j = idx0 then p else zᵣ)) +ᵣ (if j = idxL then q1 else zᵣ)) := by
      funext i j
      unfold M1 updateRow idx0 idxL
      by_cases hi : i.val = 0
      · have hieq : i = ⟨0, by omega⟩ := Fin.ext hi
        rw [hieq]
        simp only [↓reduceIte]
        unfold perturb
        by_cases hj0 : j.val = 0
        · have hj0e : j = ⟨0, by omega⟩ := Fin.ext hj0
          rw [hj0e]
          have hjne : (⟨0, by omega⟩ : Fin (n + 2)) ≠ ⟨n + 1, by omega⟩ := fin_ne (by simp)
          simp only [hjne, and_self, ↓reduceIte, add_zero]
        · have hj0n : j ≠ ⟨0, by omega⟩ := fin_ne hj0
          by_cases hjL : j.val = n + 1
          · have hjLe : j = ⟨n + 1, by omega⟩ := Fin.ext hjL
            rw [hjLe]
            have hneL0 : (⟨n + 1, by omega⟩ : Fin (n + 2)) ≠ ⟨0, by omega⟩ := fin_ne (by simp)
            simp only [hneL0, hn0, and_false, and_self, ↓reduceIte, add_zero]
          · have hjLn : j ≠ ⟨n + 1, by omega⟩ := fin_ne hjL
            simp only [hj0n, hj0, hjLn, hjL, hn0.symm, and_false, ↓reduceIte, add_zero]
      · have hine : i ≠ ⟨0, by omega⟩ := fin_ne hi
        simp only [hine, ↓reduceIte]
        unfold perturb
        by_cases hiL : i.val = n + 1
        · by_cases hj0 : j.val = 0
          · simp only [hiL, hj0, hn0, hn0.symm, false_and, and_self, ↓reduceIte, add_zero]
          · by_cases hjL : j.val = n + 1
            · simp only [hiL, hjL, hn0, false_and, and_false, and_self, ↓reduceIte, add_zero]
            · simp only [hiL, hj0, hjL, hn0, and_false, ↓reduceIte, add_zero]
        · simp only [hi, hiL, false_and, ↓reduceIte, add_zero]
    rw [hstep2, det_updateRow_add, det_updateRow_add, updateRow_self]
    have hM1 : det M1 = (portalTuple M).d0 +ᵣ p *ᵣ (portalTuple M).dL +ᵣ q1 *ᵣ (portalTuple M).d0R := by
      rw [hstep1, det_updateRow_add, det_updateRow_add, updateRow_self]
      have ha : det (updateRow M idx0 (fun j => if j = idx0 then p else zᵣ)) = p *ᵣ (portalTuple M).dL := by
        rw [det_single_entry_row (r := idx0) (c := idx0) (s := p)]
        · have hsign : rsign (R := R) (idx0.val + idx0.val) = eᵣ := rfl
          rw [hsign, CRing.one_mul]
          apply congrArg (CRing.mul p)
          apply det_congr; intro a b
          unfold minor updateRow idx0
          rw [skipIdx_zero]
          have hne : a.succ ≠ ⟨0, by omega⟩ := Fin.succ_ne_zero a
          simp only [hne, ↓reduceIte]
        · intro j; unfold updateRow; simp
      have hb : det (updateRow M idx0 (fun j => if j = idxL then q1 else zᵣ)) = q1 *ᵣ (portalTuple M).d0R := by
        rw [det_single_entry_row (r := idx0) (c := idxL) (s := q1)]
        · have h0L : idx0.val + idxL.val = n + 1 := Nat.zero_add (n + 1)
          rw [h0L, CRing.mul_comm (rsign (n + 1)) q1, CRing.mul_assoc]
          unfold portalTuple
          apply congrArg (CRing.mul q1)
          apply congrArg (CRing.mul (rsign (n + 1)))
          apply det_congr; intro a b
          unfold minor updateRow idx0 idxL
          rw [skipIdx_zero]
          have hne : a.succ ≠ ⟨0, by omega⟩ := Fin.succ_ne_zero a
          simp only [hne, ↓reduceIte]
        · intro j; unfold updateRow; simp
      rw [ha, hb]; rfl
    have hQ2 : det (updateRow M1 idxL (fun j => if j = idx0 then q2 else zᵣ)) =
               q2 *ᵣ ((portalTuple M).dR0 -ᵣ q1 *ᵣ (portalTuple M).dLR) := by
      rw [det_single_entry_row (r := idxL) (c := idx0) (s := q2)]
      · have hminEq : minor (updateRow M1 idxL (fun j => if j = idx0 then q2 else zᵣ)) idxL idx0 =
                      minor M1 idxL idx0 := by
          funext a b; unfold minor updateRow idxL
          rw [skipIdx_last]
          have hne : (⟨a.val, Nat.lt_succ_of_lt a.isLt⟩ : Fin (n + 2)) ≠ ⟨n + 1, by omega⟩ :=
            fin_ne (by simp; have := a.isLt; omega)
          simp only [hne, ↓reduceIte]
        rw [hminEq]
        have hL0 : idxL.val + idx0.val = n + 1 := Nat.add_zero (n + 1)
        rw [hL0, CRing.mul_comm (rsign (n + 1)) q2, CRing.mul_assoc]
        apply congrArg (CRing.mul q2)
        have hM1_R0 :
            rsign (n + 1) *ᵣ det (minor M1 ⟨n + 1, by omega⟩ ⟨0, by omega⟩) =
            rsign (n + 1) *ᵣ det (minor M ⟨n + 1, by omega⟩ ⟨0, by omega⟩) -ᵣ
            q1 *ᵣ det (minor (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n, by omega⟩ ⟨n, by omega⟩) := by
          have hminM1 : minor M1 ⟨n + 1, by omega⟩ ⟨0, by omega⟩ =
                        minor (perturb M p q1 q2 r) ⟨n + 1, by omega⟩ ⟨0, by omega⟩ := by
            funext a b; unfold M1 minor perturb
            simp only [skipIdx_zero, skipIdx_last, Fin.succ]
            have h1 : a.val ≠ n + 1 := by have := a.isLt; omega
            simp only [h1, false_and, ↓reduceIte]
          rw [hminM1]
          exact hdR0
        exact hM1_R0
      · intro j; unfold updateRow; simp
    have hR : det (updateRow M1 idxL (fun j => if j = idxL then r else zᵣ)) =
              r *ᵣ ((portalTuple M).dR +ᵣ p *ᵣ (portalTuple M).dLR) := by
      rw [det_single_entry_row (r := idxL) (c := idxL) (s := r)]
      · have hsign : rsign (R := R) (idxL.val + idxL.val) = eᵣ := by
          unfold rsign idxL; have h : ((n + 1) + (n + 1)) % 2 = 0 := by omega
          simp only [h, ↓reduceIte]
        rw [hsign, CRing.one_mul]
        apply congrArg (CRing.mul r)
        have hminEq : minor (updateRow M1 idxL (fun j => if j = idxL then r else zᵣ)) idxL idxL =
                      minor M1 idxL idxL := by
          funext a b; unfold minor updateRow idxL; rw [skipIdx_last]
          have hne : (⟨a.val, Nat.lt_succ_of_lt a.isLt⟩ : Fin (n + 2)) ≠ ⟨n + 1, by omega⟩ :=
            fin_ne (by simp; have := a.isLt; omega)
          simp only [hne, ↓reduceIte]
        rw [hminEq]
        have hM1_R : minor M1 idxL idxL = minor (perturb M p q1 q2 r) idxL idxL := by
          funext a b; unfold M1 minor perturb idxL; simp only [skipIdx_last]
          have h1 : a.val ≠ n + 1 := by have := a.isLt; omega
          have h2 : b.val ≠ n + 1 := by have := b.isLt; omega
          simp only [h1, h2, false_and, and_false, ↓reduceIte]
        rw [hM1_R]
        exact hdR
      · intro j; unfold updateRow; simp
    rw [hM1, hQ2, hR]
    unfold rsub
    rw [CRing.left_distrib q2, mul_neg, CRing.left_distrib r, right_distrib (p *ᵣ r), neg_mul]
    rw [← CRing.mul_assoc q2 q1, CRing.mul_comm q2 q1, ← CRing.mul_assoc r p, CRing.mul_comm r p]
    let a0 := (portalTuple M).d0
    let aL := p *ᵣ (portalTuple M).dL
    let aR := r *ᵣ (portalTuple M).dR
    let a1 := (p *ᵣ r) *ᵣ (portalTuple M).dLR
    let a2 := -ᵣ((q1 *ᵣ q2) *ᵣ (portalTuple M).dLR)
    let b1 := q1 *ᵣ (portalTuple M).d0R
    let b2 := q2 *ᵣ (portalTuple M).dR0
    have lhs_norm :
        ((a0 +ᵣ aL +ᵣ b1) +ᵣ (b2 +ᵣ a2)) +ᵣ (aR +ᵣ a1) =
        a0 +ᵣ (aL +ᵣ (aR +ᵣ (a1 +ᵣ (a2 +ᵣ (b1 +ᵣ b2))))) := by
      simp only [CRing.add_assoc]
      apply congrArg (CRing.add a0)
      apply congrArg (CRing.add aL)
      -- Goal: b1 + (b2 + (a2 + (aR + a1))) = aR + (a1 + (a2 + (b1 + b2)))
      rw [add_left_comm a2 aR, add_left_comm b2 aR, add_left_comm b1 aR]
      apply congrArg (CRing.add aR)
      -- Goal: b1 + (b2 + (a2 + a1)) = a1 + (a2 + (b1 + b2))
      rw [CRing.add_comm a2 a1, add_left_comm b2 a1, add_left_comm b1 a1]
      apply congrArg (CRing.add a1)
      -- Goal: b1 + (b2 + a2) = a2 + (b1 + b2)
      rw [CRing.add_comm b2 a2, add_left_comm b1 a2]
    have rhs_norm :
        ((((a0 +ᵣ aL) +ᵣ aR) +ᵣ (a1 +ᵣ a2)) +ᵣ b1) +ᵣ b2 =
        a0 +ᵣ (aL +ᵣ (aR +ᵣ (a1 +ᵣ (a2 +ᵣ (b1 +ᵣ b2))))) := by
      simp only [CRing.add_assoc]
    change ((a0 +ᵣ aL +ᵣ b1) +ᵣ (b2 +ᵣ a2)) +ᵣ (aR +ᵣ a1) =
           ((((a0 +ᵣ aL) +ᵣ aR) +ᵣ (a1 +ᵣ a2)) +ᵣ b1) +ᵣ b2
    rw [lhs_norm, rhs_norm]
  unfold portalTuple stepPerturb
  simp only [PortalState.mk.injEq]
  exact ⟨hd0, hdL, hdR, hdLR, hd0R, hdR0⟩

/-! ### Theorem A2: Series Gluing Transfer Law (Exact, Division-Free, Any CRing R) -/

theorem portalTuple_glue {n1 n2 : Nat} (M1 : Mat (n1 + 2) R) (M2 : Mat (n2 + 2) R) (s : R) :
    portalTuple (glue M1 M2 s) = stepGlue (portalTuple M1) (portalTuple M2) s := by
  have hd0 : det (glue M1 M2 s) =
      (portalTuple M1).d0 *ᵣ (portalTuple M2).dL +ᵣ
      (portalTuple M1).dR *ᵣ (portalTuple M2).d0 +ᵣ
      s *ᵣ ((portalTuple M1).dR *ᵣ (portalTuple M2).dL) := by
    have hsz : (n1 + n2 + 1) + 2 = (n1 + 1) + 1 + (n2 + 1) := by omega
    rw [det_cast hsz (glue M1 M2 s)]
    have hEq := det_junction (a := n1 + 1) (b := n2 + 1) M1 M2 s
    have hmat :
        det (fun i j : Fin ((n1 + 1) + 1 + (n2 + 1)) =>
          glue M1 M2 s ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩) =
        det (fun i j : Fin ((n1 + 1) + 1 + (n2 + 1)) =>
          if hi1 : i.val < n1 + 1 then
            if hj1 : j.val ≤ n1 + 1 then M1 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ else zᵣ
          else if hi2 : i.val = n1 + 1 then
            if hj1 : j.val < n1 + 1 then M1 ⟨n1 + 1, by omega⟩ ⟨j.val, by omega⟩
            else if hj2 : j.val = n1 + 1 then
              M1 ⟨n1 + 1, by omega⟩ ⟨n1 + 1, by omega⟩ +ᵣ M2 ⟨0, by omega⟩ ⟨0, by omega⟩ +ᵣ s
            else M2 ⟨0, by omega⟩ ⟨j.val - (n1 + 1), by omega⟩
          else
            if hj1 : j.val < n1 + 1 then zᵣ else M2 ⟨i.val - (n1 + 1), by omega⟩ ⟨j.val - (n1 + 1), by omega⟩) := by
      apply det_congr; intro i j; rfl
    rw [hmat]
    exact hEq
  have hdL : det (minor (glue M1 M2 s) ⟨0, by omega⟩ ⟨0, by omega⟩) =
      (portalTuple M1).dL *ᵣ (portalTuple M2).dL +ᵣ
      (portalTuple M1).dLR *ᵣ (portalTuple M2).d0 +ᵣ
      s *ᵣ ((portalTuple M1).dLR *ᵣ (portalTuple M2).dL) := by
    have hsz : n1 + n2 + 1 + 1 = n1 + 1 + (n2 + 1) := by omega
    rw [det_cast hsz (minor (glue M1 M2 s) ⟨0, by omega⟩ ⟨0, by omega⟩)]
    have hEq := det_junction (a := n1) (b := n2 + 1) (minor M1 ⟨0, by omega⟩ ⟨0, by omega⟩) M2 s
    have hmat :
        det (fun i j : Fin (n1 + 1 + (n2 + 1)) =>
          minor (glue M1 M2 s) ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩) =
        det (fun i j : Fin (n1 + 1 + (n2 + 1)) =>
          if hi1 : i.val < n1 then
            if hj1 : j.val ≤ n1 then minor M1 ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ else zᵣ
          else if hi2 : i.val = n1 then
            if hj1 : j.val < n1 then minor M1 ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨n1, by omega⟩ ⟨j.val, by omega⟩
            else if hj2 : j.val = n1 then
              minor M1 ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨n1, by omega⟩ ⟨n1, by omega⟩ +ᵣ M2 ⟨0, by omega⟩ ⟨0, by omega⟩ +ᵣ s
            else M2 ⟨0, by omega⟩ ⟨j.val - n1, by omega⟩
          else
            if hj1 : j.val < n1 then zᵣ else M2 ⟨i.val - n1, by omega⟩ ⟨j.val - n1, by omega⟩) := by
      apply det_congr; intro i j
      unfold minor glue
      simp only [skipIdx_zero, Fin.succ]
      by_cases hi1 : i.val < n1
      · have hi1' : i.val + 1 < n1 + 1 := by omega
        simp only [hi1, hi1', ↓reduceDIte]
        by_cases hj1 : j.val ≤ n1
        · have hj1' : j.val + 1 ≤ n1 + 1 := by omega
          simp only [hj1, hj1', ↓reduceDIte]
        · have hj1' : ¬ (j.val + 1 ≤ n1 + 1) := by omega
          simp only [hj1, hj1', ↓reduceDIte]
      · by_cases hi2 : i.val = n1
        · have hn : ¬ (n1 < n1) := Nat.lt_irrefl n1
          have hni : ¬ (n1 + 1 < n1 + 1) := Nat.lt_irrefl (n1 + 1)
          simp only [hi2, hn, hni, ↓reduceDIte]
          by_cases hj1 : j.val < n1
          · have hj1' : j.val + 1 < n1 + 1 := by omega
            simp only [hj1, hj1', ↓reduceDIte]
          · by_cases hj2 : j.val = n1
            · simp only [hj2, hn, hni, ↓reduceDIte]
            · have hj1' : ¬ (j.val + 1 < n1 + 1) := by omega
              have hj2' : ¬ (j.val + 1 = n1 + 1) := by omega
              simp only [hj1, hj2, hj1', hj2', ↓reduceDIte]
              have ha2 : (⟨j.val + 1 - (n1 + 1), by omega⟩ : Fin (n2 + 2)) = ⟨j.val - n1, by omega⟩ :=
                Fin.ext (by simp)
              rw [ha2]
        · have hi1' : ¬ (i.val + 1 < n1 + 1) := by omega
          have hi2' : ¬ (i.val + 1 = n1 + 1) := by omega
          simp only [hi1, hi2, hi1', hi2', ↓reduceDIte]
          by_cases hj1 : j.val < n1
          · have hj1' : j.val + 1 < n1 + 1 := by omega
            simp only [hj1, hj1', ↓reduceDIte]
          · have hj1' : ¬ (j.val + 1 < n1 + 1) := by omega
            simp only [hj1, hj1', ↓reduceDIte]
            have ha1 : i.val + 1 - (n1 + 1) = i.val - n1 := by omega
            have ha2 : j.val + 1 - (n1 + 1) = j.val - n1 := by omega
            congr 1
            · exact Fin.ext ha1
            · exact Fin.ext ha2
    rw [hmat]
    exact hEq
  have hdR : det (minor (glue M1 M2 s) ⟨n1 + n2 + 2, by omega⟩ ⟨n1 + n2 + 2, by omega⟩) =
      (portalTuple M1).d0 *ᵣ (portalTuple M2).dLR +ᵣ
      (portalTuple M1).dR *ᵣ (portalTuple M2).dR +ᵣ
      s *ᵣ ((portalTuple M1).dR *ᵣ (portalTuple M2).dLR) := by
    have hsz : n1 + n2 + 1 + 1 = (n1 + 1) + 1 + n2 := by omega
    rw [det_cast hsz (minor (glue M1 M2 s) ⟨n1 + n2 + 2, by omega⟩ ⟨n1 + n2 + 2, by omega⟩)]
    have hEq := det_junction (a := n1 + 1) (b := n2) M1 (minor M2 ⟨n2 + 1, by omega⟩ ⟨n2 + 1, by omega⟩) s
    have hmat :
        det (fun i j : Fin ((n1 + 1) + 1 + n2) =>
          minor (glue M1 M2 s) ⟨n1 + n2 + 2, by omega⟩ ⟨n1 + n2 + 2, by omega⟩
            ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩) =
        det (fun i j : Fin ((n1 + 1) + 1 + n2) =>
          if hi1 : i.val < n1 + 1 then
            if hj1 : j.val ≤ n1 + 1 then M1 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ else zᵣ
          else if hi2 : i.val = n1 + 1 then
            if hj1 : j.val < n1 + 1 then M1 ⟨n1 + 1, by omega⟩ ⟨j.val, by omega⟩
            else if hj2 : j.val = n1 + 1 then
              M1 ⟨n1 + 1, by omega⟩ ⟨n1 + 1, by omega⟩ +ᵣ
              minor M2 ⟨n2 + 1, by omega⟩ ⟨n2 + 1, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩ +ᵣ s
            else minor M2 ⟨n2 + 1, by omega⟩ ⟨n2 + 1, by omega⟩ ⟨0, by omega⟩ ⟨j.val - (n1 + 1), by omega⟩
          else
            if hj1 : j.val < n1 + 1 then zᵣ
            else minor M2 ⟨n2 + 1, by omega⟩ ⟨n2 + 1, by omega⟩ ⟨i.val - (n1 + 1), by omega⟩ ⟨j.val - (n1 + 1), by omega⟩) := by
      apply det_congr; intro i j
      unfold minor glue
      simp only [skipIdx_last]
    rw [hmat, hEq]
    have hcomm :
        det (minor (minor M2 ⟨n2 + 1, by omega⟩ ⟨n2 + 1, by omega⟩) ⟨0, Nat.zero_lt_succ n2⟩ ⟨0, Nat.zero_lt_succ n2⟩) =
        (portalTuple M2).dLR := by
      apply det_congr; intro a b; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    rw [hcomm]
    rfl
  have hdLR :
      det (minor (minor (glue M1 M2 s) ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n1 + n2 + 1, by omega⟩ ⟨n1 + n2 + 1, by omega⟩) =
      (portalTuple M1).dL *ᵣ (portalTuple M2).dLR +ᵣ
      (portalTuple M1).dLR *ᵣ (portalTuple M2).dR +ᵣ
      s *ᵣ ((portalTuple M1).dLR *ᵣ (portalTuple M2).dLR) := by
    have hsz : n1 + n2 + 1 = n1 + 1 + n2 := by omega
    rw [det_cast hsz (minor (minor (glue M1 M2 s) ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n1 + n2 + 1, by omega⟩ ⟨n1 + n2 + 1, by omega⟩)]
    have hEq := det_junction (a := n1) (b := n2)
      (minor M1 ⟨0, by omega⟩ ⟨0, by omega⟩)
      (minor M2 ⟨n2 + 1, by omega⟩ ⟨n2 + 1, by omega⟩) s
    have hmat :
        det (fun i j : Fin (n1 + 1 + n2) =>
          minor (minor (glue M1 M2 s) ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨n1 + n2 + 1, by omega⟩ ⟨n1 + n2 + 1, by omega⟩
            ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩) =
        det (fun i j : Fin (n1 + 1 + n2) =>
          if hi1 : i.val < n1 then
            if hj1 : j.val ≤ n1 then minor M1 ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ else zᵣ
          else if hi2 : i.val = n1 then
            if hj1 : j.val < n1 then minor M1 ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨n1, by omega⟩ ⟨j.val, by omega⟩
            else if hj2 : j.val = n1 then
              minor M1 ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨n1, by omega⟩ ⟨n1, by omega⟩ +ᵣ
              minor M2 ⟨n2 + 1, by omega⟩ ⟨n2 + 1, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩ +ᵣ s
            else minor M2 ⟨n2 + 1, by omega⟩ ⟨n2 + 1, by omega⟩ ⟨0, by omega⟩ ⟨j.val - n1, by omega⟩
          else
            if hj1 : j.val < n1 then zᵣ
            else minor M2 ⟨n2 + 1, by omega⟩ ⟨n2 + 1, by omega⟩ ⟨i.val - n1, by omega⟩ ⟨j.val - n1, by omega⟩) := by
      apply det_congr; intro i j; unfold minor glue; simp only [skipIdx_last, skipIdx_zero, Fin.succ]
      by_cases hi1 : i.val < n1
      · have hi1' : i.val + 1 < n1 + 1 := by omega
        simp only [hi1, hi1', ↓reduceDIte]
        by_cases hj1 : j.val ≤ n1
        · have hj1' : j.val + 1 ≤ n1 + 1 := by omega
          simp only [hj1, hj1', ↓reduceDIte]
        · have hj1' : ¬ (j.val + 1 ≤ n1 + 1) := by omega
          simp only [hj1, hj1', ↓reduceDIte]
      · by_cases hi2 : i.val = n1
        · have hn : ¬ (n1 < n1) := Nat.lt_irrefl n1
          have hni : ¬ (n1 + 1 < n1 + 1) := Nat.lt_irrefl (n1 + 1)
          simp only [hi2, hn, hni, ↓reduceDIte]
          by_cases hj1 : j.val < n1
          · have hj1' : j.val + 1 < n1 + 1 := by omega
            simp only [hj1, hj1', ↓reduceDIte]
          · by_cases hj2 : j.val = n1
            · simp only [hj2, hn, hni, ↓reduceDIte]
            · have hj1' : ¬ (j.val + 1 < n1 + 1) := by omega
              have hj2' : ¬ (j.val + 1 = n1 + 1) := by omega
              simp only [hj1, hj2, hj1', hj2', ↓reduceDIte]
              have ha2 : (⟨j.val + 1 - (n1 + 1), by omega⟩ : Fin (n2 + 2)) = ⟨j.val - n1, by omega⟩ :=
                Fin.ext (by simp)
              rw [ha2]
        · have hi1' : ¬ (i.val + 1 < n1 + 1) := by omega
          have hi2' : ¬ (i.val + 1 = n1 + 1) := by omega
          simp only [hi1, hi2, hi1', hi2', ↓reduceDIte]
          by_cases hj1 : j.val < n1
          · have hj1' : j.val + 1 < n1 + 1 := by omega
            simp only [hj1, hj1', ↓reduceDIte]
          · have hj1' : ¬ (j.val + 1 < n1 + 1) := by omega
            simp only [hj1, hj1', ↓reduceDIte]
            have ha1 : i.val + 1 - (n1 + 1) = i.val - n1 := by omega
            have ha2 : j.val + 1 - (n1 + 1) = j.val - n1 := by omega
            congr 1
            · exact Fin.ext ha1
            · exact Fin.ext ha2
    rw [hmat, hEq]
    have hcomm :
        det (minor (minor M2 ⟨n2 + 1, by omega⟩ ⟨n2 + 1, by omega⟩) ⟨0, Nat.zero_lt_succ n2⟩ ⟨0, Nat.zero_lt_succ n2⟩) =
        (portalTuple M2).dLR := by
      apply det_congr; intro a b; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    rw [hcomm]
    rfl
  have hd0R :
      rsign ((n1 + n2 + 1) + 1) *ᵣ det (minor (glue M1 M2 s) ⟨0, by omega⟩ ⟨n1 + n2 + 2, by omega⟩) =
      (portalTuple M1).d0R *ᵣ (portalTuple M2).d0R := by
    have hsz : (n1 + n2 + 1) + 1 = (n1 + 1) + (n2 + 1) := by omega
    rw [det_cast hsz (minor (glue M1 M2 s) ⟨0, by omega⟩ ⟨n1 + n2 + 2, by omega⟩)]
    rw [det_blockUpper (a := n1 + 1) (b := n2 + 1)]
    · have hTL :
          (fun i j : Fin (n1 + 1) =>
            minor (glue M1 M2 s) ⟨0, by omega⟩ ⟨n1 + n2 + 2, by omega⟩
              ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩) =
          minor M1 ⟨0, by omega⟩ ⟨n1 + 1, by omega⟩ := by
        funext i j; unfold minor glue; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
        by_cases hi : i.val + 1 < n1 + 1
        · have hjle : j.val ≤ n1 + 1 := by have := j.isLt; omega
          simp only [hi, hjle, ↓reduceDIte]
        · have hieq : i.val + 1 = n1 + 1 := by have := i.isLt; omega
          have hjlt : j.val < n1 + 1 := j.isLt
          have hni : ¬ (n1 + 1 < n1 + 1) := Nat.lt_irrefl (n1 + 1)
          simp only [hieq, hni, hjlt, ↓reduceDIte]
      have hBR :
          (fun i j : Fin (n2 + 1) =>
            minor (glue M1 M2 s) ⟨0, by omega⟩ ⟨n1 + n2 + 2, by omega⟩
              ⟨n1 + 1 + i.val, by have := i.isLt; omega⟩ ⟨n1 + 1 + j.val, by have := j.isLt; omega⟩) =
          minor M2 ⟨0, by omega⟩ ⟨n2 + 1, by omega⟩ := by
        funext i j; unfold minor glue; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
        have h1 : ¬ (n1 + 1 + i.val + 1 < n1 + 1) := by omega
        have h2 : ¬ (n1 + 1 + i.val + 1 = n1 + 1) := by omega
        have h3 : ¬ (n1 + 1 + j.val < n1 + 1) := by omega
        simp only [h1, h2, h3, ↓reduceDIte]
        have ha1 : n1 + 1 + i.val + 1 - (n1 + 1) = i.val + 1 := by omega
        have ha2 : n1 + 1 + j.val - (n1 + 1) = j.val := by omega
        congr 1
        · exact Fin.ext ha1
        · exact Fin.ext ha2
      rw [hTL, hBR]
      have hsign : rsign (R := R) ((n1 + n2 + 1) + 1) = rsign (R := R) (n1 + 1) *ᵣ rsign (R := R) (n2 + 1) := by
        rw [← rsign_add]; congr 1
      rw [hsign]
      simp only [portalTuple, CRing.mul_assoc]
      rw [mul_left_comm (rsign (n2 + 1)) (det (minor M1 ⟨0, by omega⟩ ⟨n1 + 1, by omega⟩))]
    · intro i j; unfold minor glue; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
      have h1 : ¬ (n1 + 1 + i.val + 1 < n1 + 1) := by omega
      have h2 : ¬ (n1 + 1 + i.val + 1 = n1 + 1) := by omega
      have h3 : j.val < n1 + 1 := j.isLt
      simp only [h1, h2, h3, ↓reduceDIte]
  have hdR0 :
      rsign ((n1 + n2 + 1) + 1) *ᵣ det (minor (glue M1 M2 s) ⟨n1 + n2 + 2, by omega⟩ ⟨0, by omega⟩) =
      (portalTuple M1).dR0 *ᵣ (portalTuple M2).dR0 := by
    have hsz : (n1 + n2 + 1) + 1 = (n1 + 1) + (n2 + 1) := by omega
    rw [det_cast hsz (minor (glue M1 M2 s) ⟨n1 + n2 + 2, by omega⟩ ⟨0, by omega⟩)]
    rw [det_blockLower (a := n1 + 1) (b := n2 + 1)]
    · have hTL :
          (fun i j : Fin (n1 + 1) =>
            minor (glue M1 M2 s) ⟨n1 + n2 + 2, by omega⟩ ⟨0, by omega⟩
              ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩) =
          minor M1 ⟨n1 + 1, by omega⟩ ⟨0, by omega⟩ := by
        funext i j; unfold minor glue; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
        have hi : i.val < n1 + 1 := i.isLt
        have hjle : j.val + 1 ≤ n1 + 1 := by have := j.isLt; omega
        simp only [hi, hjle, ↓reduceDIte]
      have hBR :
          (fun i j : Fin (n2 + 1) =>
            minor (glue M1 M2 s) ⟨n1 + n2 + 2, by omega⟩ ⟨0, by omega⟩
              ⟨n1 + 1 + i.val, by have := i.isLt; omega⟩ ⟨n1 + 1 + j.val, by have := j.isLt; omega⟩) =
          minor M2 ⟨n2 + 1, by omega⟩ ⟨0, by omega⟩ := by
        funext i j; unfold minor glue; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
        by_cases hi0 : i.val = 0
        · have hni : ¬ (n1 + 1 < n1 + 1) := Nat.lt_irrefl (n1 + 1)
          have h2 : n1 + 1 + i.val = n1 + 1 := by omega
          have h3 : ¬ (n1 + 1 + j.val + 1 < n1 + 1) := by omega
          have h4 : ¬ (n1 + 1 + j.val + 1 = n1 + 1) := by omega
          simp only [h2, hni, h3, h4, ↓reduceDIte]
          have ha2 : n1 + 1 + j.val + 1 - (n1 + 1) = j.val + 1 := by omega
          have hr : (⟨0, by omega⟩ : Fin (n2 + 2)) = ⟨i.val, by have := i.isLt; omega⟩ := Fin.ext hi0.symm
          have hc : (⟨n1 + 1 + j.val + 1 - (n1 + 1), by omega⟩ : Fin (n2 + 2)) =
                    ⟨j.val + 1, by have := j.isLt; omega⟩ := Fin.ext ha2
          rw [hr, hc]
        · have h1 : ¬ (n1 + 1 + i.val < n1 + 1) := by omega
          have h2 : ¬ (n1 + 1 + i.val = n1 + 1) := by omega
          have h3 : ¬ (n1 + 1 + j.val + 1 < n1 + 1) := by omega
          simp only [h1, h2, h3, ↓reduceDIte]
          have ha1 : n1 + 1 + i.val - (n1 + 1) = i.val := by omega
          have ha2 : n1 + 1 + j.val + 1 - (n1 + 1) = j.val + 1 := by omega
          congr 1
          · exact Fin.ext ha1
          · exact Fin.ext ha2
      rw [hTL, hBR]
      have hsign : rsign (R := R) ((n1 + n2 + 1) + 1) = rsign (R := R) (n1 + 1) *ᵣ rsign (R := R) (n2 + 1) := by
        rw [← rsign_add]; congr 1
      rw [hsign]
      simp only [portalTuple, CRing.mul_assoc]
      rw [mul_left_comm (rsign (n2 + 1)) (det (minor M1 ⟨n1 + 1, by omega⟩ ⟨0, by omega⟩))]
    · intro i j; unfold minor glue; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
      have hi : i.val < n1 + 1 := i.isLt
      have hnot : ¬ (n1 + 1 + j.val + 1 ≤ n1 + 1) := by omega
      simp only [hi, hnot, ↓reduceDIte]
  unfold portalTuple stepGlue
  simp only [PortalState.mk.injEq]
  exact ⟨hd0, hdL, hdR, hdLR, hd0R, hdR0⟩

/-- Generic Infinite Lifting Theorem (Theorem A3):
Any finite algebraic invariant `Inv : Nat → PortalState R → Prop` preserved by a symmetric
2-portal step (`perturb` + `glue`) lifts automatically to ALL `k : Nat`! -/
theorem portal_tower_induction
    (dims : Nat → Nat)
    (M : ∀ k, Mat (dims k + 2) R)
    (p q1 q2 r s : Nat → R)
    (hstep : ∀ k, portalTuple (M (k + 1)) =
      stepGlue (stepPerturb (portalTuple (M k)) (p k) (q1 k) (q2 k) (r k))
               (stepPerturb (portalTuple (M k)) (p k) (q1 k) (q2 k) (r k)) (s k))
    (Inv : Nat → PortalState R → Prop)
    (hbase : Inv 0 (portalTuple (M 0)))
    (hpres : ∀ k st, Inv k st →
      Inv (k + 1) (stepGlue (stepPerturb st (p k) (q1 k) (q2 k) (r k))
                            (stepPerturb st (p k) (q1 k) (q2 k) (r k)) (s k))) :
    ∀ k, Inv k (portalTuple (M k)) := by
  intro k
  induction k with
  | zero => exact hbase
  | succ k ih =>
    rw [hstep k]
    exact hpres k (portalTuple (M k)) ih

end PortalTransfer
section ParityBlockInv
variable {R : Type} [CRing R]

/-- Prove `U_m * U_m^{-1} = I_m` for ALL `m : Nat` over any `CRing R`! -/
theorem bidiagU_mul_inv (m : Nat) : matMul (bidiagU (R := R) m) (bidiagUInv (R := R) m) = matId m := by
  funext r c
  unfold matMul matId bidiagU bidiagUInv
  by_cases hr0 : r.val = 0
  · -- Row 0 of U_m only has 1 at column 0!
    rw [sumFin_single ⟨0, by omega⟩]
    · simp only [hr0, true_or, ↓reduceIte, CRing.one_mul]
      by_cases hc0 : c.val = 0
      · have heq : r = c := Fin.ext (by omega)
        simp [heq, hc0, rsign_zero]
      · have hne : r ≠ c := fun h => hc0 (by rw [← h]; exact hr0)
        have hnotle : ¬ (c.val ≤ 0) := by omega
        simp [hne, hnotle]
    · intro k hk
      have hkne : k.val ≠ 0 := fun h => hk (Fin.ext h)
      have h1 : ¬ (k.val = r.val ∨ k.val + 1 = r.val) := by omega
      simp [h1, zero_mul]
  · -- Row r > 0 of U_m only has 1 at k = r - 1 and k = r!
    let k1 : Fin m := ⟨r.val - 1, by omega⟩
    let k2 : Fin m := r
    have hsplit :
        (fun k : Fin m =>
          (if k.val = r.val ∨ k.val + 1 = r.val then (eᵣ : R) else zᵣ) *ᵣ
          (if c.val ≤ k.val then rsign (k.val - c.val) else zᵣ)) =
        (fun k : Fin m =>
          (if k = k1 then (if c.val ≤ r.val - 1 then rsign (R := R) (r.val - 1 - c.val) else zᵣ) else zᵣ) +ᵣ
          (if k = k2 then (if c.val ≤ r.val then rsign (R := R) (r.val - c.val) else zᵣ) else zᵣ)) := by
      funext k
      by_cases hk1 : k = k1
      · rw [hk1]
        have hne : k1 ≠ k2 := fin_ne (by simp [k1, k2]; omega)
        have hor : k1.val = r.val ∨ k1.val + 1 = r.val := Or.inr (by simp [k1]; omega)
        simp only [hor, ↓reduceIte, hne, CRing.one_mul, add_zero]
        rfl
      · by_cases hk2 : k = k2
        · rw [hk2]
          have hne21 : k2 ≠ k1 := fin_ne (by simp [k1, k2]; omega)
          have hor : k2.val = r.val ∨ k2.val + 1 = r.val := Or.inl rfl
          simp only [hor, ↓reduceIte, hne21, CRing.one_mul, CRing.zero_add]
          rfl
        · have hnor : ¬ (k.val = r.val ∨ k.val + 1 = r.val) := by
            intro h; rcases h with h | h
            · exact hk2 (Fin.ext h)
            · exact hk1 (Fin.ext (by simp [k1]; omega))
          simp only [hnor, hk1, hk2, ↓reduceIte, zero_mul, add_zero]
    rw [hsplit, sumFin_add, sumFin_single k1, sumFin_single k2]
    · simp only [↓reduceIte]
      by_cases hcr : c.val < r.val
      · have hle1 : c.val ≤ r.val - 1 := by omega
        have hle2 : c.val ≤ r.val := by omega
        have hne : r ≠ c := fin_ne (by omega)
        have hsucc : r.val - c.val = (r.val - 1 - c.val) + 1 := by omega
        simp only [hle1, hle2, hne, ↓reduceIte, hsucc, rsign_succ, add_right_neg]
      · by_cases hceq : c.val = r.val
        · have hnotle1 : ¬ (c.val ≤ r.val - 1) := by omega
          have hle2 : c.val ≤ r.val := by omega
          have heq : r = c := Fin.ext hceq.symm
          have hsub : r.val - c.val = 0 := by omega
          simp only [hnotle1, hle2, ↓reduceIte, hsub, rsign_zero, CRing.zero_add]
          simp only [heq, ↓reduceIte]
        · have hnotle1 : ¬ (c.val ≤ r.val - 1) := by omega
          have hnotle2 : ¬ (c.val ≤ r.val) := by omega
          have hne : r ≠ c := fin_ne (by omega)
          simp only [hnotle1, hnotle2, hne, ↓reduceIte, add_zero]
    · intro k hk; simp [hk]
    · intro k hk; simp [hk]

/-- Prove `U_m^{-1} * U_m = I_m` for ALL `m : Nat` over any `CRing R`! -/
theorem bidiagUInv_mul (m : Nat) : matMul (bidiagUInv (R := R) m) (bidiagU (R := R) m) = matId m := by
  funext r c
  unfold matMul matId bidiagU bidiagUInv
  by_cases hclast : c.val + 1 < m
  · let k1 : Fin m := c
    let k2 : Fin m := ⟨c.val + 1, hclast⟩
    have hsplit :
        (fun k : Fin m =>
          (if k.val ≤ r.val then rsign (R := R) (r.val - k.val) else zᵣ) *ᵣ
          (if c.val = k.val ∨ c.val + 1 = k.val then (eᵣ : R) else zᵣ)) =
        (fun k : Fin m =>
          (if k = k1 then (if c.val ≤ r.val then rsign (R := R) (r.val - c.val) else zᵣ) else zᵣ) +ᵣ
          (if k = k2 then (if c.val + 1 ≤ r.val then rsign (R := R) (r.val - (c.val + 1)) else zᵣ) else zᵣ)) := by
      funext k
      by_cases hk1 : k = k1
      · rw [hk1]
        have hne : k1 ≠ k2 := fin_ne (by simp [k1, k2])
        have hor : c.val = k1.val ∨ c.val + 1 = k1.val := Or.inl rfl
        simp only [hor, ↓reduceIte, hne, mul_one, add_zero]
        rfl
      · by_cases hk2 : k = k2
        · rw [hk2]
          have hne21 : k2 ≠ k1 := fin_ne (by simp [k1, k2])
          have hor : c.val = k2.val ∨ c.val + 1 = k2.val := Or.inr rfl
          simp only [hor, ↓reduceIte, hne21, mul_one, CRing.zero_add]
          rfl
        · have hnor : ¬ (c.val = k.val ∨ c.val + 1 = k.val) := by
            intro h; rcases h with h | h
            · exact hk1 (Fin.ext h.symm)
            · exact hk2 (Fin.ext h.symm)
          simp only [hnor, hk1, hk2, ↓reduceIte, mul_zero, add_zero]
    rw [hsplit, sumFin_add, sumFin_single k1, sumFin_single k2]
    · simp only [↓reduceIte]
      by_cases hcr : c.val < r.val
      · have hle1 : c.val ≤ r.val := by omega
        have hle2 : c.val + 1 ≤ r.val := by omega
        have hne : r ≠ c := fin_ne (by omega)
        have hsucc : r.val - c.val = (r.val - (c.val + 1)) + 1 := by omega
        simp only [hle1, hle2, hne, ↓reduceIte, hsucc, rsign_succ, CRing.add_left_neg]
      · by_cases hceq : c.val = r.val
        · have hle1 : c.val ≤ r.val := by omega
          have hnotle2 : ¬ (c.val + 1 ≤ r.val) := by omega
          have heq : r = c := Fin.ext hceq.symm
          have hsub : r.val - c.val = 0 := by omega
          simp only [hle1, hnotle2, ↓reduceIte, hsub, rsign_zero, add_zero]
          simp only [heq, ↓reduceIte]
        · have hnotle1 : ¬ (c.val ≤ r.val) := by omega
          have hnotle2 : ¬ (c.val + 1 ≤ r.val) := by omega
          have hne : r ≠ c := fin_ne (by omega)
          simp only [hnotle1, hnotle2, hne, ↓reduceIte, add_zero]
    · intro k hk; simp [hk]
    · intro k hk; simp [hk]
  · rw [sumFin_single c]
    · simp only [true_or, ↓reduceIte, mul_one]
      by_cases hceq : r = c
      · subst hceq; simp [Nat.sub_self, rsign_zero]
      · have hnotle : ¬ (c.val ≤ r.val) := by
          have := r.isLt; have := c.isLt
          intro hle; exact hceq (Fin.ext (by omega))
        simp [hceq, hnotle]
    · intro k hk
      have hnor : ¬ (c.val = k.val ∨ c.val + 1 = k.val) := by
        have := k.isLt; intro h; rcases h with h | h
        · exact hk (Fin.ext h.symm)
        · omega
      simp [hnor, mul_zero]

/-- Split a sum over `Fin (2 * m)` into its even-index (`2k`) and odd-index (`2k + 1`) halves! -/
theorem sumFin_even_odd {m : Nat} (f : Fin (2 * m) → R) :
    sumFin f =
      sumFin (fun k : Fin m => f ⟨2 * k.val, by omega⟩) +ᵣ
      sumFin (fun k : Fin m => f ⟨2 * k.val + 1, by omega⟩) := by
  induction m with
  | zero =>
    simp [sumFin_zero, CRing.zero_add]
  | succ t ih =>
    have heq : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
    rw [sumFin_cast heq, sumFin_succ_last, sumFin_succ_last]
    have h1 := ih (fun i : Fin (2 * t) => f ⟨i.val, by omega⟩)
    rw [h1]
    rw [sumFin_succ_last (fun k : Fin (t + 1) => f ⟨2 * k.val, by omega⟩)]
    rw [sumFin_succ_last (fun k : Fin (t + 1) => f ⟨2 * k.val + 1, by omega⟩)]
    let sE := sumFin (fun k : Fin t => f ⟨2 * k.val, by omega⟩)
    let sO := sumFin (fun k : Fin t => f ⟨2 * k.val + 1, by omega⟩)
    let fE := f ⟨2 * t, by omega⟩
    let fO := f ⟨2 * t + 1, by omega⟩
    change ((sE +ᵣ sO) +ᵣ fE) +ᵣ fO = (sE +ᵣ fE) +ᵣ (sO +ᵣ fO)
    rw [CRing.add_assoc sE sO fE, CRing.add_comm sO fE, ← CRing.add_assoc sE fE sO, CRing.add_assoc]

/-- Theorem B1 (Even/Odd Bit-Parity Exact Inversion Engine):
For EVERY `m : Nat` and EVERY `m × m` matrix `M` over ANY commutative ring `R`,
`interleave M * interleaveInv M = I_{2m}`! -/
theorem interleave_mul_inv {m : Nat} (M : Mat m R) :
    matMul (interleave M) (interleaveInv M) = matId (2 * m) := by
  funext i j
  unfold matMul matId
  rw [sumFin_even_odd]
  let ia : Fin m := ⟨i.val / 2, by omega⟩
  let jb : Fin m := ⟨j.val / 2, by omega⟩
  have hUinv : ∀ r c : Fin m, sumFin (fun k : Fin m => bidiagU (R := R) m r k *ᵣ bidiagUInv (R := R) m k c) =
      if r = c then eᵣ else zᵣ := by
    intro r c
    have h := congrFun (congrFun (bidiagU_mul_inv (R := R) m) r) c
    exact h
  have hInvU : ∀ r c : Fin m, sumFin (fun k : Fin m => bidiagUInv (R := R) m r k *ᵣ bidiagU (R := R) m k c) =
      if r = c then eᵣ else zᵣ := by
    intro r c
    have h := congrFun (congrFun (bidiagUInv_mul (R := R) m) r) c
    exact h
  by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0
  · -- Case (even, even): 0 + U * U^{-1} = I!
    have hLeft : sumFin (fun k : Fin m => interleave M i ⟨2 * k.val, by omega⟩ *ᵣ
                                          interleaveInv M ⟨2 * k.val, by omega⟩ j) = zᵣ := by
      rw [sumFin_congr (g := fun _ => zᵣ)]
      · exact sumFin_const_zero
      · intro k; unfold interleave; simp [hi, zero_mul]
    have hRight : sumFin (fun k : Fin m => interleave M i ⟨2 * k.val + 1, by omega⟩ *ᵣ
                                           interleaveInv M ⟨2 * k.val + 1, by omega⟩ j) =
                  if ia = jb then eᵣ else zᵣ := by
      have hc : (fun k : Fin m => interleave M i ⟨2 * k.val + 1, by omega⟩ *ᵣ
                                  interleaveInv M ⟨2 * k.val + 1, by omega⟩ j) =
                (fun k : Fin m => bidiagU m ia k *ᵣ bidiagUInv m k jb) := by
        funext k; unfold interleave interleaveInv
        have hodd : (2 * k.val + 1) % 2 ≠ 0 := by omega
        have hdiv : (2 * k.val + 1) / 2 = k.val := by omega
        simp only [hi, hj, hodd, ↓reduceIte]
        congr 1 <;> (congr 1; exact Fin.ext hdiv)
      rw [hc, hUinv ia jb]
    rw [hLeft, hRight, CRing.zero_add]
    by_cases hij : ia = jb
    · have heq : i = j := Fin.ext (by have := congrArg Fin.val hij; simp [ia, jb] at this; omega)
      simp [hij, heq]
    · have hne : i ≠ j := fun h => hij (Fin.ext (by simp [ia, jb, h]))
      simp [hij, hne]
  · -- Case (even, odd): 0 + 0 = 0!
    have hLeft : sumFin (fun k : Fin m => interleave M i ⟨2 * k.val, by omega⟩ *ᵣ
                                          interleaveInv M ⟨2 * k.val, by omega⟩ j) = zᵣ := by
      rw [sumFin_congr (g := fun _ => zᵣ)]
      · exact sumFin_const_zero
      · intro k; unfold interleave; simp [hi, zero_mul]
    have hRight : sumFin (fun k : Fin m => interleave M i ⟨2 * k.val + 1, by omega⟩ *ᵣ
                                           interleaveInv M ⟨2 * k.val + 1, by omega⟩ j) = zᵣ := by
      rw [sumFin_congr (g := fun _ => zᵣ)]
      · exact sumFin_const_zero
      · intro k; unfold interleaveInv
        simp [hj, mul_zero]
    have hne : i ≠ j := fun h => hj (by rw [← h]; exact hi)
    rw [hLeft, hRight, add_zero]
    simp only [hne, ↓reduceIte]
  · -- Case (odd, even): U^T * (-U^{-T} M U^{-1}) + M * U^{-1} = 0!
    have hLeft : sumFin (fun k : Fin m => interleave M i ⟨2 * k.val, by omega⟩ *ᵣ
                                          interleaveInv M ⟨2 * k.val, by omega⟩ j) =
                 -ᵣ(matMul M (bidiagUInv m) ia jb) := by
      have hc : (fun k : Fin m => interleave M i ⟨2 * k.val, by omega⟩ *ᵣ
                                  interleaveInv M ⟨2 * k.val, by omega⟩ j) =
                (fun k : Fin m => -ᵣ(bidiagU m k ia *ᵣ
                  sumFin (fun r : Fin m => bidiagUInv m r k *ᵣ matMul M (bidiagUInv m) r jb))) := by
        funext k; unfold interleave interleaveInv
        have hev : (2 * k.val) % 2 = 0 := by omega
        have hdiv : (2 * k.val) / 2 = k.val := by omega
        simp only [hi, hj, hev, ↓reduceIte, mul_neg]
        congr 1; unfold matMul
        congr 1
        · congr 1; exact Fin.ext hdiv
        · apply sumFin_congr; intro r; congr 1; congr 1; exact Fin.ext hdiv
      rw [hc, sumFin_neg]
      apply congrArg CRing.neg
      have hswap :
          sumFin (fun k : Fin m => bidiagU m k ia *ᵣ
            sumFin (fun r : Fin m => bidiagUInv m r k *ᵣ matMul M (bidiagUInv m) r jb)) =
          sumFin (fun r : Fin m =>
            sumFin (fun k : Fin m => bidiagUInv m r k *ᵣ bidiagU m k ia) *ᵣ matMul M (bidiagUInv m) r jb) := by
        calc sumFin (fun k : Fin m => bidiagU m k ia *ᵣ
                sumFin (fun r : Fin m => bidiagUInv m r k *ᵣ matMul M (bidiagUInv m) r jb))
            = sumFin (fun k : Fin m => sumFin (fun r : Fin m =>
                bidiagU m k ia *ᵣ (bidiagUInv m r k *ᵣ matMul M (bidiagUInv m) r jb))) := by
              apply sumFin_congr; intro k; rw [← sumFin_mul_left]
          _ = sumFin (fun r : Fin m => sumFin (fun k : Fin m =>
                bidiagU m k ia *ᵣ (bidiagUInv m r k *ᵣ matMul M (bidiagUInv m) r jb))) := sumFin_comm _
          _ = sumFin (fun r : Fin m =>
                sumFin (fun k : Fin m => bidiagUInv m r k *ᵣ bidiagU m k ia) *ᵣ matMul M (bidiagUInv m) r jb) := by
              apply sumFin_congr; intro r
              rw [← sumFin_mul_right]
              apply sumFin_congr; intro k
              rw [← CRing.mul_assoc, CRing.mul_comm (bidiagU m k ia)]
      rw [hswap]
      rw [sumFin_single ia]
      · rw [hInvU ia ia]; simp [CRing.one_mul]
      · intro r hr; rw [hInvU r ia]; simp [hr, zero_mul]
    have hRight : sumFin (fun k : Fin m => interleave M i ⟨2 * k.val + 1, by omega⟩ *ᵣ
                                           interleaveInv M ⟨2 * k.val + 1, by omega⟩ j) =
                  matMul M (bidiagUInv m) ia jb := by
      unfold matMul
      apply sumFin_congr; intro k
      unfold interleave interleaveInv
      have hodd : (2 * k.val + 1) % 2 ≠ 0 := by omega
      have hdiv : (2 * k.val + 1) / 2 = k.val := by omega
      simp only [hi, hj, hodd, ↓reduceIte]
      congr 1 <;> (congr 1; exact Fin.ext hdiv)
    have hne : i ≠ j := fun h => hi (by rw [h]; exact hj)
    rw [hLeft, hRight, CRing.add_left_neg]
    simp only [hne, ↓reduceIte]
  · -- Case (odd, odd): U^T * U^{-T} + 0 = I!
    have hLeft : sumFin (fun k : Fin m => interleave M i ⟨2 * k.val, by omega⟩ *ᵣ
                                          interleaveInv M ⟨2 * k.val, by omega⟩ j) =
                 if ia = jb then eᵣ else zᵣ := by
      have hc : (fun k : Fin m => interleave M i ⟨2 * k.val, by omega⟩ *ᵣ
                                  interleaveInv M ⟨2 * k.val, by omega⟩ j) =
                (fun k : Fin m => bidiagUInv m jb k *ᵣ bidiagU m k ia) := by
        funext k; unfold interleave interleaveInv
        have hev : (2 * k.val) % 2 = 0 := by omega
        have hdiv : (2 * k.val) / 2 = k.val := by omega
        simp only [hi, hj, hev, ↓reduceIte]
        rw [CRing.mul_comm]
        congr 1 <;> (congr 1; exact Fin.ext hdiv)
      rw [hc, hInvU jb ia]
      by_cases hij : ia = jb
      · rw [hij]
      · have hji : jb ≠ ia := fun h => hij h.symm
        simp only [hij, hji, ↓reduceIte]
    have hRight : sumFin (fun k : Fin m => interleave M i ⟨2 * k.val + 1, by omega⟩ *ᵣ
                                           interleaveInv M ⟨2 * k.val + 1, by omega⟩ j) = zᵣ := by
      rw [sumFin_congr (g := fun _ => zᵣ)]
      · exact sumFin_const_zero
      · intro k; unfold interleaveInv
        simp [hj, mul_zero]
    rw [hLeft, hRight, add_zero]
    by_cases hij : ia = jb
    · have heq : i = j := Fin.ext (by have := congrArg Fin.val hij; simp [ia, jb] at this; omega)
      simp [hij, heq]
    · have hne : i ≠ j := fun h => hij (Fin.ext (by simp [ia, jb, h]))
      simp [hij, hne]

/-- Bordered Dyadic/Scaled Inverse Lemma (Theorem B2):
If `A` is a symmetric bordered matrix `[[0, u^T], [u, B]]` of size `n + 1`,
`B * Binv = I_n`, `w = Binv * u`, and `u^T * w = σ`, then
`J = [[-1, w^T], [w, σ * Binv - w * w^T]]` satisfies `A * J = σ * I_{n+1}`! -/
theorem bordered_schur_inv {n : Nat}
    (B Binv : Mat n R) (u : Fin n → R) (σ : R)
    (hBinv : matMul B Binv = matId n)
    (_hBsym : ∀ i j, B i j = B j i)
    (hBinvSym : ∀ i j, Binv i j = Binv j i)
    (hσ : sumFin (fun k : Fin n => u k *ᵣ sumFin (fun r : Fin n => Binv k r *ᵣ u r)) = σ) :
    let w : Fin n → R := fun i => sumFin (fun r : Fin n => Binv i r *ᵣ u r)
    let A : Mat (n + 1) R := fun i j =>
      if hi : i.val = 0 then
        if hj : j.val = 0 then zᵣ else u ⟨j.val - 1, by omega⟩
      else
        if hj : j.val = 0 then u ⟨i.val - 1, by omega⟩
        else B ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
    let J : Mat (n + 1) R := fun i j =>
      if hi : i.val = 0 then
        if hj : j.val = 0 then -ᵣeᵣ else w ⟨j.val - 1, by omega⟩
      else
        if hj : j.val = 0 then w ⟨i.val - 1, by omega⟩
        else σ *ᵣ Binv ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ -ᵣ
             w ⟨i.val - 1, by omega⟩ *ᵣ w ⟨j.val - 1, by omega⟩
    matMul A J = fun i j => if i = j then σ else zᵣ := by
  intro w A J
  -- First prove B * w = u!
  have hBw : ∀ i : Fin n, sumFin (fun k : Fin n => B i k *ᵣ w k) = u i := by
    intro i
    calc sumFin (fun k : Fin n => B i k *ᵣ sumFin (fun r : Fin n => Binv k r *ᵣ u r))
        = sumFin (fun k : Fin n => sumFin (fun r : Fin n => B i k *ᵣ (Binv k r *ᵣ u r))) := by
          apply sumFin_congr; intro k; rw [← sumFin_mul_left]
      _ = sumFin (fun r : Fin n => sumFin (fun k : Fin n => B i k *ᵣ (Binv k r *ᵣ u r))) := sumFin_comm _
      _ = sumFin (fun r : Fin n => matMul B Binv i r *ᵣ u r) := by
          apply sumFin_congr; intro r; unfold matMul; rw [← sumFin_mul_right]
          apply sumFin_congr; intro k; rw [CRing.mul_assoc]
      _ = sumFin (fun r : Fin n => (if i = r then eᵣ else zᵣ) *ᵣ u r) := by
          apply sumFin_congr; intro r; rw [hBinv]; rfl
      _ = u i := by
          rw [sumFin_single i]
          · simp [CRing.one_mul]
          · intro r hr; have hne : i ≠ r := fun h => hr h.symm; simp [hne, zero_mul]
  -- Also prove sum_k u k * Binv k j = w j (by symmetry of Binv)!
  have huBinv : ∀ j : Fin n, sumFin (fun k : Fin n => u k *ᵣ Binv k j) = w j := by
    intro j; unfold w; apply sumFin_congr; intro k; rw [CRing.mul_comm, hBinvSym]
  funext i j
  unfold matMul
  rw [sumFin_succ]
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · -- (0, 0): 0 * (-1) + u^T * w = σ!
    have heq : i = j := Fin.ext (by omega)
    simp only [A, J, hj, ↓reduceDIte, heq, ↓reduceIte, zero_mul, CRing.zero_add]
    have hsum : sumFin (fun k : Fin n => u ⟨k.succ.val - 1, by simp [Fin.succ]⟩ *ᵣ w ⟨k.succ.val - 1, by simp [Fin.succ]⟩) =
                sumFin (fun k : Fin n => u k *ᵣ w k) := by
      apply sumFin_congr; intro k; rfl
    exact hσ
  · -- (0, j+1): 0 * w_j + sum_k u_k * (σ Binv_{kj} - w_k w_j) = σ w_j - σ w_j = 0!
    let j' : Fin n := ⟨j.val - 1, by omega⟩
    have hne : i ≠ j := fun h => hj (by rw [← h]; exact hi)
    simp only [A, J, hi, hj, ↓reduceDIte, hne, ↓reduceIte, zero_mul, CRing.zero_add]
    have hsum :
        sumFin (fun k : Fin n => u ⟨k.succ.val - 1, by omega⟩ *ᵣ
          (σ *ᵣ Binv ⟨k.succ.val - 1, by omega⟩ j' -ᵣ w ⟨k.succ.val - 1, by omega⟩ *ᵣ w j')) =
        σ *ᵣ sumFin (fun k : Fin n => u k *ᵣ Binv k j') -ᵣ
        sumFin (fun k : Fin n => u k *ᵣ w k) *ᵣ w j' := by
      unfold rsub
      rw [← sumFin_mul_left, ← sumFin_mul_right, ← sumFin_neg, ← sumFin_add]
      apply sumFin_congr; intro k
      have hk : (⟨k.succ.val - 1, by omega⟩ : Fin n) = k := Fin.ext (by simp [Fin.succ])
      rw [hk, CRing.left_distrib, mul_neg, mul_left_comm (u k) σ, CRing.mul_assoc (u k) (w k)]
    change sumFin (fun k : Fin n => u ⟨k.succ.val - 1, by omega⟩ *ᵣ
             (σ *ᵣ Binv ⟨k.succ.val - 1, by omega⟩ j' -ᵣ w ⟨k.succ.val - 1, by omega⟩ *ᵣ w j')) = zᵣ
    rw [hsum, huBinv j', hσ]
    exact add_right_neg (σ *ᵣ w j')
  · -- (i+1, 0): u_i * (-1) + (B * w)_i = -u_i + u_i = 0!
    let i' : Fin n := ⟨i.val - 1, by omega⟩
    have hne : i ≠ j := fun h => hi (by rw [h]; exact hj)
    simp only [A, J, hi, hj, ↓reduceDIte, hne, ↓reduceIte, mul_neg, mul_one]
    have hsum : sumFin (fun k : Fin n => B i' ⟨k.succ.val - 1, by omega⟩ *ᵣ w ⟨k.succ.val - 1, by omega⟩) =
                u i' := by
      have hc : (fun k : Fin n => B i' ⟨k.succ.val - 1, by omega⟩ *ᵣ w ⟨k.succ.val - 1, by omega⟩) =
                (fun k : Fin n => B i' k *ᵣ w k) := by
        funext k; congr 1
      exact hBw i'
    change -ᵣ(u i') +ᵣ sumFin (fun k : Fin n => B i' ⟨k.succ.val - 1, by omega⟩ *ᵣ w ⟨k.succ.val - 1, by omega⟩) = zᵣ
    rw [hsum, CRing.add_left_neg]
  · -- (i+1, j+1): u_i * w_j + sum_k B_{ik} (σ Binv_{kj} - w_k w_j) = u_i w_j + σ δ_{ij} - u_i w_j = σ δ_{ij}!
    let i' : Fin n := ⟨i.val - 1, by omega⟩
    let j' : Fin n := ⟨j.val - 1, by omega⟩
    simp only [A, J, hi, hj, ↓reduceDIte]
    have hsum :
        sumFin (fun k : Fin n => B i' ⟨k.succ.val - 1, by omega⟩ *ᵣ
          (σ *ᵣ Binv ⟨k.succ.val - 1, by omega⟩ j' -ᵣ w ⟨k.succ.val - 1, by omega⟩ *ᵣ w j')) =
        σ *ᵣ matMul B Binv i' j' -ᵣ
        sumFin (fun k : Fin n => B i' k *ᵣ w k) *ᵣ w j' := by
      unfold rsub matMul
      rw [← sumFin_mul_left, ← sumFin_mul_right, ← sumFin_neg, ← sumFin_add]
      apply sumFin_congr; intro k
      have hk : (⟨k.succ.val - 1, by omega⟩ : Fin n) = k := Fin.ext (by simp [Fin.succ])
      rw [hk, CRing.left_distrib, mul_neg, mul_left_comm (B i' k) σ, CRing.mul_assoc (B i' k) (w k)]
    change u i' *ᵣ w j' +ᵣ
      sumFin (fun k : Fin n => B i' ⟨k.succ.val - 1, by omega⟩ *ᵣ
        (σ *ᵣ Binv ⟨k.succ.val - 1, by omega⟩ j' -ᵣ w ⟨k.succ.val - 1, by omega⟩ *ᵣ w j')) =
      if i = j then σ else zᵣ
    rw [hsum, hBw i', hBinv]
    unfold rsub matId
    rw [CRing.add_comm (u i' *ᵣ w j'), CRing.add_assoc, CRing.add_left_neg, add_zero]
    by_cases hij : i' = j'
    · have heq : i = j := Fin.ext (by have := congrArg Fin.val hij; simp [i', j'] at this; omega)
      simp [hij, heq, mul_one]
    · have hne : i ≠ j := fun h => hij (Fin.ext (by simp [i', j', h]))
      simp [hij, hne, mul_zero]

/-- Bridging Lemma (Row-Elimination Schur Complement):
For a symmetric bordered matrix `A = [[0, u^T], [u, B]]`, if `B * Binv = I_n` and `w = Binv * u`,
then `det A = -(u^T * w) * det B`!
This directly connects Mechanism A (`det A = -4`, `det B = 1`) to Mechanism B (`u^T * w = 4`)! -/
theorem det_bordered_schur {n : Nat} (B Binv : Mat n R) (u : Fin n → R)
    (hBinv : matMul B Binv = matId n)
    (hBsym : ∀ i j, B i j = B j i)
    (_hBinvSym : ∀ i j, Binv i j = Binv j i) :
    let w : Fin n → R := fun i => sumFin (fun r : Fin n => Binv i r *ᵣ u r)
    let A : Mat (n + 1) R := fun i j =>
      if hi : i.val = 0 then
        if hj : j.val = 0 then zᵣ else u ⟨j.val - 1, by omega⟩
      else
        if hj : j.val = 0 then u ⟨i.val - 1, by omega⟩
        else B ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
    det A = -ᵣ(sumFin (fun k : Fin n => u k *ᵣ w k)) *ᵣ det B := by
  intro w A
  -- Row-elimination helper: subtracting a linear combination of rows `1..n` from row `0` preserves `det`!
  have hRowElim : ∀ (k : Nat) (hk : k ≤ n) (M : Mat (n + 1) R) (c : Fin n → R),
      det (updateRow M ⟨0, Nat.zero_lt_succ n⟩
        (fun j => M ⟨0, Nat.zero_lt_succ n⟩ j -ᵣ
                  sumFin (fun r : Fin k => c ⟨r.val, Nat.lt_of_lt_of_le r.isLt hk⟩ *ᵣ
                                           M ⟨r.val + 1, by have := r.isLt; omega⟩ j))) = det M := by
    intro k
    induction k with
    | zero =>
      intro _ M c
      have h0 : (fun j : Fin (n + 1) => M ⟨0, Nat.zero_lt_succ n⟩ j -ᵣ
                  sumFin (fun r : Fin 0 => c ⟨r.val, Nat.lt_of_lt_of_le r.isLt (Nat.zero_le n)⟩ *ᵣ
                                           M ⟨r.val + 1, by omega⟩ j)) =
                (fun j : Fin (n + 1) => M ⟨0, Nat.zero_lt_succ n⟩ j) := by
        funext j; unfold rsub; rw [sumFin_zero, neg_zero, add_zero]
      rw [h0, updateRow_self]
    | succ t iht =>
      intro ht M c
      let prev : Fin (n + 1) → R := fun j =>
        M ⟨0, Nat.zero_lt_succ n⟩ j -ᵣ
        sumFin (fun r : Fin t => c ⟨r.val, by have := r.isLt; omega⟩ *ᵣ
                                 M ⟨r.val + 1, by have := r.isLt; omega⟩ j)
      have hsplit :
          (fun j : Fin (n + 1) => M ⟨0, Nat.zero_lt_succ n⟩ j -ᵣ
            sumFin (fun r : Fin (t + 1) => c ⟨r.val, Nat.lt_of_lt_of_le r.isLt ht⟩ *ᵣ
                                           M ⟨r.val + 1, by have := r.isLt; omega⟩ j)) =
          (fun j : Fin (n + 1) => prev j +ᵣ
            (-ᵣ(c ⟨t, by omega⟩)) *ᵣ M ⟨t + 1, by omega⟩ j) := by
        funext j
        unfold prev rsub
        rw [sumFin_succ_last, neg_add, ← CRing.add_assoc, neg_mul]
      rw [hsplit, det_updateRow_add, det_updateRow_smul]
      have hzero : det (updateRow M ⟨0, Nat.zero_lt_succ n⟩ (fun j => M ⟨t + 1, by omega⟩ j)) = zᵣ := by
        apply det_eq_zero_of_row_eq _ ⟨0, Nat.zero_lt_succ n⟩ ⟨t + 1, by omega⟩
        · exact fin_ne (by simp)
        · intro j; unfold updateRow
          have hne : (⟨t + 1, by omega⟩ : Fin (n + 1)) ≠ ⟨0, Nat.zero_lt_succ n⟩ := fin_ne (by simp)
          simp only [hne, ↓reduceIte]
      rw [hzero, mul_zero, add_zero]
      exact iht (Nat.le_of_succ_le ht) M c
  rw [← hRowElim n (Nat.le_refl n) A w]
  have hBw : ∀ j' : Fin n, sumFin (fun r : Fin n => w r *ᵣ B r j') = u j' := by
    intro j'
    have h1 : (fun r : Fin n => w r *ᵣ B r j') = (fun r : Fin n => B j' r *ᵣ w r) := by
      funext r; rw [CRing.mul_comm, hBsym]
    rw [h1]
    calc sumFin (fun r : Fin n => B j' r *ᵣ sumFin (fun s : Fin n => Binv r s *ᵣ u s))
        = sumFin (fun r : Fin n => sumFin (fun s : Fin n => B j' r *ᵣ (Binv r s *ᵣ u s))) := by
          apply sumFin_congr; intro r; rw [← sumFin_mul_left]
      _ = sumFin (fun s : Fin n => sumFin (fun r : Fin n => B j' r *ᵣ (Binv r s *ᵣ u s))) := sumFin_comm _
      _ = sumFin (fun s : Fin n => matMul B Binv j' s *ᵣ u s) := by
          apply sumFin_congr; intro s; unfold matMul; rw [← sumFin_mul_right]
          apply sumFin_congr; intro r; rw [CRing.mul_assoc]
      _ = sumFin (fun s : Fin n => (if j' = s then eᵣ else zᵣ) *ᵣ u s) := by
          apply sumFin_congr; intro s; rw [hBinv]; rfl
      _ = u j' := by
          rw [sumFin_single j']
          · simp [CRing.one_mul]
          · intro s hs; have hne : j' ≠ s := fun h => hs h.symm; simp [hne, zero_mul]
  rw [det_single_entry_row (r := ⟨0, Nat.zero_lt_succ n⟩) (c := ⟨0, Nat.zero_lt_succ n⟩)
        (s := -ᵣ(sumFin (fun k : Fin n => u k *ᵣ w k)))]
  · have hsign : rsign (R := R) ((⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)).val +
                                 (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)).val) = eᵣ := rfl
    rw [hsign, CRing.one_mul]
    apply congrArg (CRing.mul _)
    apply det_congr; intro a b
    unfold minor updateRow A
    simp only [skipIdx_zero, Fin.succ]
    have ha : a.val + 1 ≠ 0 := by omega
    have hb : b.val + 1 ≠ 0 := by omega
    simp only [ha, hb, ↓reduceDIte]
    rfl
  · intro j
    unfold updateRow A rsub
    simp only [↓reduceIte]
    by_cases hj : j = ⟨0, Nat.zero_lt_succ n⟩
    · subst hj
      simp only [↓reduceDIte, ↓reduceIte, CRing.zero_add]
      apply congrArg CRing.neg
      apply sumFin_congr; intro r
      have hr : r.val + 1 ≠ 0 := by omega
      simp only [hr, ↓reduceDIte]
      rw [CRing.mul_comm]
      rfl
    · have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp only [hj, hj0, ↓reduceDIte, ↓reduceIte]
      let j' : Fin n := ⟨j.val - 1, by omega⟩
      have hsum :
          sumFin (fun r : Fin n => w r *ᵣ (if hr : r.val + 1 = 0 then u j' else B ⟨r.val + 1 - 1, by omega⟩ j')) =
          u j' := by
        have hc : (fun r : Fin n => w r *ᵣ (if hr : r.val + 1 = 0 then u j' else B ⟨r.val + 1 - 1, by omega⟩ j')) =
                  (fun r : Fin n => w r *ᵣ B r j') := by
          funext r
          have hr : r.val + 1 ≠ 0 := by omega
          simp only [hr, ↓reduceDIte]
          rfl
        rw [hc]
        exact hBw j'
      rw [hsum, add_right_neg]

end ParityBlockInv
section BitwiseBridges
theorem lowbit_zero : lowbit 0 = 0 := by unfold lowbit; simp

theorem lowbit_odd {n : Nat} (h : n % 2 = 1) : lowbit n = 1 := by
  unfold lowbit
  have hne : n ≠ 0 := by omega
  simp [hne, h]

theorem lowbit_even {n : Nat} (hne : n ≠ 0) (he : n % 2 = 0) :
    lowbit n = 2 * lowbit (n / 2) := by
  conv => lhs; unfold lowbit
  have ho : ¬ (n % 2 = 1) := by omega
  simp [hne, ho]

theorem lowbit_two_mul (n : Nat) : lowbit (2 * n) = 2 * lowbit n := by
  cases n with
  | zero => simp [lowbit_zero]
  | succ m =>
    rw [lowbit_even (by omega) (by omega)]
    have hdiv : 2 * (m + 1) / 2 = m + 1 := by omega
    rw [hdiv]

theorem lowbit_pos (n : Nat) (h : 0 < n) : 0 < lowbit n := by
  by_cases ho : n % 2 = 1
  · rw [lowbit_odd ho]; omega
  · rw [lowbit_even (by omega) (by omega)]
    have hsub := lowbit_pos (n / 2) (by omega)
    omega
termination_by n

theorem lowbit_le (n : Nat) : lowbit n ≤ n := by
  by_cases h0 : n = 0
  · subst h0; simp [lowbit_zero]
  · by_cases ho : n % 2 = 1
    · rw [lowbit_odd ho]; omega
    · rw [lowbit_even h0 (by omega)]
      have hle := lowbit_le (n / 2)
      omega
termination_by n

theorem lowbit_two_pow (k : Nat) : lowbit (2 ^ k) = 2 ^ k := by
  induction k with
  | zero => rw [Nat.pow_zero, lowbit_odd (by omega)]
  | succ m ih =>
    rw [Nat.pow_succ, Nat.mul_comm, lowbit_two_mul, ih]

theorem lowbit_add_two_pow (k j : Nat) (hj1 : 0 < j) (hj2 : j < 2 ^ k) :
    lowbit (2 ^ k + j) = lowbit j := by
  induction k generalizing j with
  | zero => simp at hj2; omega
  | succ m ih =>
    by_cases ho : j % 2 = 1
    · have hpow : 2 ^ (m + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
      have ho2 : (2 ^ (m + 1) + j) % 2 = 1 := by omega
      rw [lowbit_odd ho, lowbit_odd ho2]
    · have he : j % 2 = 0 := by omega
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      have hne1 : 2 ^ (m + 1) + j ≠ 0 := by omega
      have he1 : (2 ^ (m + 1) + j) % 2 = 0 := by rw [hpow]; omega
      rw [lowbit_even hne1 he1, lowbit_even (by omega) he]
      have hdiv : (2 ^ (m + 1) + j) / 2 = 2 ^ m + j / 2 := by rw [hpow]; omega
      rw [hdiv, ih (j / 2) (by omega) (by rw [hpow] at hj2; omega)]

theorem add_lowbit_le_two_pow (k i : Nat) (h1 : 0 < i) (h2 : i < 2 ^ k) :
    i + lowbit i ≤ 2 ^ k := by
  induction k generalizing i with
  | zero => simp at h2; omega
  | succ m ih =>
    by_cases ho : i % 2 = 1
    · rw [lowbit_odd ho]; omega
    · have he : i % 2 = 0 := by omega
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [lowbit_even (by omega) he]
      have hsub := ih (i / 2) (by omega) (by rw [hpow] at h2; omega)
      omega

/-- Helper: bitwise AND of `q` with its `w`-bit complement `2^w - 1 - q` is `0`. -/
private theorem land_compl_zero (w q : Nat) (hq : q < 2 ^ w) :
    (q &&& (2 ^ w - 1 - q)) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_and, Nat.zero_testBit]
  induction w generalizing q b with
  | zero => simp at hq; subst hq; simp
  | succ m ih =>
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    cases b with
    | zero =>
      simp only [Nat.testBit_zero]
      have h1 : 2 ^ (m + 1) - 1 - q = 2 * (2 ^ m - 1 - q / 2) + (1 - q % 2) := by
        have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        omega
      rw [h1]
      by_cases hq2 : q % 2 = 0
      · simp [hq2]
      · have hq1 : q % 2 = 1 := by omega
        simp [hq1]
    | succ b' =>
      rw [Nat.testBit_succ, Nat.testBit_succ]
      have hdiv : (2 ^ (m + 1) - 1 - q) / 2 = 2 ^ m - 1 - q / 2 := by
        have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        omega
      rw [hdiv]
      exact ih (q / 2) (by rw [hpow] at hq; omega) b'

/-- Pure-Silicon Bitwise Characterization: `i &&& (2^w - i) = lowbit i` for all `0 < i < 2^w`! -/
theorem lowbit_eq_land_sub (w i : Nat) (h1 : 0 < i) (h2 : i < 2 ^ w) :
    (i &&& (2 ^ w - i)) = lowbit i := by
  induction w generalizing i with
  | zero => simp at h2; omega
  | succ m ih =>
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases ho : i % 2 = 1
    · rw [lowbit_odd ho]
      apply Nat.eq_of_testBit_eq; intro b
      rw [Nat.testBit_and]
      cases b with
      | zero =>
        simp only [Nat.testBit_zero]
        have hsub : (2 ^ (m + 1) - i) % 2 = 1 := by rw [hpow]; omega
        simp [ho, hsub]
      | succ b' =>
        rw [Nat.testBit_succ, Nat.testBit_succ]
        have h1b : Nat.testBit 1 (b' + 1) = false := by
          rw [Nat.testBit_succ]; simp
        rw [h1b]
        have hdiv : (2 ^ (m + 1) - i) / 2 = 2 ^ m - 1 - i / 2 := by
          have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
          omega
        rw [hdiv]
        have hzero := land_compl_zero m (i / 2) (by rw [hpow] at h2; omega)
        have htb := congrArg (fun x => Nat.testBit x b') hzero
        rw [Nat.testBit_and, Nat.zero_testBit] at htb
        exact htb
    · have he : i % 2 = 0 := by omega
      rw [lowbit_even (by omega) he]
      apply Nat.eq_of_testBit_eq; intro b
      rw [Nat.testBit_and]
      cases b with
      | zero =>
        simp only [Nat.testBit_zero]
        have h0 : (2 * lowbit (i / 2)) % 2 = 0 := by omega
        simp [he, h0]
      | succ b' =>
        rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        have hdiv1 : (2 ^ (m + 1) - i) / 2 = 2 ^ m - i / 2 := by rw [hpow]; omega
        have hdiv2 : (2 * lowbit (i / 2)) / 2 = lowbit (i / 2) := by omega
        rw [hdiv1, hdiv2]
        have hih := ih (i / 2) (by omega) (by rw [hpow] at h2; omega)
        have htb := congrArg (fun x => Nat.testBit x b') hih
        rw [Nat.testBit_and] at htb
        exact htb

/-! ### Bitwise Fenwick Update+Query Graph `G_k` on `{0, ..., 2^k}` -/

theorem fenwickEdge_symm (N i j : Nat) : fenwickEdge N i j = fenwickEdge N j i := by
  unfold fenwickEdge
  by_cases h1 : (0 < i ∧ i < N ∧ (j = i - lowbit i ∨ j = i + lowbit i)) <;>
  by_cases h2 : (0 < j ∧ j < N ∧ (i = j - lowbit j ∨ i = j + lowbit j)) <;>
  simp [h1, h2]

theorem fenwickEdge_irrefl (N i : Nat) : fenwickEdge N i i = false := by
  unfold fenwickEdge
  simp only [decide_eq_false_iff_not, not_or, not_and]
  constructor <;> (intro h1 _; have hpos := lowbit_pos i h1; omega)

theorem fenwickEdge_split_cross {k i j : Nat} (hi : i < 2 ^ k) (hj1 : 2 ^ k < j) (_hj2 : j ≤ 2 ^ (k + 1)) :
    fenwickEdge (2 ^ (k + 1)) i j = false := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  unfold fenwickEdge
  simp only [decide_eq_false_iff_not, not_or]
  constructor
  · intro ⟨hi0, _, hdir⟩
    have hle := add_lowbit_le_two_pow k i hi0 hi
    have hlb := lowbit_le i
    omega
  · intro ⟨_, hjlt, hdir⟩
    have hj'1 : 0 < j - 2 ^ k := by omega
    have hj'2 : j - 2 ^ k < 2 ^ k := by omega
    have hlb : lowbit j = lowbit (j - 2 ^ k) := by
      have heq : j = 2 ^ k + (j - 2 ^ k) := by omega
      conv => lhs; rw [heq]
      exact lowbit_add_two_pow k (j - 2 ^ k) hj'1 hj'2
    have hle := lowbit_le (j - 2 ^ k)
    omega

theorem fenwickEdge_split_left {k i j : Nat} (hi : i ≤ 2 ^ k) (hj : j ≤ 2 ^ k) :
    fenwickEdge (2 ^ (k + 1)) i j =
      (fenwickEdge (2 ^ k) i j || decide ((i = 0 ∧ j = 2 ^ k) ∨ (i = 2 ^ k ∧ j = 0))) := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hlbpow : lowbit (2 ^ k) = 2 ^ k := lowbit_two_pow k
  unfold fenwickEdge
  by_cases hch : (i = 0 ∧ j = 2 ^ k) ∨ (i = 2 ^ k ∧ j = 0)
  · have hdt : decide ((i = 0 ∧ j = 2 ^ k) ∨ (i = 2 ^ k ∧ j = 0)) = true :=
      decide_eq_true hch
    rw [hdt, Bool.or_true, decide_eq_true_eq]
    rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · right; exact ⟨hpos, by omega, Or.inl (by rw [hlbpow]; omega)⟩
    · left; exact ⟨hpos, by omega, Or.inl (by rw [hlbpow]; omega)⟩
  · have hchf : decide ((i = 0 ∧ j = 2 ^ k) ∨ (i = 2 ^ k ∧ j = 0)) = false := by
      simp [hch]
    rw [hchf, Bool.or_false]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      rcases h with ⟨hi0, _, hdir⟩ | ⟨hj0, _, hdir⟩
      · by_cases him : i = 2 ^ k
        · subst him; rw [hlbpow] at hdir
          rcases hdir with h1 | h2
          · exfalso; exact hch (Or.inr ⟨rfl, by omega⟩)
          · omega
        · left; exact ⟨hi0, by omega, hdir⟩
      · by_cases hjm : j = 2 ^ k
        · subst hjm; rw [hlbpow] at hdir
          rcases hdir with h1 | h2
          · exfalso; exact hch (Or.inl ⟨by omega, rfl⟩)
          · omega
        · right; exact ⟨hj0, by omega, hdir⟩
    · intro h
      rcases h with ⟨hi0, hilt, hdir⟩ | ⟨hj0, hjlt, hdir⟩
      · left; exact ⟨hi0, by omega, hdir⟩
      · right; exact ⟨hj0, by omega, hdir⟩

theorem fenwickEdge_split_right {k i j : Nat}
    (hi1 : 2 ^ k ≤ i) (hi2 : i ≤ 2 ^ (k + 1))
    (hj1 : 2 ^ k ≤ j) (hj2 : j ≤ 2 ^ (k + 1)) :
    fenwickEdge (2 ^ (k + 1)) i j =
      (fenwickEdge (2 ^ k) (i - 2 ^ k) (j - 2 ^ k) ||
       decide ((i = 2 ^ k ∧ j = 2 ^ (k + 1)) ∨ (i = 2 ^ (k + 1) ∧ j = 2 ^ k))) := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hlbpow : lowbit (2 ^ k) = 2 ^ k := lowbit_two_pow k
  unfold fenwickEdge
  by_cases hch : (i = 2 ^ k ∧ j = 2 ^ (k + 1)) ∨ (i = 2 ^ (k + 1) ∧ j = 2 ^ k)
  · have hdt : decide ((i = 2 ^ k ∧ j = 2 ^ (k + 1)) ∨ (i = 2 ^ (k + 1) ∧ j = 2 ^ k)) = true :=
      decide_eq_true hch
    rw [hdt, Bool.or_true, decide_eq_true_eq]
    rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨hpos, by omega, Or.inr (by rw [hlbpow]; omega)⟩
    · right; exact ⟨hpos, by omega, Or.inr (by rw [hlbpow]; omega)⟩
  · have hchf : decide ((i = 2 ^ k ∧ j = 2 ^ (k + 1)) ∨ (i = 2 ^ (k + 1) ∧ j = 2 ^ k)) = false := by
      simp [hch]
    rw [hchf, Bool.or_false]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      rcases h with ⟨_, hilt, hdir⟩ | ⟨_, hjlt, hdir⟩
      · by_cases him : i = 2 ^ k
        · subst him; rw [hlbpow] at hdir
          rcases hdir with h1 | h2
          · omega
          · exfalso; exact hch (Or.inl ⟨rfl, by omega⟩)
        · have hi'1 : 0 < i - 2 ^ k := by omega
          have hi'2 : i - 2 ^ k < 2 ^ k := by omega
          have hlb : lowbit i = lowbit (i - 2 ^ k) := by
            have heq : i = 2 ^ k + (i - 2 ^ k) := by omega
            conv => lhs; rw [heq]
            exact lowbit_add_two_pow k (i - 2 ^ k) hi'1 hi'2
          have hle := lowbit_le (i - 2 ^ k)
          rw [hlb] at hdir
          left; exact ⟨hi'1, hi'2, by omega⟩
      · by_cases hjm : j = 2 ^ k
        · subst hjm; rw [hlbpow] at hdir
          rcases hdir with h1 | h2
          · omega
          · exfalso; exact hch (Or.inr ⟨by omega, rfl⟩)
        · have hj'1 : 0 < j - 2 ^ k := by omega
          have hj'2 : j - 2 ^ k < 2 ^ k := by omega
          have hlb : lowbit j = lowbit (j - 2 ^ k) := by
            have heq : j = 2 ^ k + (j - 2 ^ k) := by omega
            conv => lhs; rw [heq]
            exact lowbit_add_two_pow k (j - 2 ^ k) hj'1 hj'2
          have hle := lowbit_le (j - 2 ^ k)
          rw [hlb] at hdir
          right; exact ⟨hj'1, hj'2, by omega⟩
    · intro h
      rcases h with ⟨hi'1, hi'2, hdir⟩ | ⟨hj'1, hj'2, hdir⟩
      · have hlb : lowbit i = lowbit (i - 2 ^ k) := by
          have heq : i = 2 ^ k + (i - 2 ^ k) := by omega
          conv => lhs; rw [heq]
          exact lowbit_add_two_pow k (i - 2 ^ k) hi'1 hi'2
        have hle := lowbit_le (i - 2 ^ k)
        left; exact ⟨by omega, by omega, by rw [hlb]; omega⟩
      · have hlb : lowbit j = lowbit (j - 2 ^ k) := by
          have heq : j = 2 ^ k + (j - 2 ^ k) := by omega
          conv => lhs; rw [heq]
          exact lowbit_add_two_pow k (j - 2 ^ k) hj'1 hj'2
        have hle := lowbit_le (j - 2 ^ k)
        right; exact ⟨by omega, by omega, by rw [hlb]; omega⟩

theorem fenwickEdge_endpoints_false (k : Nat) : fenwickEdge (2 ^ k) 0 (2 ^ k) = false := by
  unfold fenwickEdge; simp

theorem fenwickEdge_endpoints_false' (k : Nat) : fenwickEdge (2 ^ k) (2 ^ k) 0 = false := by
  unfold fenwickEdge; simp

section BitwiseMatrices
variable {R : Type} [CRing R]

theorem det_castPortal {k : Nat} (hk : 1 ≤ k) (M : Mat (2 ^ k + 1) R) :
    det (castPortal hk M) = det M := by
  have hge : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hsz : (2 ^ k - 1) + 2 = 2 ^ k + 1 := by omega
  rw [det_cast hsz (castPortal hk M)]
  rfl

theorem two_le_two_pow {k : Nat} (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk

theorem glue_dim_eq {k : Nat} (hk : 1 ≤ k) :
    ((2 ^ k - 1) + (2 ^ k - 1) + 1) + 2 = 2 ^ (k + 1) + 1 := by
  have h2k := two_le_two_pow hk
  rw [Nat.pow_succ]; omega

/-! ### Clean Entrywise Evaluation Lemmas for `perturb` -/

theorem perturb_00 {n : Nat} (M : Mat (n + 2) R) (p q1 q2 r : R) (i j : Fin (n + 2))
    (hi : i.val = 0) (hj : j.val = 0) : perturb M p q1 q2 r i j = M i j +ᵣ p := by
  unfold perturb
  have h1 : i.val = 0 ∧ j.val = 0 := ⟨hi, hj⟩
  simp only [h1, and_self, ↓reduceIte]

theorem perturb_0L {n : Nat} (M : Mat (n + 2) R) (p q1 q2 r : R) (i j : Fin (n + 2))
    (hi : i.val = 0) (hj : j.val = n + 1) : perturb M p q1 q2 r i j = M i j +ᵣ q1 := by
  unfold perturb
  have h1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
  have h2 : i.val = 0 ∧ j.val = n + 1 := ⟨hi, hj⟩
  simp only [h1, ↓reduceIte]; simp only [h2, and_self, ↓reduceIte]

theorem perturb_L0 {n : Nat} (M : Mat (n + 2) R) (p q1 q2 r : R) (i j : Fin (n + 2))
    (hi : i.val = n + 1) (hj : j.val = 0) : perturb M p q1 q2 r i j = M i j +ᵣ q2 := by
  unfold perturb
  have h1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
  have h2 : ¬ (i.val = 0 ∧ j.val = n + 1) := by omega
  have h3 : i.val = n + 1 ∧ j.val = 0 := ⟨hi, hj⟩
  simp only [h1, h2, ↓reduceIte]; simp only [h3, and_self, ↓reduceIte]

theorem perturb_LL {n : Nat} (M : Mat (n + 2) R) (p q1 q2 r : R) (i j : Fin (n + 2))
    (hi : i.val = n + 1) (hj : j.val = n + 1) : perturb M p q1 q2 r i j = M i j +ᵣ r := by
  unfold perturb
  have h1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
  have h2 : ¬ (i.val = 0 ∧ j.val = n + 1) := by omega
  have h3 : ¬ (i.val = n + 1 ∧ j.val = 0) := by omega
  have h4 : i.val = n + 1 ∧ j.val = n + 1 := ⟨hi, hj⟩
  simp only [h1, h2, h3, ↓reduceIte]; simp only [h4, and_self, ↓reduceIte]

theorem perturb_other {n : Nat} (M : Mat (n + 2) R) (p q1 q2 r : R) (i j : Fin (n + 2))
    (h1 : ¬ (i.val = 0 ∧ j.val = 0))
    (h2 : ¬ (i.val = 0 ∧ j.val = n + 1))
    (h3 : ¬ (i.val = n + 1 ∧ j.val = 0))
    (h4 : ¬ (i.val = n + 1 ∧ j.val = n + 1)) :
    perturb M p q1 q2 r i j = M i j := by
  unfold perturb
  simp only [h1, h2, h3, h4, ↓reduceIte, add_zero]

/-- Bridge 1: Exact entrywise equality showing the bitwise-defined `fenwickUQAdj (k + 1) c`
EQUALS `glue (perturb (fenwickUQAdj k c) 0 c c 0) (perturb (fenwickUQAdj k c) 0 c c 0) 0`! -/
theorem fenwickUQAdj_step (k : Nat) (hk : 1 ≤ k) (c : R) :
    let M := castPortal hk (fenwickUQAdj k c)
    let G := glue (perturb M zᵣ c c zᵣ) (perturb M zᵣ c c zᵣ) zᵣ
    ∀ (i j : Fin (2 ^ (k + 1) + 1)),
      fenwickUQAdj (k + 1) c i j =
      G ⟨i.val, by have := i.isLt; have := glue_dim_eq hk; omega⟩
        ⟨j.val, by have := j.isLt; have := glue_dim_eq hk; omega⟩ := by
  have h2k := two_le_two_pow hk
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  intro M G i j
  unfold G glue
  by_cases hi1 : i.val < 2 ^ k
  · have hi1' : i.val < (2 ^ k - 1) + 1 := by omega
    simp only [hi1', ↓reduceDIte]
    by_cases hj1 : j.val ≤ 2 ^ k
    · have hj1' : j.val ≤ (2 ^ k - 1) + 1 := by omega
      simp only [hj1', ↓reduceDIte]
      by_cases h0L : i.val = 0 ∧ j.val = 2 ^ k
      · rcases h0L with ⟨hi0, hj2k⟩
        rw [perturb_0L _ _ _ _ _ _ _ (by dsimp only; exact hi0) (by dsimp only; omega)]
        unfold M castPortal fenwickUQAdj
        dsimp only
        rw [fenwickEdge_split_left (by omega) hj1]
        have hfe : fenwickEdge (2 ^ k) i.val j.val = false := by
          rw [hi0, hj2k]; exact fenwickEdge_endpoints_false k
        have hch : decide ((i.val = 0 ∧ j.val = 2 ^ k) ∨ (i.val = 2 ^ k ∧ j.val = 0)) = true :=
          decide_eq_true (Or.inl ⟨hi0, hj2k⟩)
        have hnot1 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
        simp only [hfe, hch, Bool.false_or, hnot1, Bool.false_eq_true, ↓reduceIte, CRing.zero_add]
      · by_cases h00 : i.val = 0 ∧ j.val = 0
        · rw [perturb_00 _ _ _ _ _ _ _ (by dsimp only; exact h00.1) (by dsimp only; exact h00.2), add_zero]
          unfold M castPortal fenwickUQAdj
          dsimp only
          rw [fenwickEdge_split_left (by omega) hj1]
          have hch : decide ((i.val = 0 ∧ j.val = 2 ^ k) ∨ (i.val = 2 ^ k ∧ j.val = 0)) = false := decide_eq_false (by omega)
          simp only [hch, Bool.or_false]
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          unfold M castPortal fenwickUQAdj
          dsimp only
          rw [fenwickEdge_split_left (by omega) hj1]
          have hch : decide ((i.val = 0 ∧ j.val = 2 ^ k) ∨ (i.val = 2 ^ k ∧ j.val = 0)) = false := decide_eq_false (by omega)
          simp only [hch, Bool.or_false]
    · have hj1' : ¬ (j.val ≤ (2 ^ k - 1) + 1) := by omega
      simp only [hj1', ↓reduceDIte]
      unfold fenwickUQAdj
      rw [fenwickEdge_split_cross hi1 (by omega) (by have := j.isLt; omega)]
      simp
  · by_cases hi2 : i.val = 2 ^ k
    · have hi1' : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
      have hi2' : i.val = (2 ^ k - 1) + 1 := by omega
      simp only [hi1', ↓reduceDIte]; simp only [hi2', ↓reduceDIte]
      by_cases hj1 : j.val < 2 ^ k
      · have hj1' : j.val < (2 ^ k - 1) + 1 := by omega
        simp only [hj1', ↓reduceDIte]
        by_cases hj0 : j.val = 0
        · rw [perturb_L0 _ _ _ _ _ _ _ rfl (by dsimp only; exact hj0)]
          unfold M castPortal fenwickUQAdj
          dsimp only
          rw [fenwickEdge_split_left (by omega) (by omega)]
          have hfe : fenwickEdge (2 ^ k) i.val j.val = false := by
            rw [hi2, hj0]; exact fenwickEdge_endpoints_false' k
          have hfe' : fenwickEdge (2 ^ k) ((2 ^ k - 1) + 1) j.val = false := by
            have : (2 ^ k - 1) + 1 = 2 ^ k := by omega
            rw [this, hj0]; exact fenwickEdge_endpoints_false' k
          have hch : decide ((i.val = 0 ∧ j.val = 2 ^ k) ∨ (i.val = 2 ^ k ∧ j.val = 0)) = true :=
            decide_eq_true (Or.inr ⟨hi2, hj0⟩)
          have hnot1 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
          simp only [hfe, hfe', hch, Bool.false_or, hnot1, Bool.false_eq_true, ↓reduceIte, CRing.zero_add]
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          unfold M castPortal fenwickUQAdj
          dsimp only
          rw [fenwickEdge_split_left (by omega) (by omega)]
          have hch : decide ((i.val = 0 ∧ j.val = 2 ^ k) ∨ (i.val = 2 ^ k ∧ j.val = 0)) = false := decide_eq_false (by omega)
          have hm : (2 ^ k - 1) + 1 = i.val := by omega
          simp only [hch, Bool.or_false, hm]
      · by_cases hj2 : j.val = 2 ^ k
        · have hj1' : ¬ (j.val < (2 ^ k - 1) + 1) := by omega
          have hj2' : j.val = (2 ^ k - 1) + 1 := by omega
          simp only [hj1', ↓reduceDIte]; simp only [hj2', ↓reduceDIte, add_zero]
          rw [perturb_LL _ _ _ _ _ _ _ rfl rfl, add_zero]
          rw [perturb_00 _ _ _ _ _ _ _ rfl rfl, add_zero]
          unfold M castPortal fenwickUQAdj
          dsimp only
          have h1 : fenwickEdge (2 ^ (k + 1)) i.val j.val = false := by rw [hi2, hj2]; exact fenwickEdge_irrefl _ _
          rw [h1, fenwickEdge_irrefl, fenwickEdge_irrefl]
          simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        · have hj1' : ¬ (j.val < (2 ^ k - 1) + 1) := by omega
          have hj2' : ¬ (j.val = (2 ^ k - 1) + 1) := by omega
          simp only [hj1', ↓reduceDIte]; simp only [hj2', ↓reduceDIte]
          by_cases hjend : j.val = 2 ^ (k + 1)
          · rw [perturb_0L _ _ _ _ _ _ _ rfl (by dsimp only; omega)]
            unfold M castPortal fenwickUQAdj
            dsimp only
            rw [fenwickEdge_split_right (by omega) (by omega) (by omega) (by omega)]
            have hfe : fenwickEdge (2 ^ k) (i.val - 2 ^ k) (j.val - 2 ^ k) = false := by
              have ha : i.val - 2 ^ k = 0 := by omega
              have hb : j.val - 2 ^ k = 2 ^ k := by omega
              rw [ha, hb]; exact fenwickEdge_endpoints_false k
            have hfe' : fenwickEdge (2 ^ k) 0 (j.val - ((2 ^ k - 1) + 1)) = false := by
              have hb : j.val - ((2 ^ k - 1) + 1) = 2 ^ k := by omega
              rw [hb]; exact fenwickEdge_endpoints_false k
            have hch : decide ((i.val = 2 ^ k ∧ j.val = 2 ^ (k + 1)) ∨ (i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ k)) = true :=
              decide_eq_true (Or.inl ⟨hi2, hjend⟩)
            have hnot1 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
            simp only [hfe, hfe', hch, Bool.false_or, hnot1, Bool.false_eq_true, ↓reduceIte, CRing.zero_add]
          · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
            unfold M castPortal fenwickUQAdj
            dsimp only
            rw [fenwickEdge_split_right (by omega) (by omega) (by omega) (by have := j.isLt; omega)]
            have hch : decide ((i.val = 2 ^ k ∧ j.val = 2 ^ (k + 1)) ∨ (i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ k)) = false := decide_eq_false (by omega)
            have ha : i.val - 2 ^ k = 0 := by omega
            have hb : j.val - ((2 ^ k - 1) + 1) = j.val - 2 ^ k := by omega
            have hiff : (i.val + 1 = j.val ∨ j.val + 1 = i.val) ↔
                        (0 + 1 = j.val - 2 ^ k ∨ j.val - 2 ^ k + 1 = 0) := by omega
            simp only [hch, Bool.or_false, ha, hb, hiff]
    · have hi1' : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
      have hi2' : ¬ (i.val = (2 ^ k - 1) + 1) := by omega
      simp only [hi1', ↓reduceDIte]; simp only [hi2', ↓reduceDIte]
      by_cases hj1 : j.val < 2 ^ k
      · have hj1' : j.val < (2 ^ k - 1) + 1 := by omega
        simp only [hj1', ↓reduceDIte]
        unfold fenwickUQAdj
        rw [fenwickEdge_symm, fenwickEdge_split_cross hj1 (by omega) (by have := i.isLt; omega)]
        simp
      · have hj1' : ¬ (j.val < (2 ^ k - 1) + 1) := by omega
        simp only [hj1', ↓reduceDIte]
        by_cases hL0 : i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ k
        · rcases hL0 with ⟨hiend, hj2k⟩
          rw [perturb_L0 _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega)]
          unfold M castPortal fenwickUQAdj
          dsimp only
          rw [fenwickEdge_split_right (by omega) (by omega) (by omega) (by omega)]
          have hfe : fenwickEdge (2 ^ k) (i.val - 2 ^ k) (j.val - 2 ^ k) = false := by
            have ha : i.val - 2 ^ k = 2 ^ k := by omega
            have hb : j.val - 2 ^ k = 0 := by omega
            rw [ha, hb]; exact fenwickEdge_endpoints_false' k
          have hfe' : fenwickEdge (2 ^ k) (i.val - ((2 ^ k - 1) + 1)) (j.val - ((2 ^ k - 1) + 1)) = false := by
            have ha : i.val - ((2 ^ k - 1) + 1) = 2 ^ k := by omega
            have hb : j.val - ((2 ^ k - 1) + 1) = 0 := by omega
            rw [ha, hb]; exact fenwickEdge_endpoints_false' k
          have hch : decide ((i.val = 2 ^ k ∧ j.val = 2 ^ (k + 1)) ∨ (i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ k)) = true :=
            decide_eq_true (Or.inr ⟨hiend, hj2k⟩)
          have hnot1 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
          simp only [hfe, hfe', hch, Bool.false_or, hnot1, Bool.false_eq_true, ↓reduceIte, CRing.zero_add]
        · by_cases hLL : i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ (k + 1)
          · rw [perturb_LL _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega), add_zero]
            unfold M castPortal fenwickUQAdj
            dsimp only
            rw [fenwickEdge_split_right (by omega) (by omega) (by omega) (by omega)]
            have hch : decide ((i.val = 2 ^ k ∧ j.val = 2 ^ (k + 1)) ∨ (i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ k)) = false := decide_eq_false (by omega)
            have ha : i.val - ((2 ^ k - 1) + 1) = i.val - 2 ^ k := by omega
            have hb : j.val - ((2 ^ k - 1) + 1) = j.val - 2 ^ k := by omega
            have hiff : (i.val + 1 = j.val ∨ j.val + 1 = i.val) ↔
                        (i.val - 2 ^ k + 1 = j.val - 2 ^ k ∨ j.val - 2 ^ k + 1 = i.val - 2 ^ k) := by omega
            simp only [hch, Bool.or_false, ha, hb, hiff]
          · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
            unfold M castPortal fenwickUQAdj
            dsimp only
            rw [fenwickEdge_split_right (by omega) (by have := i.isLt; omega) (by omega) (by have := j.isLt; omega)]
            have hch : decide ((i.val = 2 ^ k ∧ j.val = 2 ^ (k + 1)) ∨ (i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ k)) = false := decide_eq_false (by omega)
            have ha : i.val - ((2 ^ k - 1) + 1) = i.val - 2 ^ k := by omega
            have hb : j.val - ((2 ^ k - 1) + 1) = j.val - 2 ^ k := by omega
            have hiff : (i.val + 1 = j.val ∨ j.val + 1 = i.val) ↔
                        (i.val - 2 ^ k + 1 = j.val - 2 ^ k ∨ j.val - 2 ^ k + 1 = i.val - 2 ^ k) := by omega
            simp only [hch, Bool.or_false, ha, hb, hiff]

/-- Degree splitting lemma for `fenwickUQDeg (k + 1)` (used for Laplacian & Signless Laplacian bridges!). -/
theorem fenwickUQDeg_step (k : Nat) (hk : 1 ≤ k) (i : Fin (2 ^ (k + 1) + 1)) :
    fenwickUQDeg (R := R) (k + 1) i =
      if hi1 : i.val < 2 ^ k then
        fenwickUQDeg k ⟨i.val, by omega⟩ +ᵣ (if i.val = 0 then eᵣ else zᵣ)
      else if hi2 : i.val = 2 ^ k then
        (fenwickUQDeg k ⟨2 ^ k, by omega⟩ +ᵣ eᵣ) +ᵣ (fenwickUQDeg k ⟨0, by omega⟩ +ᵣ eᵣ)
      else
        fenwickUQDeg k ⟨i.val - 2 ^ k, by have := i.isLt; have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := (by rw [Nat.pow_succ]; omega); omega⟩ +ᵣ
        (if i.val = 2 ^ (k + 1) then eᵣ else zᵣ) := by
  have h2k := two_le_two_pow hk
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  unfold fenwickUQDeg
  have hsz : 2 ^ (k + 1) + 1 = (2 ^ k + 1) + 2 ^ k := by omega
  rw [sumFin_cast hsz (fun j => fenwickUQAdj (R := R) (k + 1) eᵣ i j)]
  rw [sumFin_append]
  have hstep := fenwickUQAdj_step (R := R) k hk eᵣ
  by_cases hi1 : i.val < 2 ^ k
  · simp only [hi1, ↓reduceDIte]
    have hR : sumFin (fun j : Fin (2 ^ k) =>
        fenwickUQAdj (R := R) (k + 1) eᵣ i ⟨2 ^ k + 1 + j.val, by omega⟩) = zᵣ := by
      rw [sumFin_congr (g := fun _ => zᵣ)]
      · exact sumFin_const_zero
      · intro j; rw [hstep]; unfold glue
        have ha : i.val < (2 ^ k - 1) + 1 := by omega
        have hb : ¬ (2 ^ k + 1 + j.val ≤ (2 ^ k - 1) + 1) := by omega
        simp only [ha, hb, ↓reduceDIte]
    rw [hR, add_zero]
    have hL :
        (fun j : Fin (2 ^ k + 1) => fenwickUQAdj (R := R) (k + 1) eᵣ i ⟨j.val, by omega⟩) =
        (fun j : Fin (2 ^ k + 1) => fenwickUQAdj (R := R) k eᵣ ⟨i.val, by omega⟩ j +ᵣ
          (if j = ⟨2 ^ k, by omega⟩ then (if i.val = 0 then eᵣ else zᵣ) else zᵣ)) := by
      funext j; rw [hstep]; unfold glue
      have ha : i.val < (2 ^ k - 1) + 1 := by omega
      have hb : j.val ≤ (2 ^ k - 1) + 1 := by have := j.isLt; omega
      simp only [ha, hb, ↓reduceDIte]
      by_cases hj : j.val = 2 ^ k
      · have hjeq : j = ⟨2 ^ k, by omega⟩ := Fin.ext hj
        simp only [hjeq, ↓reduceIte]
        by_cases hi0 : i.val = 0
        · rw [perturb_0L _ _ _ _ _ _ _ (by dsimp only; exact hi0) (by dsimp only; omega)]
          simp only [hi0, ↓reduceIte]; rfl
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          simp only [hi0, ↓reduceIte, add_zero]; rfl
      · have hjne : j ≠ ⟨2 ^ k, by omega⟩ := fin_ne hj
        simp only [hjne, ↓reduceIte, add_zero]
        by_cases h00 : i.val = 0 ∧ j.val = 0
        · rw [perturb_00 _ _ _ _ _ _ _ (by dsimp only; exact h00.1) (by dsimp only; exact h00.2), add_zero]; rfl
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]; rfl
    rw [hL, sumFin_add]
    have hs : sumFin (fun j : Fin (2 ^ k + 1) => if j = ⟨2 ^ k, by omega⟩ then (if i.val = 0 then (eᵣ : R) else zᵣ) else zᵣ) =
              if i.val = 0 then eᵣ else zᵣ := by
      rw [sumFin_single ⟨2 ^ k, by omega⟩]
      · simp only [↓reduceIte]
      · intro j hj; simp only [hj, ↓reduceIte]
    rw [hs]
  · by_cases hi2 : i.val = 2 ^ k
    · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]
      have hL :
          sumFin (fun j : Fin (2 ^ k + 1) => fenwickUQAdj (R := R) (k + 1) eᵣ i ⟨j.val, by omega⟩) =
          sumFin (fun j : Fin (2 ^ k + 1) => fenwickUQAdj (R := R) k eᵣ ⟨2 ^ k, by omega⟩ j) +ᵣ eᵣ := by
        have hf :
            (fun j : Fin (2 ^ k + 1) => fenwickUQAdj (R := R) (k + 1) eᵣ i ⟨j.val, by omega⟩) =
            (fun j : Fin (2 ^ k + 1) => fenwickUQAdj (R := R) k eᵣ ⟨2 ^ k, by omega⟩ j +ᵣ
              (if j = ⟨0, by omega⟩ then eᵣ else zᵣ)) := by
          funext j; rw [hstep]; unfold glue
          have ha1 : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
          have ha2 : i.val = (2 ^ k - 1) + 1 := by omega
          simp only [ha1, ↓reduceDIte]; simp only [ha2, ↓reduceDIte]
          by_cases hj : j.val = 2 ^ k
          · have hj1 : ¬ (j.val < (2 ^ k - 1) + 1) := by omega
            have hj2 : j.val = (2 ^ k - 1) + 1 := by omega
            have hjne : j ≠ ⟨0, by omega⟩ := fin_ne (by dsimp only; omega)
            simp only [hj1, ↓reduceDIte]; simp only [hj2, hjne, ↓reduceDIte, ↓reduceIte, add_zero]
            rw [perturb_LL _ _ _ _ _ _ _ rfl rfl, add_zero]
            rw [perturb_00 _ _ _ _ _ _ _ rfl rfl, add_zero]
            unfold castPortal fenwickUQAdj
            dsimp only
            have h1 : fenwickEdge (2 ^ k) (2 ^ k) j.val = false := by rw [hj]; exact fenwickEdge_irrefl _ _
            rw [h1, fenwickEdge_irrefl, fenwickEdge_irrefl]
            simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
          · have hj1 : j.val < (2 ^ k - 1) + 1 := by have := j.isLt; omega
            simp only [hj1, ↓reduceDIte]
            by_cases hj0 : j.val = 0
            · have hjeq : j = ⟨0, by omega⟩ := Fin.ext hj0
              rw [perturb_L0 _ _ _ _ _ _ _ rfl (by dsimp only; exact hj0)]
              simp only [hjeq, ↓reduceIte]
              unfold castPortal
              apply congrArg (· +ᵣ eᵣ)
              congr 1
              exact Fin.ext (by dsimp only; omega)
            · have hjne : j ≠ ⟨0, by omega⟩ := fin_ne hj0
              simp only [hjne, ↓reduceIte, add_zero]
              rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
              unfold castPortal
              have hr : (⟨(2 ^ k - 1) + 1, by omega⟩ : Fin (2 ^ k + 1)) = ⟨2 ^ k, by omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hr]
        rw [hf, sumFin_add]
        have hs : sumFin (fun j : Fin (2 ^ k + 1) => if j = ⟨0, by omega⟩ then (eᵣ : R) else zᵣ) = eᵣ := by
          rw [sumFin_single ⟨0, by omega⟩]
          · simp only [↓reduceIte]
          · intro j hj; simp only [hj, ↓reduceIte]
        rw [hs]
      have hR :
          sumFin (fun j : Fin (2 ^ k) => fenwickUQAdj (R := R) (k + 1) eᵣ i ⟨2 ^ k + 1 + j.val, by omega⟩) =
          sumFin (fun j : Fin (2 ^ k + 1) => fenwickUQAdj (R := R) k eᵣ ⟨0, by omega⟩ j) +ᵣ eᵣ := by
        rw [sumFin_succ (fun j : Fin (2 ^ k + 1) => fenwickUQAdj (R := R) k eᵣ ⟨0, by omega⟩ j)]
        have h00 : fenwickUQAdj (R := R) k eᵣ ⟨0, by omega⟩ ⟨0, by omega⟩ = zᵣ := by
          unfold fenwickUQAdj; rw [fenwickEdge_irrefl]; simp
        rw [h00, CRing.zero_add]
        have hf :
            (fun j : Fin (2 ^ k) => fenwickUQAdj (R := R) (k + 1) eᵣ i ⟨2 ^ k + 1 + j.val, by omega⟩) =
            (fun j : Fin (2 ^ k) => fenwickUQAdj (R := R) k eᵣ ⟨0, by omega⟩ j.succ +ᵣ
              (if j = ⟨2 ^ k - 1, by omega⟩ then eᵣ else zᵣ)) := by
          funext j; rw [hstep]; unfold glue
          have ha1 : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
          have ha2 : i.val = (2 ^ k - 1) + 1 := by omega
          have hb1 : ¬ (2 ^ k + 1 + j.val < (2 ^ k - 1) + 1) := by omega
          have hb2 : ¬ (2 ^ k + 1 + j.val = (2 ^ k - 1) + 1) := by omega
          simp only [ha1, hb1, ↓reduceDIte]; simp only [ha2, hb2, ↓reduceDIte]
          have hsub : 2 ^ k + 1 + j.val - ((2 ^ k - 1) + 1) = j.val + 1 := by omega
          by_cases hj : j.val = 2 ^ k - 1
          · have hjeq : j = ⟨2 ^ k - 1, by omega⟩ := Fin.ext hj
            rw [perturb_0L _ _ _ _ _ _ _ rfl (by dsimp only; omega)]
            simp only [hjeq, ↓reduceIte]
            unfold castPortal
            apply congrArg (· +ᵣ eᵣ)
            congr 1
            exact Fin.ext (by dsimp only [Fin.succ]; omega)
          · have hjne : j ≠ ⟨2 ^ k - 1, by omega⟩ := fin_ne hj
            simp only [hjne, ↓reduceIte, add_zero]
            rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
            unfold castPortal
            have hc : (⟨2 ^ k + 1 + j.val - ((2 ^ k - 1) + 1), by omega⟩ : Fin (2 ^ k + 1)) = j.succ :=
              Fin.ext (by dsimp only [Fin.succ]; omega)
            rw [hc]
        rw [hf, sumFin_add]
        have hs : sumFin (fun j : Fin (2 ^ k) => if j = ⟨2 ^ k - 1, by omega⟩ then (eᵣ : R) else zᵣ) = eᵣ := by
          rw [sumFin_single ⟨2 ^ k - 1, by omega⟩]
          · simp only [↓reduceIte]
          · intro j hj; simp only [hj, ↓reduceIte]
        rw [hs]
      rw [hL, hR]
    · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]
      rw [sumFin_succ_last (fun j : Fin (2 ^ k + 1) => fenwickUQAdj (R := R) (k + 1) eᵣ i ⟨j.val, by omega⟩)]
      have hZero : sumFin (fun j : Fin (2 ^ k) => fenwickUQAdj (R := R) (k + 1) eᵣ i ⟨j.val, by omega⟩) = zᵣ := by
        rw [sumFin_congr (g := fun _ => zᵣ)]
        · exact sumFin_const_zero
        · intro j; rw [hstep]; unfold glue
          have ha1 : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
          have ha2 : ¬ (i.val = (2 ^ k - 1) + 1) := by omega
          have hb1 : j.val < (2 ^ k - 1) + 1 := by have := j.isLt; omega
          simp only [ha1, ha2, hb1, ↓reduceDIte]
      rw [hZero, CRing.zero_add]
      rw [sumFin_succ (fun j : Fin (2 ^ k + 1) =>
        fenwickUQAdj (R := R) k eᵣ ⟨i.val - 2 ^ k, by have := i.isLt; omega⟩ j)]
      have hHead :
          fenwickUQAdj (R := R) (k + 1) eᵣ i ⟨2 ^ k, by omega⟩ =
          fenwickUQAdj (R := R) k eᵣ ⟨i.val - 2 ^ k, by have := i.isLt; omega⟩ ⟨0, by omega⟩ +ᵣ
          (if i.val = 2 ^ (k + 1) then eᵣ else zᵣ) := by
        rw [hstep]; unfold glue
        have ha1 : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
        have ha2 : ¬ (i.val = (2 ^ k - 1) + 1) := by omega
        have hb1 : ¬ (2 ^ k < (2 ^ k - 1) + 1) := by omega
        simp only [ha1, ha2, hb1, ↓reduceDIte]
        by_cases hiend : i.val = 2 ^ (k + 1)
        · rw [perturb_L0 _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega)]
          simp only [hiend, ↓reduceIte]
          unfold castPortal
          have hr : (⟨2 ^ (k + 1) - ((2 ^ k - 1) + 1), by omega⟩ : Fin (2 ^ k + 1)) =
                    ⟨2 ^ (k + 1) - 2 ^ k, by omega⟩ := Fin.ext (by dsimp only; omega)
          have hc : (⟨2 ^ k - ((2 ^ k - 1) + 1), by omega⟩ : Fin (2 ^ k + 1)) = ⟨0, by omega⟩ :=
            Fin.ext (by dsimp only; omega)
          rw [hr, hc]
        · simp only [hiend, ↓reduceIte, add_zero]
          rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          unfold castPortal
          have hr : (⟨i.val - ((2 ^ k - 1) + 1), by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) =
                    ⟨i.val - 2 ^ k, by have := i.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
          have hc : (⟨2 ^ k - ((2 ^ k - 1) + 1), by omega⟩ : Fin (2 ^ k + 1)) = ⟨0, by omega⟩ :=
            Fin.ext (by dsimp only; omega)
          rw [hr, hc]
      have hTail :
          sumFin (fun j : Fin (2 ^ k) => fenwickUQAdj (R := R) (k + 1) eᵣ i ⟨2 ^ k + 1 + j.val, by omega⟩) =
          sumFin (fun j : Fin (2 ^ k) => fenwickUQAdj (R := R) k eᵣ ⟨i.val - 2 ^ k, by have := i.isLt; omega⟩ j.succ) := by
        apply sumFin_congr; intro j
        rw [hstep]; unfold glue
        have ha1 : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
        have ha2 : ¬ (i.val = (2 ^ k - 1) + 1) := by omega
        have hb1 : ¬ (2 ^ k + 1 + j.val < (2 ^ k - 1) + 1) := by omega
        simp only [ha1, ha2, hb1, ↓reduceDIte]
        have hr : (⟨i.val - ((2 ^ k - 1) + 1), by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) =
                  ⟨i.val - 2 ^ k, by have := i.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
        have hc : (⟨2 ^ k + 1 + j.val - ((2 ^ k - 1) + 1), by have := j.isLt; omega⟩ : Fin (2 ^ k + 1)) = j.succ :=
          Fin.ext (by dsimp only [Fin.succ]; omega)
        by_cases hLL : i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ k - 1
        · rw [perturb_LL _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega), add_zero]
          unfold castPortal; rw [hr, hc]
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          unfold castPortal; rw [hr, hc]
      rw [hHead, hTail, CRing.add_assoc, CRing.add_comm (if i.val = 2 ^ (k + 1) then eᵣ else zᵣ), ← CRing.add_assoc]

/-- Bridge 2: Exact entrywise equality for the bitwise Laplacian `fenwickUQLap (k + 1)`! -/
theorem fenwickUQLap_step (k : Nat) (hk : 1 ≤ k) :
    let M := castPortal hk (fenwickUQLap (R := R) k)
    let G := glue (perturb M eᵣ (-ᵣeᵣ) (-ᵣeᵣ) eᵣ) (perturb M eᵣ (-ᵣeᵣ) (-ᵣeᵣ) eᵣ) zᵣ
    ∀ (i j : Fin (2 ^ (k + 1) + 1)),
      fenwickUQLap (R := R) (k + 1) i j =
      G ⟨i.val, by have := i.isLt; have := glue_dim_eq hk; omega⟩
        ⟨j.val, by have := j.isLt; have := glue_dim_eq hk; omega⟩ := by
  have h2k := two_le_two_pow hk
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  intro M G i j
  have hA := fenwickUQAdj_step (R := R) k hk eᵣ i j
  have hD := fenwickUQDeg_step (R := R) k hk i
  unfold fenwickUQLap rsub
  rw [hA, hD]
  unfold G glue
  by_cases hi1 : i.val < 2 ^ k
  · have hi1' : i.val < (2 ^ k - 1) + 1 := by omega
    simp only [hi1, hi1', ↓reduceDIte]
    by_cases hj1 : j.val ≤ 2 ^ k
    · have hj1' : j.val ≤ (2 ^ k - 1) + 1 := by omega
      simp only [hj1', ↓reduceDIte]
      by_cases h00 : i.val = 0 ∧ j.val = 0
      · have hij : i = j := Fin.ext (by omega)
        rw [perturb_00 _ _ _ _ _ _ _ (by dsimp only; exact h00.1) (by dsimp only; exact h00.2),
            perturb_00 _ _ _ _ _ _ _ (by dsimp only; exact h00.1) (by dsimp only; exact h00.2)]
        simp only [hij, h00.2, ↓reduceIte, add_zero]
        unfold M castPortal fenwickUQLap rsub
        simp only [↓reduceIte]
        rw [CRing.add_assoc, CRing.add_comm eᵣ, ← CRing.add_assoc]
      · by_cases h0L : i.val = 0 ∧ j.val = 2 ^ k
        · have hne : i ≠ j := fin_ne (by omega)
          rw [perturb_0L _ _ _ _ _ _ _ (by dsimp only; exact h0L.1) (by dsimp only; omega),
              perturb_0L _ _ _ _ _ _ _ (by dsimp only; exact h0L.1) (by dsimp only; omega)]
          simp only [hne, ↓reduceIte, CRing.zero_add, neg_add]
          unfold M castPortal fenwickUQLap rsub
          have hne' : (⟨i.val, by omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val, by omega⟩ := fin_ne (by dsimp only; omega)
          simp only [hne', ↓reduceIte, CRing.zero_add]
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
              perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          unfold M castPortal fenwickUQLap rsub
          by_cases hij : i = j
          · subst hij
            have hi0 : i.val ≠ 0 := fun h => h00 ⟨h, h⟩
            simp only [hi0, ↓reduceIte, add_zero]
          · have hne' : (⟨i.val, by omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val, by omega⟩ :=
              fin_ne (fun h => hij (Fin.ext (by simp at h; exact h)))
            simp only [hij, hne', ↓reduceIte]
    · have hj1' : ¬ (j.val ≤ (2 ^ k - 1) + 1) := by omega
      have hne : i ≠ j := fin_ne (by omega)
      simp only [hj1', hne, ↓reduceDIte, ↓reduceIte, neg_zero, add_zero]
  · by_cases hi2 : i.val = 2 ^ k
    · have hi1' : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
      have hi2' : i.val = (2 ^ k - 1) + 1 := by omega
      simp only [dite_eq_right hi1, dite_eq_right hi1', dite_eq_left hi2, dite_eq_left hi2']
      by_cases hj1 : j.val < 2 ^ k
      · have hj1' : j.val < (2 ^ k - 1) + 1 := by omega
        have hne : i ≠ j := fin_ne (by omega)
        have hne' : (⟨(2 ^ k - 1) + 1, by omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val, by omega⟩ := fin_ne (by dsimp only; omega)
        simp only [hj1', hne, ↓reduceDIte, ↓reduceIte, CRing.zero_add]
        by_cases hj0 : j.val = 0
        · rw [perturb_L0 _ _ _ _ _ _ _ rfl (by dsimp only; exact hj0),
              perturb_L0 _ _ _ _ _ _ _ rfl (by dsimp only; exact hj0), neg_add]
          unfold M castPortal fenwickUQLap rsub
          simp only [hne', ↓reduceIte, CRing.zero_add]
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
              perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          unfold M castPortal fenwickUQLap rsub
          simp only [hne', ↓reduceIte, CRing.zero_add]
      · by_cases hj2 : j.val = 2 ^ k
        · have hj1' : ¬ (j.val < (2 ^ k - 1) + 1) := by omega
          have hj2' : j.val = (2 ^ k - 1) + 1 := by omega
          have hij : i = j := Fin.ext (by omega)
          simp only [dite_eq_right hj1', dite_eq_left hj2', hij, ↓reduceIte, add_zero]
          rw [perturb_LL _ _ _ _ _ _ _ rfl rfl,
              perturb_00 _ _ _ _ _ _ _ rfl rfl,
              perturb_LL _ _ _ _ _ _ _ rfl rfl,
              perturb_00 _ _ _ _ _ _ _ rfl rfl, add_zero, add_zero]
          unfold M castPortal fenwickUQLap rsub
          simp only [↓reduceIte, neg_add]
          have hidx : (⟨(2 ^ k - 1) + 1, by omega⟩ : Fin (2 ^ k + 1)) = ⟨2 ^ k, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [hidx]
          let d1 := fenwickUQDeg (R := R) k ⟨2 ^ k, by omega⟩
          let d2 := fenwickUQDeg (R := R) k ⟨0, by omega⟩
          let a1 := fenwickUQAdj (R := R) k eᵣ ⟨2 ^ k, by omega⟩ ⟨2 ^ k, by omega⟩
          let a2 := fenwickUQAdj (R := R) k eᵣ ⟨0, by omega⟩ ⟨0, by omega⟩
          change ((d1 +ᵣ eᵣ) +ᵣ (d2 +ᵣ eᵣ)) +ᵣ ((-ᵣa1) +ᵣ (-ᵣa2)) =
                 ((d1 +ᵣ (-ᵣa1)) +ᵣ eᵣ) +ᵣ ((d2 +ᵣ (-ᵣa2)) +ᵣ eᵣ)
          simp only [CRing.add_assoc]
          apply congrArg (CRing.add d1)
          rw [add_left_comm (-ᵣa1) eᵣ]
          apply congrArg (CRing.add eᵣ)
          rw [add_left_comm eᵣ (-ᵣa1), add_left_comm d2 (-ᵣa1)]
          apply congrArg (CRing.add (-ᵣa1))
          apply congrArg (CRing.add d2)
          exact CRing.add_comm eᵣ (-ᵣa2)
        · have hj1' : ¬ (j.val < (2 ^ k - 1) + 1) := by omega
          have hj2' : ¬ (j.val = (2 ^ k - 1) + 1) := by omega
          have hne : i ≠ j := fin_ne (by omega)
          have hne' : (⟨0, by omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val - ((2 ^ k - 1) + 1), by omega⟩ :=
            fin_ne (by dsimp only; omega)
          simp only [dite_eq_right hj1', dite_eq_right hj2', hne, ↓reduceIte, CRing.zero_add]
          by_cases hjend : j.val = 2 ^ (k + 1)
          · rw [perturb_0L _ _ _ _ _ _ _ rfl (by dsimp only; omega),
                perturb_0L _ _ _ _ _ _ _ rfl (by dsimp only; omega), neg_add]
            unfold M castPortal fenwickUQLap rsub
            simp only [hne', ↓reduceIte, CRing.zero_add]
          · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
                perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
            unfold M castPortal fenwickUQLap rsub
            simp only [hne', ↓reduceIte, CRing.zero_add]
    · have hi1' : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
      have hi2' : ¬ (i.val = (2 ^ k - 1) + 1) := by omega
      simp only [dite_eq_right hi1, dite_eq_right hi1', dite_eq_right hi2, dite_eq_right hi2']
      by_cases hj1 : j.val < 2 ^ k
      · have hj1' : j.val < (2 ^ k - 1) + 1 := by omega
        have hne : i ≠ j := fin_ne (by omega)
        simp only [hj1', hne, ↓reduceDIte, ↓reduceIte, neg_zero, add_zero]
      · have hj1' : ¬ (j.val < (2 ^ k - 1) + 1) := by omega
        simp only [hj1', ↓reduceDIte]
        have hr : (⟨i.val - ((2 ^ k - 1) + 1), by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) =
                  ⟨i.val - 2 ^ k, by have := i.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
        by_cases hLL : i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ (k + 1)
        · have hij : i = j := Fin.ext (by omega)
          rw [perturb_LL _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega),
              perturb_LL _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega)]
          have hrj : (⟨j.val - ((2 ^ k - 1) + 1), by have := j.isLt; omega⟩ : Fin (2 ^ k + 1)) =
                    ⟨i.val - 2 ^ k, by have := i.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
          simp only [ite_eq_left hij, ite_eq_left hLL.1, add_zero]
          unfold M castPortal fenwickUQLap rsub
          simp only [hr, hrj, ↓reduceIte]
          rw [CRing.add_assoc, CRing.add_comm eᵣ, ← CRing.add_assoc]
        · by_cases hL0 : i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ k
          · have hne : i ≠ j := fin_ne (by omega)
            rw [perturb_L0 _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega),
                perturb_L0 _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega)]
            simp only [hne, ↓reduceIte, CRing.zero_add, neg_add]
            unfold M castPortal fenwickUQLap rsub
            have hne' : (⟨i.val - ((2 ^ k - 1) + 1), by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) ≠
                        ⟨j.val - ((2 ^ k - 1) + 1), by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
            simp only [hne', ↓reduceIte, CRing.zero_add]
          · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
                perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
            unfold M castPortal fenwickUQLap rsub
            by_cases hij : i = j
            · subst hij
              have hiend : i.val ≠ 2 ^ (k + 1) := fun h => hLL ⟨h, h⟩
              simp only [hiend, ↓reduceIte, add_zero, hr]
            · have hne' : (⟨i.val - ((2 ^ k - 1) + 1), by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) ≠
                          ⟨j.val - ((2 ^ k - 1) + 1), by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
              simp only [hij, hne', ↓reduceIte]

/-- Bridge 3: Characteristic matrix `x I - M` step for ANY matrix family satisfying a 2-portal
`(p, q, q, r, s=0)` recursion! -/
theorem char_step_of_portal_step {n : Nat} (M : Mat (n + 2) R) (p q r x : R) :
    let G := glue (perturb M p q q r) (perturb M p q q r) zᵣ
    let Cx : Mat (n + 2) R := fun i j => (if i = j then x else zᵣ) -ᵣ M i j
    let CG : Mat ((n + n + 1) + 2) R := fun i j => (if i = j then x else zᵣ) -ᵣ G i j
    CG = glue (perturb Cx (-ᵣp) (-ᵣq) (-ᵣq) (-ᵣr)) (perturb Cx (-ᵣp) (-ᵣq) (-ᵣq) (-ᵣr)) (-ᵣx) := by
  intro G Cx CG
  funext i j
  unfold CG G glue rsub
  by_cases hi1 : i.val < n + 1
  · simp only [hi1, ↓reduceDIte]
    by_cases hj1 : j.val ≤ n + 1
    · simp only [hj1, ↓reduceDIte]
      by_cases h00 : i.val = 0 ∧ j.val = 0
      · have hij : i = j := Fin.ext (by omega)
        rw [perturb_00 _ _ _ _ _ _ _ (by dsimp only; exact h00.1) (by dsimp only; exact h00.2),
            perturb_00 _ _ _ _ _ _ _ (by dsimp only; exact h00.1) (by dsimp only; exact h00.2)]
        unfold Cx rsub
        have hij' : (⟨i.val, by omega⟩ : Fin (n + 2)) = ⟨j.val, by omega⟩ := Fin.ext (by dsimp only; omega)
        simp only [hij, ↓reduceIte, neg_add, CRing.add_assoc]
      · by_cases h0L : i.val = 0 ∧ j.val = n + 1
        · have hne : i ≠ j := fin_ne (by omega)
          have hne' : (⟨i.val, by omega⟩ : Fin (n + 2)) ≠ ⟨j.val, by omega⟩ := fin_ne (by dsimp only; omega)
          rw [perturb_0L _ _ _ _ _ _ _ (by dsimp only; exact h0L.1) (by dsimp only; exact h0L.2),
              perturb_0L _ _ _ _ _ _ _ (by dsimp only; exact h0L.1) (by dsimp only; exact h0L.2)]
          unfold Cx rsub
          simp only [hne, hne', ↓reduceIte, CRing.zero_add, neg_add]
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
              perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          unfold Cx rsub
          by_cases hij : i = j
          · subst hij; simp only [↓reduceIte]
          · have hne' : (⟨i.val, by omega⟩ : Fin (n + 2)) ≠ ⟨j.val, by omega⟩ :=
              fin_ne (fun h => hij (Fin.ext (by simp at h; exact h)))
            simp only [hij, hne', ↓reduceIte]
    · have hne : i ≠ j := fin_ne (by omega)
      simp only [hj1, hne, ↓reduceDIte, ↓reduceIte, neg_zero, add_zero]
  · by_cases hi2 : i.val = n + 1
    · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]
      by_cases hj1 : j.val < n + 1
      · have hne : i ≠ j := fin_ne (by omega)
        have hne' : (⟨n + 1, by omega⟩ : Fin (n + 2)) ≠ ⟨j.val, by omega⟩ := fin_ne (by dsimp only; omega)
        simp only [hj1, hne, ↓reduceDIte, ↓reduceIte, CRing.zero_add]
        by_cases hj0 : j.val = 0
        · rw [perturb_L0 _ _ _ _ _ _ _ rfl (by dsimp only; exact hj0),
              perturb_L0 _ _ _ _ _ _ _ rfl (by dsimp only; exact hj0), neg_add]
          unfold Cx rsub; simp only [hne', ↓reduceIte, CRing.zero_add]
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
              perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          unfold Cx rsub; simp only [hne', ↓reduceIte, CRing.zero_add]
      · by_cases hj2 : j.val = n + 1
        · have hij : i = j := Fin.ext (by omega)
          simp only [hj1, ↓reduceDIte]; simp only [hj2, hij, ↓reduceDIte, ↓reduceIte, add_zero]
          rw [perturb_LL _ _ _ _ _ _ _ rfl rfl,
              perturb_00 _ _ _ _ _ _ _ rfl rfl,
              perturb_LL _ _ _ _ _ _ _ rfl rfl,
              perturb_00 _ _ _ _ _ _ _ rfl rfl]
          unfold Cx rsub
          simp only [↓reduceIte, neg_add]
          let m1 := M ⟨n + 1, by omega⟩ ⟨n + 1, by omega⟩
          let m2 := M ⟨0, by omega⟩ ⟨0, by omega⟩
          change x +ᵣ ((-ᵣm1 +ᵣ -ᵣr) +ᵣ (-ᵣm2 +ᵣ -ᵣp)) =
                 (((x +ᵣ -ᵣm1) +ᵣ -ᵣr) +ᵣ ((x +ᵣ -ᵣm2) +ᵣ -ᵣp)) +ᵣ -ᵣx
          simp only [CRing.add_assoc]
          apply congrArg (CRing.add x)
          apply congrArg (CRing.add (-ᵣm1))
          apply congrArg (CRing.add (-ᵣr))
          have hcan : x +ᵣ (-ᵣm2 +ᵣ (-ᵣp +ᵣ -ᵣx)) = -ᵣm2 +ᵣ -ᵣp := by
            rw [CRing.add_comm x, CRing.add_assoc, CRing.add_assoc,
                CRing.add_comm (-ᵣx) x, add_right_neg, add_zero]
          exact hcan.symm
        · have hne : i ≠ j := fin_ne (by omega)
          have hne' : (⟨0, by omega⟩ : Fin (n + 2)) ≠ ⟨j.val - (n + 1), by omega⟩ := fin_ne (by dsimp only; omega)
          simp only [hj1, ↓reduceDIte]; simp only [hj2, hne, ↓reduceDIte, ↓reduceIte, CRing.zero_add]
          by_cases hjL : j.val - (n + 1) = n + 1
          · rw [perturb_0L _ _ _ _ _ _ _ rfl (by dsimp only; exact hjL),
                perturb_0L _ _ _ _ _ _ _ rfl (by dsimp only; exact hjL), neg_add]
            unfold Cx rsub; simp only [hne', ↓reduceIte, CRing.zero_add]
          · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
                perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
            unfold Cx rsub; simp only [hne', ↓reduceIte, CRing.zero_add]
    · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]
      by_cases hj1 : j.val < n + 1
      · have hne : i ≠ j := fin_ne (by omega)
        simp only [hj1, hne, ↓reduceDIte, ↓reduceIte, neg_zero, add_zero]
      · simp only [hj1, ↓reduceDIte]
        by_cases hLL : i.val - (n + 1) = n + 1 ∧ j.val - (n + 1) = n + 1
        · have hij : i = j := Fin.ext (by omega)
          have hij' : (⟨i.val - (n + 1), by omega⟩ : Fin (n + 2)) = ⟨j.val - (n + 1), by omega⟩ :=
            Fin.ext (by dsimp only; omega)
          rw [perturb_LL _ _ _ _ _ _ _ (by dsimp only; exact hLL.1) (by dsimp only; exact hLL.2),
              perturb_LL _ _ _ _ _ _ _ (by dsimp only; exact hLL.1) (by dsimp only; exact hLL.2)]
          unfold Cx rsub
          simp only [hij, ↓reduceIte, neg_add, CRing.add_assoc]
        · by_cases hL0 : i.val - (n + 1) = n + 1 ∧ j.val - (n + 1) = 0
          · have hne : i ≠ j := fin_ne (by omega)
            have hne' : (⟨i.val - (n + 1), by omega⟩ : Fin (n + 2)) ≠ ⟨j.val - (n + 1), by omega⟩ :=
              fin_ne (by dsimp only; omega)
            rw [perturb_L0 _ _ _ _ _ _ _ (by dsimp only; exact hL0.1) (by dsimp only; exact hL0.2),
                perturb_L0 _ _ _ _ _ _ _ (by dsimp only; exact hL0.1) (by dsimp only; exact hL0.2)]
            unfold Cx rsub
            simp only [hne, hne', ↓reduceIte, CRing.zero_add, neg_add]
          · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
                perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
            unfold Cx rsub
            by_cases hij : i = j
            · subst hij; simp only [↓reduceIte]
            · have hne' : (⟨i.val - (n + 1), by omega⟩ : Fin (n + 2)) ≠ ⟨j.val - (n + 1), by omega⟩ :=
                fin_ne (by dsimp only; omega)
              simp only [hij, hne', ↓reduceIte]

/-! ### Bitwise Fenwick Truncated Matrix `B_n` on `{1, ..., n}` & Even/Odd Bridge -/

theorem fenwickB_symm (n : Nat) (i j : Fin n) : fenwickB (R := R) n i j = fenwickB n j i := by
  unfold fenwickB; rw [fenwickEdge_symm]

/-- Bridge 4: For EVERY `m : Nat`, the bitwise `2m × 2m` Fenwick matrix `fenwickB (2 * m)`
is ENTRYWISE EQUAL to `interleave (fenwickB m)`! -/
theorem fenwickB_even_eq_interleave (m : Nat) :
    fenwickB (R := R) (2 * m) = interleave (fenwickB m) := by
  funext i j
  unfold fenwickB interleave bidiagU
  by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0
  · -- Both 1-based vertices `i+1` and `j+1` are ODD: no edge!
    simp only [hi, hj, ↓reduceIte]
    have hno : fenwickEdge (2 * m) (i.val + 1) (j.val + 1) = false := by
      unfold fenwickEdge
      simp only [decide_eq_false_iff_not, not_or]
      constructor
      · intro ⟨_, _, hdir⟩
        rw [lowbit_odd (by omega)] at hdir; omega
      · intro ⟨_, _, hdir⟩
        rw [lowbit_odd (by omega)] at hdir; omega
    simp [hno]
  · -- `i+1` ODD, `j+1` EVEN: edge iff `j/2 = i/2 ∨ j/2 + 1 = i/2`!
    simp only [hi, hj, ↓reduceIte]
    have hiff : fenwickEdge (2 * m) (i.val + 1) (j.val + 1) = true ↔
                (j.val / 2 = i.val / 2 ∨ j.val / 2 + 1 = i.val / 2) := by
      unfold fenwickEdge
      simp only [decide_eq_true_eq]
      constructor
      · intro h
        rcases h with ⟨_, _, hdir⟩ | ⟨hj0, _, hdir⟩
        · rw [lowbit_odd (by omega)] at hdir; omega
        · -- `j+1` is even, so `lowbit(j+1)` is even, hence `(j+1) ± lowbit(j+1)` is even ≠ `i+1`!
          have he : (j.val + 1) % 2 = 0 := by omega
          rw [lowbit_even (by omega) he] at hdir; omega
      · intro hor
        left
        have hi_lt : i.val + 1 < 2 * m := by have := i.isLt; omega
        refine ⟨by omega, hi_lt, ?_⟩
        rw [lowbit_odd (by omega)]; omega
    by_cases hcond : j.val / 2 = i.val / 2 ∨ j.val / 2 + 1 = i.val / 2
    · have ht := hiff.mpr hcond
      simp [ht, hcond]
    · have hf : fenwickEdge (2 * m) (i.val + 1) (j.val + 1) = false := by
        cases h : fenwickEdge (2 * m) (i.val + 1) (j.val + 1)
        · rfl
        · exfalso; exact hcond (hiff.mp h)
      simp [hf, hcond]
  · -- `i+1` EVEN, `j+1` ODD: symmetric!
    simp only [hi, hj, ↓reduceIte]
    rw [fenwickEdge_symm]
    have hiff : fenwickEdge (2 * m) (j.val + 1) (i.val + 1) = true ↔
                (i.val / 2 = j.val / 2 ∨ i.val / 2 + 1 = j.val / 2) := by
      unfold fenwickEdge
      simp only [decide_eq_true_eq]
      constructor
      · intro h
        rcases h with ⟨_, _, hdir⟩ | ⟨hi0, _, hdir⟩
        · rw [lowbit_odd (by omega)] at hdir; omega
        · have he : (i.val + 1) % 2 = 0 := by omega
          rw [lowbit_even (by omega) he] at hdir; omega
      · intro hor
        left
        have hj_lt : j.val + 1 < 2 * m := by have := j.isLt; omega
        refine ⟨by omega, hj_lt, ?_⟩
        rw [lowbit_odd (by omega)]; omega
    by_cases hcond : i.val / 2 = j.val / 2 ∨ i.val / 2 + 1 = j.val / 2
    · have ht := hiff.mpr hcond
      simp [ht, hcond]
    · have hf : fenwickEdge (2 * m) (j.val + 1) (i.val + 1) = false := by
        cases h : fenwickEdge (2 * m) (j.val + 1) (i.val + 1)
        · rfl
        · exfalso; exact hcond (hiff.mp h)
      simp [hf, hcond]
  · -- Both `i+1` and `j+1` are EVEN: `i+1 = 2(i/2 + 1)`, `j+1 = 2(j/2 + 1)`!
    simp only [hi, hj, ↓reduceIte]
    have hi2 : i.val + 1 = 2 * (i.val / 2 + 1) := by omega
    have hj2 : j.val + 1 = 2 * (j.val / 2 + 1) := by omega
    have hfe : fenwickEdge (2 * m) (i.val + 1) (j.val + 1) =
               fenwickEdge m (i.val / 2 + 1) (j.val / 2 + 1) := by
      rw [hi2, hj2]
      unfold fenwickEdge
      rw [lowbit_two_mul, lowbit_two_mul]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro h; rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · left; exact ⟨by omega, by omega, by omega⟩
        · right; exact ⟨by omega, by omega, by omega⟩
      · intro h; rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · left; exact ⟨by omega, by omega, by omega⟩
        · right; exact ⟨by omega, by omega, by omega⟩
    rw [hfe]

/-! ### Signless Laplacian Bridge (`Q(G_k) = D(G_k) + A(G_k)`) -/

theorem fenwickUQSignless_step (k : Nat) (hk : 1 ≤ k) :
    let M := castPortal hk (fenwickUQSignless (R := R) k)
    let G := glue (perturb M eᵣ eᵣ eᵣ eᵣ) (perturb M eᵣ eᵣ eᵣ eᵣ) zᵣ
    ∀ (i j : Fin (2 ^ (k + 1) + 1)),
      fenwickUQSignless (R := R) (k + 1) i j =
      G ⟨i.val, by have := i.isLt; have := glue_dim_eq hk; omega⟩
        ⟨j.val, by have := j.isLt; have := glue_dim_eq hk; omega⟩ := by
  have h2k := two_le_two_pow hk
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  intro M G i j
  have hA := fenwickUQAdj_step (R := R) k hk eᵣ i j
  have hD := fenwickUQDeg_step (R := R) k hk i
  unfold fenwickUQSignless
  rw [hA, hD]
  unfold G glue
  by_cases hi1 : i.val < 2 ^ k
  · have hi1' : i.val < (2 ^ k - 1) + 1 := by omega
    simp only [hi1, hi1', ↓reduceDIte]
    by_cases hj1 : j.val ≤ 2 ^ k
    · have hj1' : j.val ≤ (2 ^ k - 1) + 1 := by omega
      simp only [hj1', ↓reduceDIte]
      by_cases h00 : i.val = 0 ∧ j.val = 0
      · have hij : i = j := Fin.ext (by omega)
        rw [perturb_00 _ _ _ _ _ _ _ (by dsimp only; exact h00.1) (by dsimp only; exact h00.2),
            perturb_00 _ _ _ _ _ _ _ (by dsimp only; exact h00.1) (by dsimp only; exact h00.2)]
        simp only [hij, h00.2, ↓reduceIte, add_zero]
        unfold M castPortal fenwickUQSignless
        simp only [↓reduceIte]
        rw [CRing.add_assoc, CRing.add_comm eᵣ, ← CRing.add_assoc]
      · by_cases h0L : i.val = 0 ∧ j.val = 2 ^ k
        · have hne : i ≠ j := fin_ne (by omega)
          rw [perturb_0L _ _ _ _ _ _ _ (by dsimp only; exact h0L.1) (by dsimp only; omega),
              perturb_0L _ _ _ _ _ _ _ (by dsimp only; exact h0L.1) (by dsimp only; omega)]
          simp only [hne, ↓reduceIte, CRing.zero_add]
          unfold M castPortal fenwickUQSignless
          have hne' : (⟨i.val, by omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val, by omega⟩ := fin_ne (by dsimp only; omega)
          simp only [hne', ↓reduceIte, CRing.zero_add]
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
              perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          unfold M castPortal fenwickUQSignless
          by_cases hij : i = j
          · subst hij
            have hi0 : i.val ≠ 0 := fun h => h00 ⟨h, h⟩
            simp only [hi0, ↓reduceIte, add_zero]
          · have hne' : (⟨i.val, by omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val, by omega⟩ :=
              fin_ne (fun h => hij (Fin.ext (by dsimp only at h; exact h)))
            simp only [hij, hne', ↓reduceIte]
    · have hj1' : ¬ (j.val ≤ (2 ^ k - 1) + 1) := by omega
      have hne : i ≠ j := fin_ne (by omega)
      simp only [hj1', hne, ↓reduceDIte, ↓reduceIte, add_zero]
  · by_cases hi2 : i.val = 2 ^ k
    · have hi1' : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
      have hi2' : i.val = (2 ^ k - 1) + 1 := by omega
      simp only [dite_eq_right hi1, dite_eq_right hi1', dite_eq_left hi2, dite_eq_left hi2']
      by_cases hj1 : j.val < 2 ^ k
      · have hj1' : j.val < (2 ^ k - 1) + 1 := by omega
        have hne : i ≠ j := fin_ne (by omega)
        have hne' : (⟨(2 ^ k - 1) + 1, by omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val, by omega⟩ := fin_ne (by dsimp only; omega)
        simp only [hj1', hne, ↓reduceDIte, ↓reduceIte, CRing.zero_add]
        by_cases hj0 : j.val = 0
        · rw [perturb_L0 _ _ _ _ _ _ _ rfl (by dsimp only; exact hj0),
              perturb_L0 _ _ _ _ _ _ _ rfl (by dsimp only; exact hj0)]
          unfold M castPortal fenwickUQSignless
          simp only [hne', ↓reduceIte, CRing.zero_add]
        · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
              perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
          unfold M castPortal fenwickUQSignless
          simp only [hne', ↓reduceIte, CRing.zero_add]
      · by_cases hj2 : j.val = 2 ^ k
        · have hj1' : ¬ (j.val < (2 ^ k - 1) + 1) := by omega
          have hj2' : j.val = (2 ^ k - 1) + 1 := by omega
          have hij : i = j := Fin.ext (by omega)
          simp only [dite_eq_right hj1', dite_eq_left hj2', hij, ↓reduceIte, add_zero]
          rw [perturb_LL _ _ _ _ _ _ _ rfl rfl,
              perturb_00 _ _ _ _ _ _ _ rfl rfl,
              perturb_LL _ _ _ _ _ _ _ rfl rfl,
              perturb_00 _ _ _ _ _ _ _ rfl rfl, add_zero, add_zero]
          unfold M castPortal fenwickUQSignless
          simp only [↓reduceIte]
          have hidx : (⟨(2 ^ k - 1) + 1, by omega⟩ : Fin (2 ^ k + 1)) = ⟨2 ^ k, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [hidx]
          let d1 := fenwickUQDeg (R := R) k ⟨2 ^ k, by omega⟩
          let d2 := fenwickUQDeg (R := R) k ⟨0, by omega⟩
          let a1 := fenwickUQAdj (R := R) k eᵣ ⟨2 ^ k, by omega⟩ ⟨2 ^ k, by omega⟩
          let a2 := fenwickUQAdj (R := R) k eᵣ ⟨0, by omega⟩ ⟨0, by omega⟩
          change ((d1 +ᵣ eᵣ) +ᵣ (d2 +ᵣ eᵣ)) +ᵣ (a1 +ᵣ a2) =
                 ((d1 +ᵣ a1) +ᵣ eᵣ) +ᵣ ((d2 +ᵣ a2) +ᵣ eᵣ)
          simp only [CRing.add_assoc]
          apply congrArg (CRing.add d1)
          rw [add_left_comm a1 eᵣ]
          apply congrArg (CRing.add eᵣ)
          rw [add_left_comm eᵣ a1, add_left_comm d2 a1]
          apply congrArg (CRing.add a1)
          apply congrArg (CRing.add d2)
          exact CRing.add_comm eᵣ a2
        · have hj1' : ¬ (j.val < (2 ^ k - 1) + 1) := by omega
          have hj2' : ¬ (j.val = (2 ^ k - 1) + 1) := by omega
          have hne : i ≠ j := fin_ne (by omega)
          have hne' : (⟨0, by omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val - ((2 ^ k - 1) + 1), by omega⟩ :=
            fin_ne (by dsimp only; omega)
          simp only [dite_eq_right hj1', dite_eq_right hj2', hne, ↓reduceIte, CRing.zero_add]
          by_cases hjend : j.val = 2 ^ (k + 1)
          · rw [perturb_0L _ _ _ _ _ _ _ rfl (by dsimp only; omega),
                perturb_0L _ _ _ _ _ _ _ rfl (by dsimp only; omega)]
            unfold M castPortal fenwickUQSignless
            simp only [hne', ↓reduceIte, CRing.zero_add]
          · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
                perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
            unfold M castPortal fenwickUQSignless
            simp only [hne', ↓reduceIte, CRing.zero_add]
    · have hi1' : ¬ (i.val < (2 ^ k - 1) + 1) := by omega
      have hi2' : ¬ (i.val = (2 ^ k - 1) + 1) := by omega
      simp only [dite_eq_right hi1, dite_eq_right hi1', dite_eq_right hi2, dite_eq_right hi2']
      by_cases hj1 : j.val < 2 ^ k
      · have hj1' : j.val < (2 ^ k - 1) + 1 := by omega
        have hne : i ≠ j := fin_ne (by omega)
        simp only [hj1', hne, ↓reduceDIte, ↓reduceIte, add_zero]
      · have hj1' : ¬ (j.val < (2 ^ k - 1) + 1) := by omega
        simp only [hj1', ↓reduceDIte]
        have hr : (⟨i.val - ((2 ^ k - 1) + 1), by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) =
                  ⟨i.val - 2 ^ k, by have := i.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
        by_cases hLL : i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ (k + 1)
        · have hij : i = j := Fin.ext (by omega)
          rw [perturb_LL _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega),
              perturb_LL _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega)]
          have hrj : (⟨j.val - ((2 ^ k - 1) + 1), by have := j.isLt; omega⟩ : Fin (2 ^ k + 1)) =
                    ⟨i.val - 2 ^ k, by have := i.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
          simp only [ite_eq_left hij, ite_eq_left hLL.1, add_zero]
          unfold M castPortal fenwickUQSignless
          simp only [hr, hrj, ↓reduceIte]
          rw [CRing.add_assoc, CRing.add_comm eᵣ, ← CRing.add_assoc]
        · by_cases hL0 : i.val = 2 ^ (k + 1) ∧ j.val = 2 ^ k
          · have hne : i ≠ j := fin_ne (by omega)
            rw [perturb_L0 _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega),
                perturb_L0 _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega)]
            simp only [hne, ↓reduceIte, CRing.zero_add]
            unfold M castPortal fenwickUQSignless
            have hne' : (⟨i.val - ((2 ^ k - 1) + 1), by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) ≠
                        ⟨j.val - ((2 ^ k - 1) + 1), by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
            simp only [hne', ↓reduceIte, CRing.zero_add]
          · rw [perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega),
                perturb_other _ _ _ _ _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)]
            unfold M castPortal fenwickUQSignless
            by_cases hij : i = j
            · subst hij
              have hiend : i.val ≠ 2 ^ (k + 1) := fun h => hLL ⟨h, h⟩
              simp only [hiend, ↓reduceIte, add_zero, hr]
            · have hne' : (⟨i.val - ((2 ^ k - 1) + 1), by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) ≠
                          ⟨j.val - ((2 ^ k - 1) + 1), by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
              simp only [hij, hne', ↓reduceIte]



end BitwiseMatrices
end BitwiseBridges
section MainTheorems
section SmallDet
variable {R : Type} [CRing R]

theorem rnat_int (n : Nat) : rnat (R := Int) n = (n : Int) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold rnat
    rw [ih]
    change (k : Int) + 1 = ((k + 1 : Nat) : Int)
    omega

theorem det_fin0 (M : Mat 0 R) : det M = eᵣ := rfl

theorem det_fin1 (M : Mat 1 R) : det M = M ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  unfold det
  rw [sumFin_succ, sumFin_zero, add_zero]
  have hs : rsign (R := R) 0 = eᵣ := rfl
  have hd : det (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) = eᵣ := rfl
  rw [hs, hd, CRing.one_mul, mul_one]

theorem det_fin2 (M : Mat 2 R) :
    det M = M ⟨0, by omega⟩ ⟨0, by omega⟩ *ᵣ M ⟨1, by omega⟩ ⟨1, by omega⟩ -ᵣ
            M ⟨0, by omega⟩ ⟨1, by omega⟩ *ᵣ M ⟨1, by omega⟩ ⟨0, by omega⟩ := by
  unfold det
  rw [sumFin_succ, sumFin_succ, sumFin_zero, add_zero]
  have hs0 : rsign (R := R) 0 = eᵣ := rfl
  have hs1 : rsign (R := R) 1 = -ᵣeᵣ := rfl
  simp only [Fin.succ]
  rw [hs0, hs1, CRing.one_mul, neg_mul, CRing.one_mul]
  have h0 : det (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) = M ⟨1, by omega⟩ ⟨1, by omega⟩ := by
    rw [det_fin1]; rfl
  have h1 : det (minor M ⟨0, by omega⟩ ⟨1, by omega⟩) = M ⟨1, by omega⟩ ⟨0, by omega⟩ := by
    rw [det_fin1]; rfl
  change M ⟨0, by omega⟩ ⟨0, by omega⟩ *ᵣ det (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) +ᵣ
         (-ᵣ(M ⟨0, by omega⟩ ⟨1, by omega⟩)) *ᵣ det (minor M ⟨0, by omega⟩ ⟨1, by omega⟩) = _
  rw [h0, h1, neg_mul]
  rfl

theorem det_fin3 (M : Mat 3 R) :
    det M =
      M ⟨0, by omega⟩ ⟨0, by omega⟩ *ᵣ
        (M ⟨1, by omega⟩ ⟨1, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨2, by omega⟩ -ᵣ
         M ⟨1, by omega⟩ ⟨2, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨1, by omega⟩) -ᵣ
      M ⟨0, by omega⟩ ⟨1, by omega⟩ *ᵣ
        (M ⟨1, by omega⟩ ⟨0, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨2, by omega⟩ -ᵣ
         M ⟨1, by omega⟩ ⟨2, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨0, by omega⟩) +ᵣ
      M ⟨0, by omega⟩ ⟨2, by omega⟩ *ᵣ
        (M ⟨1, by omega⟩ ⟨0, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨1, by omega⟩ -ᵣ
         M ⟨1, by omega⟩ ⟨1, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨0, by omega⟩) := by
  conv => lhs; unfold det
  rw [sumFin_succ, sumFin_succ, sumFin_succ, sumFin_zero, add_zero]
  have hs0 : rsign (R := R) 0 = eᵣ := rfl
  have hs1 : rsign (R := R) 1 = -ᵣeᵣ := rfl
  have hs2 : rsign (R := R) 2 = eᵣ := rfl
  have h0 : det (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) =
      M ⟨1, by omega⟩ ⟨1, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨2, by omega⟩ -ᵣ
      M ⟨1, by omega⟩ ⟨2, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨1, by omega⟩ := by
    rw [det_fin2]; rfl
  have h1 : det (minor M ⟨0, by omega⟩ ⟨1, by omega⟩) =
      M ⟨1, by omega⟩ ⟨0, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨2, by omega⟩ -ᵣ
      M ⟨1, by omega⟩ ⟨2, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨0, by omega⟩ := by
    rw [det_fin2]; rfl
  have h2 : det (minor M ⟨0, by omega⟩ ⟨2, by omega⟩) =
      M ⟨1, by omega⟩ ⟨0, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨1, by omega⟩ -ᵣ
      M ⟨1, by omega⟩ ⟨1, by omega⟩ *ᵣ M ⟨2, by omega⟩ ⟨0, by omega⟩ := by
    rw [det_fin2]; rfl
  change rsign 0 *ᵣ M ⟨0, by omega⟩ ⟨0, by omega⟩ *ᵣ det (minor M ⟨0, by omega⟩ ⟨0, by omega⟩) +ᵣ
         (rsign 1 *ᵣ M ⟨0, by omega⟩ ⟨1, by omega⟩ *ᵣ det (minor M ⟨0, by omega⟩ ⟨1, by omega⟩) +ᵣ
          rsign 2 *ᵣ M ⟨0, by omega⟩ ⟨2, by omega⟩ *ᵣ det (minor M ⟨0, by omega⟩ ⟨2, by omega⟩)) = _
  rw [hs0, hs1, hs2, CRing.one_mul, CRing.one_mul, neg_mul, CRing.one_mul, neg_mul, h0, h1, h2]
  rw [← CRing.add_assoc]
  rfl

theorem portalTuple_eq_of_dim_eq {m n : Nat} (hm : m = n)
    (M : Mat (m + 2) R) (N : Mat (n + 2) R)
    (heq : ∀ (i j : Fin (m + 2)), M i j = N ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) :
    portalTuple M = portalTuple N := by
  subst hm
  have hMN : M = N := by funext i j; exact heq i j
  rw [hMN]

theorem det_eq_of_dim_eq {m n : Nat} (hm : m = n)
    (M : Mat m R) (N : Mat n R)
    (heq : ∀ (i j : Fin m), M i j = N ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) :
    det M = det N := by
  subst hm
  have hMN : M = N := by funext i j; exact heq i j
  rw [hMN]

theorem minor00_castPortal {k : Nat} (hk : 1 ≤ k) (M : Mat (2 ^ k + 1) R) :
    det (minor (castPortal hk M) ⟨0, by omega⟩ ⟨0, by omega⟩) =
    det (minor M ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩) := by
  have h2k := two_le_two_pow hk
  apply det_eq_of_dim_eq (by omega)
  intro i j; unfold minor castPortal; rfl

/-! ### Step Lemmas in `portalTuple` Form (Plugging Section 7 Bridges into Section 5) -/

theorem portalTuple_fenwickUQAdj_succ (k : Nat) (hk : 1 ≤ k) (c : R) :
    portalTuple (castPortal (by omega : 1 ≤ k + 1) (fenwickUQAdj (k + 1) c)) =
    stepGlue (stepPerturb (portalTuple (castPortal hk (fenwickUQAdj k c))) zᵣ c c zᵣ)
             (stepPerturb (portalTuple (castPortal hk (fenwickUQAdj k c))) zᵣ c c zᵣ) zᵣ := by
  have h2k := two_le_two_pow hk
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [← portalTuple_perturb, ← portalTuple_glue]
  apply portalTuple_eq_of_dim_eq (by omega)
  intro i j
  unfold castPortal
  exact fenwickUQAdj_step k hk c ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩

theorem portalTuple_fenwickUQLap_succ (k : Nat) (hk : 1 ≤ k) :
    portalTuple (castPortal (by omega : 1 ≤ k + 1) (fenwickUQLap (R := R) (k + 1))) =
    stepGlue (stepPerturb (portalTuple (castPortal hk (fenwickUQLap (R := R) k))) eᵣ (-ᵣeᵣ) (-ᵣeᵣ) eᵣ)
             (stepPerturb (portalTuple (castPortal hk (fenwickUQLap (R := R) k))) eᵣ (-ᵣeᵣ) (-ᵣeᵣ) eᵣ) zᵣ := by
  have h2k := two_le_two_pow hk
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [← portalTuple_perturb, ← portalTuple_glue]
  apply portalTuple_eq_of_dim_eq (by omega)
  intro i j
  unfold castPortal
  exact fenwickUQLap_step k hk ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩

theorem portalTuple_fenwickUQSignless_succ (k : Nat) (hk : 1 ≤ k) :
    portalTuple (castPortal (by omega : 1 ≤ k + 1) (fenwickUQSignless (R := R) (k + 1))) =
    stepGlue (stepPerturb (portalTuple (castPortal hk (fenwickUQSignless (R := R) k))) eᵣ eᵣ eᵣ eᵣ)
             (stepPerturb (portalTuple (castPortal hk (fenwickUQSignless (R := R) k))) eᵣ eᵣ eᵣ eᵣ) zᵣ := by
  have h2k := two_le_two_pow hk
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [← portalTuple_perturb, ← portalTuple_glue]
  apply portalTuple_eq_of_dim_eq (by omega)
  intro i j
  unfold castPortal
  exact fenwickUQSignless_step k hk ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩

theorem portalTuple_fenwickUQChar_succ (k : Nat) (hk : 1 ≤ k) (x : R) :
    portalTuple (castPortal (by omega : 1 ≤ k + 1) (fenwickUQChar (k + 1) x)) =
    stepGlue (stepPerturb (portalTuple (castPortal hk (fenwickUQChar k x))) zᵣ (-ᵣeᵣ) (-ᵣeᵣ) zᵣ)
             (stepPerturb (portalTuple (castPortal hk (fenwickUQChar k x))) zᵣ (-ᵣeᵣ) (-ᵣeᵣ) zᵣ) (-ᵣx) := by
  have h2k := two_le_two_pow hk
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hcz : (-ᵣ(zᵣ : R)) = zᵣ := neg_zero
  have hcast : castPortal hk (fenwickUQChar (R := R) k x) =
      fun i j => (if i = j then x else zᵣ) -ᵣ castPortal hk (fenwickUQAdj (R := R) k eᵣ) i j := by
    funext i j; unfold castPortal fenwickUQChar
    by_cases hij : i = j
    · subst hij; simp only [↓reduceIte]
    · have hne : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ :=
        fin_ne (fun h => hij (Fin.ext (by dsimp only at h; exact h)))
      simp only [hij, hne, ↓reduceIte]
  have hstep' := char_step_of_portal_step (M := castPortal hk (fenwickUQAdj (R := R) k eᵣ)) (p := zᵣ) (q := eᵣ) (r := zᵣ) (x := x)
  simp only [neg_zero] at hstep'
  rw [hcast, ← portalTuple_perturb, ← portalTuple_glue, ← hstep']
  apply portalTuple_eq_of_dim_eq (by omega)
  intro i j
  unfold castPortal fenwickUQChar
  dsimp only
  have hA := fenwickUQAdj_step (R := R) k hk eᵣ ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩
  rw [hA]
  have hiff : ((⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (k + 1) + 1)) =
                ⟨j.val, by have := j.isLt; omega⟩) ↔
              ((⟨i.val, by have := i.isLt; omega⟩ : Fin ((2 ^ k - 1) + (2 ^ k - 1) + 1 + 2)) =
                ⟨j.val, by have := j.isLt; omega⟩) := by
    constructor <;> (intro h; exact Fin.ext (by injection h))
  by_cases hij : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (k + 1) + 1)) = ⟨j.val, by have := j.isLt; omega⟩
  · have hij' := hiff.mp hij
    simp only [ite_eq_left hij, ite_eq_left hij']; rfl
  · have hij' : ¬ ((⟨i.val, by have := i.isLt; omega⟩ : Fin ((2 ^ k - 1) + (2 ^ k - 1) + 1 + 2)) =
                    ⟨j.val, by have := j.isLt; omega⟩) := fun h => hij (hiff.mpr h)
    simp only [ite_eq_right hij, ite_eq_right hij']; rfl

theorem portalTuple_fenwickUQLapChar_succ (k : Nat) (hk : 1 ≤ k) (x : R) :
    portalTuple (castPortal (by omega : 1 ≤ k + 1) (fenwickUQLapChar (k + 1) x)) =
    stepGlue (stepPerturb (portalTuple (castPortal hk (fenwickUQLapChar k x))) (-ᵣeᵣ) eᵣ eᵣ (-ᵣeᵣ))
             (stepPerturb (portalTuple (castPortal hk (fenwickUQLapChar k x))) (-ᵣeᵣ) eᵣ eᵣ (-ᵣeᵣ)) (-ᵣx) := by
  have h2k := two_le_two_pow hk
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hnn : (-ᵣ(-ᵣ(eᵣ : R))) = eᵣ := neg_neg eᵣ
  have hcast : castPortal hk (fenwickUQLapChar (R := R) k x) =
      fun i j => (if i = j then x else zᵣ) -ᵣ castPortal hk (fenwickUQLap (R := R) k) i j := by
    funext i j; unfold castPortal fenwickUQLapChar
    by_cases hij : i = j
    · subst hij; simp only [↓reduceIte]
    · have hne : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ :=
        fin_ne (fun h => hij (Fin.ext (by dsimp only at h; exact h)))
      simp only [hij, hne, ↓reduceIte]
  have hstep' := char_step_of_portal_step (M := castPortal hk (fenwickUQLap (R := R) k)) (p := eᵣ) (q := -ᵣeᵣ) (r := eᵣ) (x := x)
  simp only [neg_neg] at hstep'
  rw [hcast, ← portalTuple_perturb, ← portalTuple_glue, ← hstep']
  apply portalTuple_eq_of_dim_eq (by omega)
  intro i j
  unfold castPortal fenwickUQLapChar
  dsimp only
  have hL := fenwickUQLap_step (R := R) k hk ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩
  rw [hL]
  have hiff : ((⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (k + 1) + 1)) =
                ⟨j.val, by have := j.isLt; omega⟩) ↔
              ((⟨i.val, by have := i.isLt; omega⟩ : Fin ((2 ^ k - 1) + (2 ^ k - 1) + 1 + 2)) =
                ⟨j.val, by have := j.isLt; omega⟩) := by
    constructor <;> (intro h; exact Fin.ext (by injection h))
  by_cases hij : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (k + 1) + 1)) = ⟨j.val, by have := j.isLt; omega⟩
  · have hij' := hiff.mp hij
    simp only [ite_eq_left hij, ite_eq_left hij']; rfl
  · have hij' : ¬ ((⟨i.val, by have := i.isLt; omega⟩ : Fin ((2 ^ k - 1) + (2 ^ k - 1) + 1 + 2)) =
                    ⟨j.val, by have := j.isLt; omega⟩) := fun h => hij (hiff.mpr h)
    simp only [ite_eq_right hij, ite_eq_right hij']; rfl

theorem portalTuple_fenwickUQSignlessChar_succ (k : Nat) (hk : 1 ≤ k) (x : R) :
    portalTuple (castPortal (by omega : 1 ≤ k + 1) (fenwickUQSignlessChar (k + 1) x)) =
    stepGlue (stepPerturb (portalTuple (castPortal hk (fenwickUQSignlessChar k x))) (-ᵣeᵣ) (-ᵣeᵣ) (-ᵣeᵣ) (-ᵣeᵣ))
             (stepPerturb (portalTuple (castPortal hk (fenwickUQSignlessChar k x))) (-ᵣeᵣ) (-ᵣeᵣ) (-ᵣeᵣ) (-ᵣeᵣ)) (-ᵣx) := by
  have h2k := two_le_two_pow hk
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hcast : castPortal hk (fenwickUQSignlessChar (R := R) k x) =
      fun i j => (if i = j then x else zᵣ) -ᵣ castPortal hk (fenwickUQSignless (R := R) k) i j := by
    funext i j; unfold castPortal fenwickUQSignlessChar fenwickUQSignless
    by_cases hij : i = j
    · subst hij; simp only [↓reduceIte]
    · have hne : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ k + 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ :=
        fin_ne (fun h => hij (Fin.ext (by dsimp only at h; exact h)))
      simp only [hij, hne, ↓reduceIte]
  rw [hcast, ← portalTuple_perturb, ← portalTuple_glue]
  rw [← char_step_of_portal_step (M := castPortal hk (fenwickUQSignless k)) (p := eᵣ) (q := eᵣ) (r := eᵣ) (x := x)]
  apply portalTuple_eq_of_dim_eq (by omega)
  intro i j
  unfold castPortal fenwickUQSignlessChar
  dsimp only
  have hQ := fenwickUQSignless_step (R := R) k hk ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩
  change (if _ then x else zᵣ) -ᵣ fenwickUQSignless (R := R) (k + 1) ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ = _
  rw [hQ]
  have hiff : ((⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (k + 1) + 1)) =
                ⟨j.val, by have := j.isLt; omega⟩) ↔
              ((⟨i.val, by have := i.isLt; omega⟩ : Fin ((2 ^ k - 1) + (2 ^ k - 1) + 1 + 2)) =
                ⟨j.val, by have := j.isLt; omega⟩) := by
    constructor <;> (intro h; exact Fin.ext (by injection h))
  by_cases hij : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (k + 1) + 1)) = ⟨j.val, by have := j.isLt; omega⟩
  · have hij' := hiff.mp hij
    simp only [ite_eq_left hij, ite_eq_left hij']; rfl
  · have hij' : ¬ ((⟨i.val, by have := i.isLt; omega⟩ : Fin ((2 ^ k - 1) + (2 ^ k - 1) + 1 + 2)) =
                    ⟨j.val, by have := j.isLt; omega⟩) := fun h => hij (hiff.mpr h)
    simp only [ite_eq_right hij, ite_eq_right hij']; rfl

/-! ### Base-Case Portal Evaluations at `k = 1` (`3 × 3` Path `0 - 1 - 2`) -/

private theorem fenwickUQAdj_one_entries (c : R) :
    let M := castPortal (Nat.le_refl 1) (fenwickUQAdj (R := R) 1 c)
    M ⟨0, by omega⟩ ⟨0, by omega⟩ = zᵣ ∧
    M ⟨0, by omega⟩ ⟨1, by omega⟩ = eᵣ ∧
    M ⟨0, by omega⟩ ⟨2, by omega⟩ = zᵣ ∧
    M ⟨1, by omega⟩ ⟨0, by omega⟩ = eᵣ ∧
    M ⟨1, by omega⟩ ⟨1, by omega⟩ = zᵣ ∧
    M ⟨1, by omega⟩ ⟨2, by omega⟩ = eᵣ ∧
    M ⟨2, by omega⟩ ⟨0, by omega⟩ = zᵣ ∧
    M ⟨2, by omega⟩ ⟨1, by omega⟩ = eᵣ ∧
    M ⟨2, by omega⟩ ⟨2, by omega⟩ = zᵣ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold castPortal fenwickUQAdj fenwickEdge lowbit; simp)

theorem portalTuple_fenwickUQAdj_one (c : R) :
    portalTuple (castPortal (Nat.le_refl 1) (fenwickUQAdj (R := R) 1 c)) =
    ⟨zᵣ, -ᵣeᵣ, -ᵣeᵣ, zᵣ, eᵣ, eᵣ⟩ := by
  have ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := fenwickUQAdj_one_entries (R := R) c
  unfold portalTuple
  simp only [PortalState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_fin3, h00, h01, h02, h10, h11, h12, h20, h21, h22]
    unfold rsub
    simp [zero_mul, mul_zero, CRing.zero_add, add_zero, neg_zero]
  · rw [det_fin2]; unfold minor; simp only [skipIdx_zero, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _
    rw [h11, h22, h12, h21]
    unfold rsub; simp [zero_mul, CRing.one_mul, CRing.zero_add]
  · rw [det_fin2]; unfold minor; simp only [skipIdx_last]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _
    rw [h00, h11, h01, h10]
    unfold rsub; simp [zero_mul, CRing.one_mul, CRing.zero_add]
  · rw [det_fin1]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    exact h11
  · have hs : rsign (R := R) 2 = eᵣ := rfl
    rw [hs, CRing.one_mul, det_fin2]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _
    rw [h10, h21, h11, h20]
    unfold rsub; simp [zero_mul, CRing.one_mul, neg_zero, add_zero]
  · have hs : rsign (R := R) 2 = eᵣ := rfl
    rw [hs, CRing.one_mul, det_fin2]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _
    rw [h01, h12, h02, h11]
    unfold rsub; simp [zero_mul, CRing.one_mul, neg_zero, add_zero]

private theorem fenwickUQDeg_one_entries :
    fenwickUQDeg (R := R) 1 ⟨0, by omega⟩ = eᵣ ∧
    fenwickUQDeg (R := R) 1 ⟨1, by omega⟩ = eᵣ +ᵣ eᵣ ∧
    fenwickUQDeg (R := R) 1 ⟨2, by omega⟩ = eᵣ := by
  have ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := fenwickUQAdj_one_entries (R := R) eᵣ
  unfold castPortal at h00 h01 h02 h10 h11 h12 h20 h21 h22
  dsimp only at h00 h01 h02 h10 h11 h12 h20 h21 h22
  refine ⟨?_, ?_, ?_⟩
  · unfold fenwickUQDeg
    rw [sumFin_succ, sumFin_succ, sumFin_succ, sumFin_zero, add_zero]
    change fenwickUQAdj (R := R) 1 eᵣ ⟨0, by omega⟩ ⟨0, by omega⟩ +ᵣ
           (fenwickUQAdj (R := R) 1 eᵣ ⟨0, by omega⟩ ⟨1, by omega⟩ +ᵣ
            fenwickUQAdj (R := R) 1 eᵣ ⟨0, by omega⟩ ⟨2, by omega⟩) = eᵣ
    rw [h00, h01, h02, CRing.zero_add, add_zero]
  · unfold fenwickUQDeg
    rw [sumFin_succ, sumFin_succ, sumFin_succ, sumFin_zero, add_zero]
    change fenwickUQAdj (R := R) 1 eᵣ ⟨1, by omega⟩ ⟨0, by omega⟩ +ᵣ
           (fenwickUQAdj (R := R) 1 eᵣ ⟨1, by omega⟩ ⟨1, by omega⟩ +ᵣ
            fenwickUQAdj (R := R) 1 eᵣ ⟨1, by omega⟩ ⟨2, by omega⟩) = eᵣ +ᵣ eᵣ
    rw [h10, h11, h12, CRing.zero_add]
  · unfold fenwickUQDeg
    rw [sumFin_succ, sumFin_succ, sumFin_succ, sumFin_zero, add_zero]
    change fenwickUQAdj (R := R) 1 eᵣ ⟨2, by omega⟩ ⟨0, by omega⟩ +ᵣ
           (fenwickUQAdj (R := R) 1 eᵣ ⟨2, by omega⟩ ⟨1, by omega⟩ +ᵣ
            fenwickUQAdj (R := R) 1 eᵣ ⟨2, by omega⟩ ⟨2, by omega⟩) = eᵣ
    rw [h20, h21, h22, CRing.zero_add, add_zero]

/-! ### Theorem 1: Constant-Determinant Collapse, Unimodularity & Farey Chord (`∀ k ≥ 2, ∀ c : R`) -/

/-- Exact 6-tuple fixed point for `A(G_k(c))` over ANY commutative ring `R` and ALL `k ≥ 2`!
Notice `dLR = zᵣ` identically — standard Schur complement divides by zero at every scale,
while our division-free 6-tuple Portal-Transfer engine proves the collapse cleanly! -/
theorem fenwickUQ_portalTuple_const (c : R) (k : Nat) (hk : 2 ≤ k) :
    portalTuple (castPortal (by omega : 1 ≤ k) (fenwickUQAdj (R := R) k c)) =
    ⟨-ᵣ(rnat 4 *ᵣ c), eᵣ, eᵣ, zᵣ, eᵣ, eᵣ⟩ := by
  have hr4 : rnat (R := R) 4 *ᵣ c = c +ᵣ (c +ᵣ (c +ᵣ c)) := by
    simp only [rnat, CRing.zero_add, right_distrib, CRing.one_mul, CRing.add_assoc]
  have h2 : portalTuple (castPortal (by omega : 1 ≤ 2) (fenwickUQAdj (R := R) 2 c)) =
            ⟨-ᵣ(rnat 4 *ᵣ c), eᵣ, eᵣ, zᵣ, eᵣ, eᵣ⟩ := by
    rw [portalTuple_fenwickUQAdj_succ 1 (Nat.le_refl 1) c, portalTuple_fenwickUQAdj_one c]
    unfold stepPerturb stepGlue rsub
    simp only [PortalState.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr4]
      simp only [mul_zero, CRing.zero_add, add_zero, CRing.one_mul, mul_one,
                 neg_mul, mul_neg, neg_add, neg_zero, neg_neg, CRing.add_assoc, CRing.left_distrib]
    · simp [zero_mul, mul_zero, CRing.zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, CRing.one_mul]
    · simp [zero_mul, mul_zero, CRing.zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, CRing.one_mul]
    · simp [zero_mul, mul_zero, add_zero]
    · simp [mul_zero, neg_zero, add_zero, CRing.one_mul]
    · simp [mul_zero, neg_zero, add_zero, CRing.one_mul]
  -- Induction on m = k - 2
  have hgen : ∀ m : Nat,
      portalTuple (castPortal (by omega : 1 ≤ m + 2) (fenwickUQAdj (R := R) (m + 2) c)) =
      ⟨-ᵣ(rnat 4 *ᵣ c), eᵣ, eᵣ, zᵣ, eᵣ, eᵣ⟩ := by
    intro m
    induction m with
    | zero => exact h2
    | succ m ih =>
      rw [portalTuple_fenwickUQAdj_succ (m + 2) (by omega) c, ih]
      unfold stepPerturb stepGlue rsub
      simp only [PortalState.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hr4]
        simp only [mul_zero, CRing.zero_add, add_zero, CRing.one_mul, mul_one, neg_add, CRing.add_assoc]
        -- Goal: -ᵣc +ᵣ (-ᵣc +ᵣ (-ᵣc +ᵣ (-ᵣc +ᵣ (c +ᵣ c)))) +ᵣ (-ᵣc +ᵣ (-ᵣc +ᵣ (-ᵣc +ᵣ (-ᵣc +ᵣ (c +ᵣ c))))) = -ᵣc +ᵣ (-ᵣc +ᵣ (-ᵣc +ᵣ -ᵣc))
        have h1 : ∀ a b : R, a +ᵣ (-ᵣa +ᵣ b) = b := fun a b => by
          rw [← CRing.add_assoc, add_right_neg, CRing.zero_add]
        have h2 : ∀ a b : R, -ᵣa +ᵣ (a +ᵣ b) = b := fun a b => by
          rw [← CRing.add_assoc, CRing.add_left_neg, CRing.zero_add]
        simp only [h1, h2, add_right_neg, CRing.add_left_neg, add_zero]
      · simp [zero_mul, mul_zero, CRing.zero_add, add_zero, CRing.one_mul]
      · simp [zero_mul, mul_zero, CRing.zero_add, add_zero, CRing.one_mul]
      · simp [zero_mul, mul_zero, add_zero]
      · simp [mul_zero, neg_zero, add_zero, CRing.one_mul]
      · simp [mul_zero, neg_zero, add_zero, CRing.one_mul]
  rcases (⟨k - 2, by omega⟩ : ∃ m, k = m + 2) with ⟨m, rfl⟩
  exact hgen m

/-- Theorem 1a: Constant-Determinant Collapse `det(A(G_k(c))) = -4 * c` for ALL `k ≥ 2` and ANY `c : R`! -/
theorem fenwickUQ_det_const (c : R) (k : Nat) (hk : 2 ≤ k) :
    det (fenwickUQAdj (R := R) k c) = -ᵣ(rnat 4 *ᵣ c) := by
  rw [← det_castPortal (by omega : 1 ≤ k)]
  have h := congrArg PortalState.d0 (fenwickUQ_portalTuple_const (R := R) c k hk)
  exact h

/-- Theorem 1a (Integer Unweighted Specialization): `det(A(G_k)) = -4` for ALL `k ≥ 2`! -/
theorem fenwickUQ_det_const_int (k : Nat) (hk : 2 ≤ k) :
    det (fenwickUQAdj (R := Int) k 1) = -4 := by
  have h := fenwickUQ_det_const (R := Int) 1 k hk
  rw [rnat_int] at h
  exact h

/-- Theorem 1b (Unimodularity): Deleting portal `0` yields `det(A(G_k(c)) \ {0}) = 1` for ALL `k ≥ 2`! -/
theorem fenwickUQ_unimodular (c : R) (k : Nat) (hk : 2 ≤ k) :
    det (minor (fenwickUQAdj (R := R) k c) ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩) = eᵣ := by
  rw [← minor00_castPortal (by omega : 1 ≤ k)]
  have h := congrArg PortalState.dL (fenwickUQ_portalTuple_const (R := R) c k hk)
  exact h

/-- Theorem 1c (Structural Singularity of Interior): `Δ_LR(A(G_k(c))) = 0` for ALL `k ≥ 2`!
Proves standard Schur complement `A_BB - A_BI A_II^{-1} A_IB` is undefined at every scale `k ≥ 2`. -/
theorem fenwickUQ_interior_zero (c : R) (k : Nat) (hk : 2 ≤ k) :
    (portalTuple (castPortal (by omega : 1 ≤ k) (fenwickUQAdj (R := R) k c))).dLR = zᵣ :=
  congrArg PortalState.dLR (fenwickUQ_portalTuple_const (R := R) c k hk)

/-- Theorem 1d (Outerplanar Farey Chord Constant Determinant): Adding the chord `(0, 2^k)` of weight `c`
yields `det(A(Farey_k(c))) = -2 * c` for ALL `k ≥ 2`! -/
theorem farey_det_const (c : R) (k : Nat) (hk : 2 ≤ k) :
    det (perturb (castPortal (by omega : 1 ≤ k) (fenwickUQAdj (R := R) k c)) zᵣ c c zᵣ) =
    -ᵣ(rnat 2 *ᵣ c) := by
  have h := congrArg PortalState.d0 (portalTuple_perturb (castPortal (by omega : 1 ≤ k) (fenwickUQAdj (R := R) k c)) zᵣ c c zᵣ)
  rw [fenwickUQ_portalTuple_const c k hk] at h
  unfold portalTuple stepPerturb rsub at h
  dsimp only at h
  rw [h]
  have hr4 : rnat (R := R) 4 *ᵣ c = c +ᵣ (c +ᵣ (c +ᵣ c)) := by
    simp only [rnat, CRing.zero_add, right_distrib, CRing.one_mul, CRing.add_assoc]
  have hr2 : rnat (R := R) 2 *ᵣ c = c +ᵣ c := by
    simp only [rnat, CRing.zero_add, right_distrib, CRing.one_mul]
  rw [hr4, hr2]
  simp only [mul_zero, CRing.zero_add, add_zero, mul_one, neg_add, CRing.add_assoc]
  have h1 : ∀ a b : R, a +ᵣ (-ᵣa +ᵣ b) = b := fun a b => by
    rw [← CRing.add_assoc, add_right_neg, CRing.zero_add]
  have h2 : ∀ a b : R, -ᵣa +ᵣ (a +ᵣ b) = b := fun a b => by
    rw [← CRing.add_assoc, CRing.add_left_neg, CRing.zero_add]
  simp only [h2, CRing.add_left_neg, add_zero]

/-! ### Theorem 2: Exact Characteristic Polynomial Recurrence over Any `CRing R` & `Z[X]` (`FPS`) -/

theorem portalTuple_fenwickUQChar_one (x : R) :
    portalTuple (castPortal (Nat.le_refl 1) (fenwickUQChar (R := R) 1 x)) = adjCharState x 0 := by
  have ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := fenwickUQAdj_one_entries (R := R) eᵣ
  unfold castPortal at h00 h01 h02 h10 h11 h12 h20 h21 h22
  dsimp only at h00 h01 h02 h10 h11 h12 h20 h21 h22
  have hent :
      let M := castPortal (Nat.le_refl 1) (fenwickUQChar (R := R) 1 x)
      M ⟨0, by omega⟩ ⟨0, by omega⟩ = x ∧
      M ⟨0, by omega⟩ ⟨1, by omega⟩ = -ᵣeᵣ ∧
      M ⟨0, by omega⟩ ⟨2, by omega⟩ = zᵣ ∧
      M ⟨1, by omega⟩ ⟨0, by omega⟩ = -ᵣeᵣ ∧
      M ⟨1, by omega⟩ ⟨1, by omega⟩ = x ∧
      M ⟨1, by omega⟩ ⟨2, by omega⟩ = -ᵣeᵣ ∧
      M ⟨2, by omega⟩ ⟨0, by omega⟩ = zᵣ ∧
      M ⟨2, by omega⟩ ⟨1, by omega⟩ = -ᵣeᵣ ∧
      M ⟨2, by omega⟩ ⟨2, by omega⟩ = x := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold castPortal fenwickUQChar rsub; simp only [↓reduceIte]; rw [h00, neg_zero, add_zero]
    · unfold castPortal fenwickUQChar rsub; have hne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h01, CRing.zero_add]
    · unfold castPortal fenwickUQChar rsub; have hne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h02, neg_zero, add_zero]
    · unfold castPortal fenwickUQChar rsub; have hne : (⟨1, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h10, CRing.zero_add]
    · unfold castPortal fenwickUQChar rsub; simp only [↓reduceIte]; rw [h11, neg_zero, add_zero]
    · unfold castPortal fenwickUQChar rsub; have hne : (⟨1, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h12, CRing.zero_add]
    · unfold castPortal fenwickUQChar rsub; have hne : (⟨2, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h20, neg_zero, add_zero]
    · unfold castPortal fenwickUQChar rsub; have hne : (⟨2, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h21, CRing.zero_add]
    · unfold castPortal fenwickUQChar rsub; simp only [↓reduceIte]; rw [h22, neg_zero, add_zero]
  rcases hent with ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩
  unfold portalTuple adjCharState
  simp only [PortalState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_fin3, e00, e01, e02, e10, e11, e12, e20, e21, e22]
    unfold rsub
    simp [mul_zero, add_zero, neg_zero, neg_mul, mul_neg, neg_neg, CRing.one_mul, mul_one]
  · rw [det_fin2]; unfold minor; simp only [skipIdx_zero, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e11, e22, e12, e21]
    unfold rsub; simp [neg_mul, mul_neg, neg_neg, CRing.one_mul]
  · rw [det_fin2]; unfold minor; simp only [skipIdx_last]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e00, e11, e01, e10]
    unfold rsub; simp [neg_mul, mul_neg, neg_neg, CRing.one_mul]
  · rw [det_fin1]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]; exact e11
  · have hs : rsign (R := R) 2 = eᵣ := rfl
    rw [hs, CRing.one_mul, det_fin2]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e10, e21, e11, e20]
    unfold rsub; simp [mul_zero, neg_mul, mul_neg, neg_neg, CRing.one_mul, neg_zero, add_zero]
  · have hs : rsign (R := R) 2 = eᵣ := rfl
    rw [hs, CRing.one_mul, det_fin2]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e01, e12, e02, e11]
    unfold rsub; simp [zero_mul, neg_mul, mul_neg, neg_neg, CRing.one_mul, neg_zero, add_zero]

/-- Theorem 2a: Exact characteristic polynomial 6-tuple transfer for `x I - A(G_k)` over ANY `CRing R` (`∀ k ≥ 1`)! -/
theorem fenwickUQ_charpoly_transfer (x : R) (k : Nat) (hk : 1 ≤ k) :
    portalTuple (castPortal hk (fenwickUQChar (R := R) k x)) = adjCharState x (k - 1) := by
  have hgen : ∀ m : Nat,
      portalTuple (castPortal (by omega : 1 ≤ m + 1) (fenwickUQChar (R := R) (m + 1) x)) = adjCharState x m := by
    intro m
    induction m with
    | zero => exact portalTuple_fenwickUQChar_one x
    | succ m ih =>
      rw [portalTuple_fenwickUQChar_succ (m + 1) (by omega) x, ih]
      rfl
  rcases (⟨k - 1, by omega⟩ : ∃ m, k = m + 1) with ⟨m, rfl⟩
  exact hgen m

/-- Theorem 2b (Exact Polynomial-Ring `Z[X]` Instantiation via `FPS`):
For EVERY `k ≥ 1`, the characteristic polynomial `det(X I - A(G_k)) ∈ Z[X]` equals `(adjCharState FPS.X (k - 1)).d0`! -/
theorem fenwickUQ_charpoly_fps (k : Nat) (hk : 1 ≤ k) :
    det (fenwickUQChar (R := FPS) k FPS.X) = (adjCharState FPS.X (k - 1)).d0 := by
  rw [← det_castPortal hk]
  exact congrArg PortalState.d0 (fenwickUQ_charpoly_transfer (R := FPS) FPS.X k hk)

theorem portalTuple_fenwickUQLapChar_one (x : R) :
    portalTuple (castPortal (Nat.le_refl 1) (fenwickUQLapChar (R := R) 1 x)) = lapCharState x 0 := by
  have ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := fenwickUQAdj_one_entries (R := R) eᵣ
  have ⟨d0, d1, d2⟩ := fenwickUQDeg_one_entries (R := R)
  unfold castPortal at h00 h01 h02 h10 h11 h12 h20 h21 h22
  dsimp only at h00 h01 h02 h10 h11 h12 h20 h21 h22
  have hr2 : rnat (R := R) 2 = eᵣ +ᵣ eᵣ := by simp only [rnat, CRing.zero_add]
  have hent :
      let M := castPortal (Nat.le_refl 1) (fenwickUQLapChar (R := R) 1 x)
      M ⟨0, by omega⟩ ⟨0, by omega⟩ = x -ᵣ eᵣ ∧
      M ⟨0, by omega⟩ ⟨1, by omega⟩ = eᵣ ∧
      M ⟨0, by omega⟩ ⟨2, by omega⟩ = zᵣ ∧
      M ⟨1, by omega⟩ ⟨0, by omega⟩ = eᵣ ∧
      M ⟨1, by omega⟩ ⟨1, by omega⟩ = x -ᵣ rnat 2 ∧
      M ⟨1, by omega⟩ ⟨2, by omega⟩ = eᵣ ∧
      M ⟨2, by omega⟩ ⟨0, by omega⟩ = zᵣ ∧
      M ⟨2, by omega⟩ ⟨1, by omega⟩ = eᵣ ∧
      M ⟨2, by omega⟩ ⟨2, by omega⟩ = x -ᵣ eᵣ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold castPortal fenwickUQLapChar fenwickUQLap rsub; simp only [↓reduceIte]; rw [d0, h00, neg_zero, add_zero]
    · unfold castPortal fenwickUQLapChar fenwickUQLap rsub; have hne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h01, CRing.zero_add, CRing.zero_add, neg_neg]
    · unfold castPortal fenwickUQLapChar fenwickUQLap rsub; have hne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h02, neg_zero, add_zero, neg_zero, add_zero]
    · unfold castPortal fenwickUQLapChar fenwickUQLap rsub; have hne : (⟨1, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h10, CRing.zero_add, CRing.zero_add, neg_neg]
    · unfold castPortal fenwickUQLapChar fenwickUQLap rsub; simp only [↓reduceIte]; rw [d1, h11, hr2, neg_zero, add_zero]
    · unfold castPortal fenwickUQLapChar fenwickUQLap rsub; have hne : (⟨1, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h12, CRing.zero_add, CRing.zero_add, neg_neg]
    · unfold castPortal fenwickUQLapChar fenwickUQLap rsub; have hne : (⟨2, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h20, neg_zero, add_zero, neg_zero, add_zero]
    · unfold castPortal fenwickUQLapChar fenwickUQLap rsub; have hne : (⟨2, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h21, CRing.zero_add, CRing.zero_add, neg_neg]
    · unfold castPortal fenwickUQLapChar fenwickUQLap rsub; simp only [↓reduceIte]; rw [d2, h22, neg_zero, add_zero]
  rcases hent with ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩
  unfold portalTuple lapCharState
  simp only [PortalState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_fin3, e00, e01, e02, e10, e11, e12, e20, e21, e22]
    unfold rsub
    simp [mul_zero, add_zero, neg_zero, CRing.one_mul, mul_one]
  · rw [det_fin2]; unfold minor; simp only [skipIdx_zero, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e11, e22, e12, e21]
    unfold rsub; simp [CRing.one_mul]
  · rw [det_fin2]; unfold minor; simp only [skipIdx_last]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e00, e11, e01, e10]
    unfold rsub; simp [CRing.one_mul, CRing.mul_comm (x +ᵣ -ᵣeᵣ)]
  · rw [det_fin1]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]; exact e11
  · have hs : rsign (R := R) 2 = eᵣ := rfl
    rw [hs, CRing.one_mul, det_fin2]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e10, e21, e11, e20]
    unfold rsub; simp [mul_zero, CRing.one_mul, neg_zero, add_zero]
  · have hs : rsign (R := R) 2 = eᵣ := rfl
    rw [hs, CRing.one_mul, det_fin2]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e01, e12, e02, e11]
    unfold rsub; simp [zero_mul, CRing.one_mul, neg_zero, add_zero]

/-- Theorem 2c: Exact Laplacian characteristic polynomial transfer over ANY `CRing R` (`∀ k ≥ 1`)! -/
theorem fenwickUQLap_charpoly_transfer (x : R) (k : Nat) (hk : 1 ≤ k) :
    portalTuple (castPortal hk (fenwickUQLapChar (R := R) k x)) = lapCharState x (k - 1) := by
  have hgen : ∀ m : Nat,
      portalTuple (castPortal (by omega : 1 ≤ m + 1) (fenwickUQLapChar (R := R) (m + 1) x)) = lapCharState x m := by
    intro m
    induction m with
    | zero => exact portalTuple_fenwickUQLapChar_one x
    | succ m ih =>
      rw [portalTuple_fenwickUQLapChar_succ (m + 1) (by omega) x, ih]
      rfl
  rcases (⟨k - 1, by omega⟩ : ∃ m, k = m + 1) with ⟨m, rfl⟩
  exact hgen m

/-- Theorem 2d (Exact Laplacian Polynomial-Ring `Z[X]` Instantiation via `FPS`): -/
theorem fenwickUQLap_charpoly_fps (k : Nat) (hk : 1 ≤ k) :
    det (fenwickUQLapChar (R := FPS) k FPS.X) = (lapCharState FPS.X (k - 1)).d0 := by
  rw [← det_castPortal hk]
  exact congrArg PortalState.d0 (fenwickUQLap_charpoly_transfer (R := FPS) FPS.X k hk)

private theorem stepPerturb_int (st : PortalState Int) (p q1 q2 r : Int) :
    stepPerturb st p q1 q2 r =
      ⟨st.d0 + p * st.dL + r * st.dR + (p * r - q1 * q2) * st.dLR + q1 * st.d0R + q2 * st.dR0,
       st.dL + r * st.dLR, st.dR + p * st.dLR, st.dLR, st.d0R - q2 * st.dLR, st.dR0 - q1 * st.dLR⟩ := rfl

private theorem stepGlue_int (s1 s2 : PortalState Int) (s : Int) :
    stepGlue s1 s2 s =
      ⟨s1.d0 * s2.dL + s1.dR * s2.d0 + s * (s1.dR * s2.dL),
       s1.dL * s2.dL + s1.dLR * s2.d0 + s * (s1.dLR * s2.dL),
       s1.d0 * s2.dLR + s1.dR * s2.dR + s * (s1.dR * s2.dLR),
       s1.dL * s2.dLR + s1.dLR * s2.dR + s * (s1.dLR * s2.dLR),
       s1.d0R * s2.d0R, s1.dR0 * s2.dR0⟩ := rfl

/-! ### Theorem 3: Exact `x = 2` Laplacian & Signless-Laplacian Spectral Collapse (`∀ k ≥ 1`) -/

theorem portalTuple_fenwickUQLapChar_one_two :
    portalTuple (castPortal (Nat.le_refl 1) (fenwickUQLapChar (R := Int) 1 2)) =
    ⟨-2, -1, -1, 0, 1, 1⟩ := by
  rw [portalTuple_fenwickUQLapChar_one (R := Int) 2]
  simp only [lapCharState, PortalState.mk.injEq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fenwickUQLap_eval_two_tuple (k : Nat) (hk : 2 ≤ k) :
    portalTuple (castPortal (by omega : 1 ≤ k) (fenwickUQLapChar (R := Int) k 2)) =
    ⟨2 - (2 : Int) ^ (k + 1), 1, 1, 0, 1, 1⟩ := by
  have h2 : portalTuple (castPortal (by omega : 1 ≤ 2) (fenwickUQLapChar (R := Int) 2 2)) =
            ⟨-6, 1, 1, 0, 1, 1⟩ := by
    rw [portalTuple_fenwickUQLapChar_succ (R := Int) 1 (Nat.le_refl 1) 2, portalTuple_fenwickUQLapChar_one_two]
    rfl
  have hgen : ∀ m : Nat,
      portalTuple (castPortal (by omega : 1 ≤ m + 2) (fenwickUQLapChar (R := Int) (m + 2) 2)) =
      ⟨2 - (2 : Int) ^ (m + 3), 1, 1, 0, 1, 1⟩ := by
    intro m
    induction m with
    | zero => exact h2
    | succ m ih =>
      rw [portalTuple_fenwickUQLapChar_succ (R := Int) (m + 2) (by omega) 2, ih]
      change stepGlue (stepPerturb _ (-1) 1 1 (-1)) (stepPerturb _ (-1) 1 1 (-1)) (-2) = _
      simp only [stepPerturb_int, stepGlue_int, PortalState.mk.injEq]
      have hp : (2 : Int) ^ (m + 4) = (2 : Int) ^ (m + 3) * 2 := Int.pow_succ 2 (m + 3)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind
  rcases (⟨k - 2, by omega⟩ : ∃ m, k = m + 2) with ⟨m, rfl⟩
  exact hgen m

/-- Theorem 3a: Exact `x = 2` Laplacian Collapse `det(2 I - L(G_k)) = 2 - 2^(k + 1)` for ALL `k ≥ 1`! -/
theorem fenwickUQLap_eval_two (k : Nat) (hk : 1 ≤ k) :
    det (fenwickUQLapChar (R := Int) k 2) = 2 - (2 : Int) ^ (k + 1) := by
  match k with
  | 0 => omega
  | 1 =>
    rw [← det_castPortal (Nat.le_refl 1)]
    have h := congrArg PortalState.d0 portalTuple_fenwickUQLapChar_one_two
    dsimp only [portalTuple] at h
    rw [h]; decide
  | m + 2 =>
    rw [← det_castPortal (by omega : 1 ≤ m + 2)]
    exact congrArg PortalState.d0 (fenwickUQLap_eval_two_tuple (m + 2) (by omega))

private theorem four_le_int_two_pow (n : Nat) (hn : 2 ≤ n) : (4 : Int) ≤ (2 : Int) ^ n := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 1
    · subst hm; decide
    · have hm2 : 2 ≤ m := by omega
      have h := ih hm2
      rw [Int.pow_succ]; omega

/-- Corollary 3a: `λ = 2` is NEVER an eigenvalue of `L(G_k)` for ANY `k ≥ 1`! -/
theorem fenwickUQLap_two_not_eigenvalue (k : Nat) (hk : 1 ≤ k) :
    det (fenwickUQLapChar (R := Int) k 2) ≠ 0 := by
  rw [fenwickUQLap_eval_two k hk]
  have h4 := four_le_int_two_pow (k + 1) (by omega)
  omega

theorem portalTuple_fenwickUQSignlessChar_one_two :
    portalTuple (castPortal (Nat.le_refl 1) (fenwickUQSignlessChar (R := Int) 1 2)) =
    ⟨-2, -1, -1, 0, 1, 1⟩ := by
  have ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := fenwickUQAdj_one_entries (R := Int) eᵣ
  have ⟨d0, d1, d2⟩ := fenwickUQDeg_one_entries (R := Int)
  unfold castPortal at h00 h01 h02 h10 h11 h12 h20 h21 h22
  dsimp only at h00 h01 h02 h10 h11 h12 h20 h21 h22
  have hent :
      let M := castPortal (Nat.le_refl 1) (fenwickUQSignlessChar (R := Int) 1 2)
      M ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
      M ⟨0, by omega⟩ ⟨1, by omega⟩ = -1 ∧
      M ⟨0, by omega⟩ ⟨2, by omega⟩ = 0 ∧
      M ⟨1, by omega⟩ ⟨0, by omega⟩ = -1 ∧
      M ⟨1, by omega⟩ ⟨1, by omega⟩ = 0 ∧
      M ⟨1, by omega⟩ ⟨2, by omega⟩ = -1 ∧
      M ⟨2, by omega⟩ ⟨0, by omega⟩ = 0 ∧
      M ⟨2, by omega⟩ ⟨1, by omega⟩ = -1 ∧
      M ⟨2, by omega⟩ ⟨2, by omega⟩ = 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold castPortal fenwickUQSignlessChar rsub; simp only [↓reduceIte]; rw [d0, h00]; rfl
    · unfold castPortal fenwickUQSignlessChar rsub; have hne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h01]; rfl
    · unfold castPortal fenwickUQSignlessChar rsub; have hne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h02]; rfl
    · unfold castPortal fenwickUQSignlessChar rsub; have hne : (⟨1, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h10]; rfl
    · unfold castPortal fenwickUQSignlessChar rsub; simp only [↓reduceIte]; rw [d1, h11]; rfl
    · unfold castPortal fenwickUQSignlessChar rsub; have hne : (⟨1, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h12]; rfl
    · unfold castPortal fenwickUQSignlessChar rsub; have hne : (⟨2, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h20]; rfl
    · unfold castPortal fenwickUQSignlessChar rsub; have hne : (⟨2, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h21]; rfl
    · unfold castPortal fenwickUQSignlessChar rsub; simp only [↓reduceIte]; rw [d2, h22]; rfl
  rcases hent with ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩
  unfold portalTuple
  simp only [PortalState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_fin3, e00, e01, e02, e10, e11, e12, e20, e21, e22]; rfl
  · rw [det_fin2]; unfold minor; simp only [skipIdx_zero, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e11, e22, e12, e21]; rfl
  · rw [det_fin2]; unfold minor; simp only [skipIdx_last]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e00, e11, e01, e10]; rfl
  · rw [det_fin1]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]; exact e11
  · have hs : rsign (R := Int) 2 = eᵣ := rfl
    rw [hs, CRing.one_mul, det_fin2]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e10, e21, e11, e20]; rfl
  · have hs : rsign (R := Int) 2 = eᵣ := rfl
    rw [hs, CRing.one_mul, det_fin2]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e01, e12, e02, e11]; rfl

/-- Theorem 3b: Exact `x = 2` Signless-Laplacian Collapse `det(2 I - Q(G_k)) = 10 - 2^(k + 1)` for ALL `k ≥ 2`! -/
theorem fenwickUQSignless_eval_two_tuple (k : Nat) (hk : 2 ≤ k) :
    portalTuple (castPortal (by omega : 1 ≤ k) (fenwickUQSignlessChar (R := Int) k 2)) =
    ⟨10 - (2 : Int) ^ (k + 1), 1, 1, 0, 1, 1⟩ := by
  have h2 : portalTuple (castPortal (by omega : 1 ≤ 2) (fenwickUQSignlessChar (R := Int) 2 2)) =
            ⟨2, 1, 1, 0, 1, 1⟩ := by
    rw [portalTuple_fenwickUQSignlessChar_succ (R := Int) 1 (Nat.le_refl 1) 2, portalTuple_fenwickUQSignlessChar_one_two]
    rfl
  have hgen : ∀ m : Nat,
      portalTuple (castPortal (by omega : 1 ≤ m + 2) (fenwickUQSignlessChar (R := Int) (m + 2) 2)) =
      ⟨10 - (2 : Int) ^ (m + 3), 1, 1, 0, 1, 1⟩ := by
    intro m
    induction m with
    | zero => exact h2
    | succ m ih =>
      rw [portalTuple_fenwickUQSignlessChar_succ (R := Int) (m + 2) (by omega) 2, ih]
      change stepGlue (stepPerturb _ (-1) (-1) (-1) (-1)) (stepPerturb _ (-1) (-1) (-1) (-1)) (-2) = _
      simp only [stepPerturb_int, stepGlue_int, PortalState.mk.injEq]
      have hp : (2 : Int) ^ (m + 4) = (2 : Int) ^ (m + 3) * 2 := Int.pow_succ 2 (m + 3)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind
  rcases (⟨k - 2, by omega⟩ : ∃ m, k = m + 2) with ⟨m, rfl⟩
  exact hgen m

theorem fenwickUQSignless_eval_two (k : Nat) (hk : 2 ≤ k) :
    det (fenwickUQSignlessChar (R := Int) k 2) = 10 - (2 : Int) ^ (k + 1) := by
  rw [← det_castPortal (by omega : 1 ≤ k)]
  exact congrArg PortalState.d0 (fenwickUQSignless_eval_two_tuple k hk)

/-- Corollary 3b: `λ = 2` is NEVER an eigenvalue of the signless Laplacian `Q(G_k)` for ANY `k ≥ 1`! -/
theorem fenwickUQSignless_two_not_eigenvalue (k : Nat) (hk : 1 ≤ k) :
    det (fenwickUQSignlessChar (R := Int) k 2) ≠ 0 := by
  match k with
  | 0 => omega
  | 1 =>
    rw [← det_castPortal (Nat.le_refl 1)]
    have h := congrArg PortalState.d0 portalTuple_fenwickUQSignlessChar_one_two
    dsimp only [portalTuple] at h
    rw [h]; decide
  | 2 => rw [fenwickUQSignless_eval_two 2 (by omega)]; decide
  | 3 => rw [fenwickUQSignless_eval_two 3 (by omega)]; decide
  | n + 4 =>
    rw [fenwickUQSignless_eval_two (n + 4) (by omega)]
    have h4 := four_le_int_two_pow (n + 3) (by omega)
    have hp1 : (2 : Int) ^ (n + 4) = (2 : Int) ^ (n + 3) * 2 := Int.pow_succ 2 (n + 3)
    have hp2 : (2 : Int) ^ (n + 4 + 1) = (2 : Int) ^ (n + 4) * 2 := Int.pow_succ 2 (n + 4)
    omega

/-! ### Theorem 4: Spanning-Tree Perfect-Square Law & Exact Dyadic Effective Resistance (`∀ k ≥ 1`) -/

theorem portalTuple_fenwickUQLap_one :
    portalTuple (castPortal (Nat.le_refl 1) (fenwickUQLap (R := Int) 1)) =
    ⟨0, 1, 1, 2, 1, 1⟩ := by
  have ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := fenwickUQAdj_one_entries (R := Int) eᵣ
  have ⟨d0, d1, d2⟩ := fenwickUQDeg_one_entries (R := Int)
  unfold castPortal at h00 h01 h02 h10 h11 h12 h20 h21 h22
  dsimp only at h00 h01 h02 h10 h11 h12 h20 h21 h22
  have hent :
      let M := castPortal (Nat.le_refl 1) (fenwickUQLap (R := Int) 1)
      M ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
      M ⟨0, by omega⟩ ⟨1, by omega⟩ = -1 ∧
      M ⟨0, by omega⟩ ⟨2, by omega⟩ = 0 ∧
      M ⟨1, by omega⟩ ⟨0, by omega⟩ = -1 ∧
      M ⟨1, by omega⟩ ⟨1, by omega⟩ = 2 ∧
      M ⟨1, by omega⟩ ⟨2, by omega⟩ = -1 ∧
      M ⟨2, by omega⟩ ⟨0, by omega⟩ = 0 ∧
      M ⟨2, by omega⟩ ⟨1, by omega⟩ = -1 ∧
      M ⟨2, by omega⟩ ⟨2, by omega⟩ = 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold castPortal fenwickUQLap rsub; simp only [↓reduceIte]; rw [d0, h00]; rfl
    · unfold castPortal fenwickUQLap rsub; have hne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h01]; rfl
    · unfold castPortal fenwickUQLap rsub; have hne : (⟨0, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h02]; rfl
    · unfold castPortal fenwickUQLap rsub; have hne : (⟨1, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h10]; rfl
    · unfold castPortal fenwickUQLap rsub; simp only [↓reduceIte]; rw [d1, h11]; rfl
    · unfold castPortal fenwickUQLap rsub; have hne : (⟨1, by omega⟩ : Fin 3) ≠ ⟨2, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h12]; rfl
    · unfold castPortal fenwickUQLap rsub; have hne : (⟨2, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h20]; rfl
    · unfold castPortal fenwickUQLap rsub; have hne : (⟨2, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := fin_ne (by simp); simp only [hne, ↓reduceIte]; rw [h21]; rfl
    · unfold castPortal fenwickUQLap rsub; simp only [↓reduceIte]; rw [d2, h22]; rfl
  rcases hent with ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩
  unfold portalTuple
  simp only [PortalState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_fin3, e00, e01, e02, e10, e11, e12, e20, e21, e22]; rfl
  · rw [det_fin2]; unfold minor; simp only [skipIdx_zero, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e11, e22, e12, e21]; rfl
  · rw [det_fin2]; unfold minor; simp only [skipIdx_last]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e00, e11, e01, e10]; rfl
  · rw [det_fin1]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]; exact e11
  · have hs : rsign (R := Int) 2 = eᵣ := rfl
    rw [hs, CRing.one_mul, det_fin2]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e10, e21, e11, e20]; rfl
  · have hs : rsign (R := Int) 2 = eᵣ := rfl
    rw [hs, CRing.one_mul, det_fin2]; unfold minor; simp only [skipIdx_zero, skipIdx_last, Fin.succ]
    change _ *ᵣ _ -ᵣ _ *ᵣ _ = _; rw [e01, e12, e02, e11]; rfl

/-- Theorem 4a: Exact 6-tuple for combinatorial Laplacian `L(G_k)` for ALL `k ≥ 1`! -/
theorem fenwickUQLap_portalTuple (k : Nat) (hk : 1 ≤ k) :
    portalTuple (castPortal hk (fenwickUQLap (R := Int) k)) =
    ⟨0, tauSeq k, tauSeq k, dSeq k, tauSeq k, tauSeq k⟩ := by
  have hgen : ∀ m : Nat,
      portalTuple (castPortal (by omega : 1 ≤ m + 1) (fenwickUQLap (R := Int) (m + 1))) =
      ⟨0, (lapSpanPair m).1, (lapSpanPair m).1, (lapSpanPair m).2, (lapSpanPair m).1, (lapSpanPair m).1⟩ := by
    intro m
    induction m with
    | zero => exact portalTuple_fenwickUQLap_one
    | succ m ih =>
      rw [portalTuple_fenwickUQLap_succ (R := Int) (m + 1) (by omega), ih]
      let τ := (lapSpanPair m).1
      let d := (lapSpanPair m).2
      have hpair : lapSpanPair (m + 1) = ((τ + d) * (τ + d), 2 * d * (τ + d)) := rfl
      rw [hpair]
      change stepGlue (stepPerturb _ 1 (-1) (-1) 1) (stepPerturb _ 1 (-1) (-1) 1) 0 = _
      simp only [stepPerturb_int, stepGlue_int, PortalState.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind
  rcases (⟨k - 1, by omega⟩ : ∃ m, k = m + 1) with ⟨m, rfl⟩
  unfold tauSeq dSeq
  have hsub : m + 1 - 1 = m := by omega
  rw [hsub]
  exact hgen m

/-- Theorem 4b (Spanning-Tree Perfect-Square Law):
By Kirchhoff's Matrix-Tree Theorem, the spanning-tree count `τ(G_{k+1}) = det(L(G_{k+1}) \ {0})`
is ALWAYS a perfect square `(tauSeq k + dSeq k)^2` for ALL `k ≥ 1`! -/
theorem fenwickUQLap_spanning_tree_square (k : Nat) (hk : 1 ≤ k) :
    det (minor (fenwickUQLap (R := Int) (k + 1)) ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩) =
    (tauSeq k + dSeq k) * (tauSeq k + dSeq k) := by
  rw [← minor00_castPortal (by omega : 1 ≤ k + 1)]
  have h := congrArg PortalState.dL (fenwickUQLap_portalTuple (k + 1) (by omega))
  dsimp only [portalTuple] at h
  rw [h]
  unfold tauSeq dSeq
  have h1 : k + 1 - 1 = (k - 1) + 1 := by omega
  rw [h1]; rfl

/-- Positivity of spanning-tree counts (non-degeneracy of effective resistance denominator). -/
theorem tauSeq_pos (k : Nat) (_hk : 1 ≤ k) : 0 < tauSeq k ∧ 0 < dSeq k := by
  have hgen : ∀ m : Nat, 0 < (lapSpanPair m).1 ∧ 0 < (lapSpanPair m).2 := by
    intro m
    induction m with
    | zero => exact ⟨by decide, by decide⟩
    | succ m ih =>
      unfold lapSpanPair
      rcases ih with ⟨h1, h2⟩
      have hs : 0 < (lapSpanPair m).1 + (lapSpanPair m).2 := by omega
      exact ⟨Int.mul_pos hs hs, Int.mul_pos (by omega) hs⟩
  unfold tauSeq dSeq
  exact hgen (k - 1)

/-- Theorem 4c (Exact Dyadic Effective Resistance):
Across the entire Fenwick network `G_k`, the exact effective resistance between portals `0` and `2^k`
satisfies `(2^k - 1) * d_k = 2^k * τ_k`, i.e. `R_eff(0, 2^k) = 2^k / (2^k - 1)` for ALL `k ≥ 1`! -/
theorem fenwickUQLap_effective_resistance (k : Nat) (hk : 1 ≤ k) :
    ((2 : Int) ^ k - 1) * dSeq k = (2 : Int) ^ k * tauSeq k := by
  have hgen : ∀ m : Nat,
      ((2 : Int) ^ (m + 1) - 1) * (lapSpanPair m).2 = (2 : Int) ^ (m + 1) * (lapSpanPair m).1 := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      unfold lapSpanPair
      dsimp only
      let τ := (lapSpanPair m).1
      let d := (lapSpanPair m).2
      have hih : ((2 : Int) ^ (m + 1) - 1) * d = (2 : Int) ^ (m + 1) * τ := ih
      have hp : (2 : Int) ^ (m + 2) = 2 * (2 : Int) ^ (m + 1) := by
        rw [Int.pow_succ, Int.mul_comm]
      have hstep : ((2 : Int) ^ (m + 2) - 1) * (2 * d) = (2 : Int) ^ (m + 2) * (τ + d) := by
        rw [hp]
        have h1 : (2 * (2 : Int) ^ (m + 1) - 1) * (2 * d) =
                  2 * (((2 : Int) ^ (m + 1) - 1) * d + (2 : Int) ^ (m + 1) * d) := by
          let P : Int := (2 : Int) ^ (m + 1)
          change (2 * P - 1) * (2 * d) = 2 * ((P - 1) * d + P * d)
          rw [Int.sub_mul, Int.sub_mul, Int.one_mul, Int.mul_add, Int.mul_sub]
          have ha : 2 * P * (2 * d) = 2 * (P * d) + 2 * (P * d) := by
            rw [Int.mul_assoc, ← Int.mul_assoc P 2 d, Int.mul_comm P 2, Int.mul_assoc,
                show (2 : Int) * (2 * (P * d)) = 2 * (P * d) + 2 * (P * d) by omega]
          rw [ha]; omega
        rw [h1, hih, ← Int.mul_add, ← Int.mul_assoc]
      calc ((2 : Int) ^ (m + 2) - 1) * (2 * d * (τ + d))
          = ((2 : Int) ^ (m + 2) - 1) * (2 * d) * (τ + d) := by rw [← Int.mul_assoc]
        _ = (2 : Int) ^ (m + 2) * (τ + d) * (τ + d) := by rw [hstep]
        _ = (2 : Int) ^ (m + 2) * ((τ + d) * (τ + d)) := by rw [Int.mul_assoc]
  unfold tauSeq dSeq
  have heq : k - 1 + 1 = k := by omega
  have h := hgen (k - 1)
  rw [heq] at h
  exact h

end SmallDet
section InversionTheorems
variable {R : Type} [CRing R]

/-- Theorem 5a (Universal Even-Size Closed-Form Inverse over ANY `CRing R`):
For EVERY `m : Nat` (not just powers of two!), the `2m × 2m` Fenwick matrix `B_{2m}` has
exact one-shot closed-form inverse `interleaveInv (fenwickB m)`! -/
theorem fenwickB_closed_form_inv (m : Nat) :
    matMul (fenwickB (R := R) (2 * m)) (interleaveInv (fenwickB m)) = matId (2 * m) := by
  rw [fenwickB_even_eq_interleave]
  exact interleave_mul_inv (fenwickB m)

theorem interleaveInv_symm {m : Nat} (M : Mat m R) (hM : ∀ a b, M a b = M b a) :
    ∀ i j : Fin (2 * m), interleaveInv M i j = interleaveInv M j i := by
  intro i j
  unfold interleaveInv
  by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0
  · simp only [hi, hj, ↓reduceIte]
    apply congrArg CRing.neg
    unfold matMul
    calc sumFin (fun k : Fin m => bidiagUInv m k ⟨i.val / 2, by omega⟩ *ᵣ
           sumFin (fun r : Fin m => M k r *ᵣ bidiagUInv m r ⟨j.val / 2, by omega⟩))
        = sumFin (fun k : Fin m => sumFin (fun r : Fin m =>
            bidiagUInv m k ⟨i.val / 2, by omega⟩ *ᵣ (M k r *ᵣ bidiagUInv m r ⟨j.val / 2, by omega⟩))) := by
          apply sumFin_congr; intro k; rw [← sumFin_mul_left]
      _ = sumFin (fun r : Fin m => sumFin (fun k : Fin m =>
            bidiagUInv m k ⟨i.val / 2, by omega⟩ *ᵣ (M k r *ᵣ bidiagUInv m r ⟨j.val / 2, by omega⟩))) :=
          sumFin_comm _
      _ = sumFin (fun r : Fin m => bidiagUInv m r ⟨j.val / 2, by omega⟩ *ᵣ
            sumFin (fun k : Fin m => M r k *ᵣ bidiagUInv m k ⟨i.val / 2, by omega⟩)) := by
          apply sumFin_congr; intro r
          rw [← sumFin_mul_left]
          apply sumFin_congr; intro k
          rw [hM k r, CRing.mul_comm (M r k), ← CRing.mul_assoc, CRing.mul_comm _ (bidiagUInv m r _), CRing.mul_assoc, CRing.mul_comm (bidiagUInv m k _)]
  · simp only [hi, hj, ↓reduceIte]
  · simp only [hi, hj, ↓reduceIte]
  · simp only [hi, hj, ↓reduceIte]

end InversionTheorems
theorem fenwickBPow2Inv_mul (k : Nat) (hk : 1 ≤ k) :
    matMul (fenwickB (R := Int) (2 ^ k)) (fenwickBPow2Inv k hk) = matId (2 ^ k) := by
  have hpow : 2 * 2 ^ (k - 1) = 2 ^ k := by
    have heq : (k - 1) + 1 = k := by omega
    conv => rhs; rw [← heq]
    rw [Nat.pow_succ]; omega
  funext i j
  unfold matMul fenwickBPow2Inv matId
  have hmul := fenwickB_closed_form_inv (R := Int) (2 ^ (k - 1))
  have hij := congrFun (congrFun hmul ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
  unfold matMul matId at hij
  rw [sumFin_cast (R := Int) hpow.symm]
  have hcongr :
      (fun r : Fin (2 * 2 ^ (k - 1)) =>
        fenwickB (R := Int) (2 ^ k) i ⟨r.val, by omega⟩ *ᵣ
        interleaveInv (fenwickB (R := Int) (2 ^ (k - 1))) ⟨r.val, by omega⟩ ⟨j.val, by omega⟩) =
      (fun r : Fin (2 * 2 ^ (k - 1)) =>
        fenwickB (R := Int) (2 * 2 ^ (k - 1)) ⟨i.val, by omega⟩ r *ᵣ
        interleaveInv (fenwickB (R := Int) (2 ^ (k - 1))) r ⟨j.val, by omega⟩) := by
    funext r
    congr 1
    unfold fenwickB
    dsimp only
    have hf : fenwickEdge (2 ^ k) (i.val + 1) (r.val + 1) =
              fenwickEdge (2 * 2 ^ (k - 1)) (i.val + 1) (r.val + 1) :=
      congrFun (congrFun (congrArg fenwickEdge hpow.symm) (i.val + 1)) (r.val + 1)
    rw [hf]
  rw [hcongr, hij]
  by_cases he : i = j
  · subst he; simp only [↓reduceIte]
  · have hne : (⟨i.val, by omega⟩ : Fin (2 * 2 ^ (k - 1))) ≠ ⟨j.val, by omega⟩ :=
      fin_ne (fun h => he (Fin.ext (by dsimp only at h; exact h)))
    simp only [he, hne, ↓reduceIte]

theorem fenwickBPow2Inv_symm (k : Nat) (hk : 1 ≤ k) (i j : Fin (2 ^ k)) :
    fenwickBPow2Inv k hk i j = fenwickBPow2Inv k hk j i := by
  unfold fenwickBPow2Inv
  exact interleaveInv_symm (fenwickB (R := Int) (2 ^ (k - 1))) (fenwickB_symm _) _ _

theorem fenwickUQAdj_eq_bordered (k : Nat) :
    fenwickUQAdj (R := Int) k 1 = fun i j =>
      if hi : i.val = 0 then
        if hj : j.val = 0 then (zᵣ : Int) else fenwickU k ⟨j.val - 1, by omega⟩
      else
        if hj : j.val = 0 then fenwickU k ⟨i.val - 1, by omega⟩
        else fenwickB (R := Int) (2 ^ k) ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ := by
  funext i j
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · simp only [hi, hj, ↓reduceDIte]
    unfold fenwickUQAdj
    have h0 : fenwickEdge (2 ^ k) i.val j.val = false := by rw [hi, hj]; exact fenwickEdge_irrefl _ _
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
  · simp only [hi, hj, ↓reduceDIte]
    unfold fenwickU fenwickUQAdj
    dsimp only
    have hfeq : fenwickEdge (2 ^ k) i.val j.val = fenwickEdge (2 ^ k) (j.val - 1 + 1) 0 := by
      have h1 : j.val - 1 + 1 = j.val := by omega
      rw [hi, h1, fenwickEdge_symm]
    rw [hfeq]
    by_cases hfe : fenwickEdge (2 ^ k) (j.val - 1 + 1) 0 = true
    · simp only [hfe, ↓reduceIte]; split <;> (split <;> rfl)
    · have hf : fenwickEdge (2 ^ k) (j.val - 1 + 1) 0 = false := by cases h : fenwickEdge (2 ^ k) (j.val - 1 + 1) 0 <;> simp_all
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
  · simp only [hi, hj, ↓reduceDIte]
    unfold fenwickU fenwickUQAdj
    dsimp only
    have hfeq : fenwickEdge (2 ^ k) i.val j.val = fenwickEdge (2 ^ k) (i.val - 1 + 1) 0 := by
      have h1 : i.val - 1 + 1 = i.val := by omega
      rw [hj, h1]
    rw [hfeq]
    by_cases hfe : fenwickEdge (2 ^ k) (i.val - 1 + 1) 0 = true
    · simp only [hfe, ↓reduceIte]; split <;> (split <;> rfl)
    · have hf : fenwickEdge (2 ^ k) (i.val - 1 + 1) 0 = false := by cases h : fenwickEdge (2 ^ k) (i.val - 1 + 1) 0 <;> simp_all
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
  · simp only [hi, hj, ↓reduceDIte]
    unfold fenwickUQAdj fenwickB
    dsimp only
    have h1 : i.val - 1 + 1 = i.val := by omega
    have h2 : j.val - 1 + 1 = j.val := by omega
    rw [h1, h2]
    by_cases hfe : fenwickEdge (2 ^ k) i.val j.val = true
    · simp only [hfe, ↓reduceIte]; split <;> rfl
    · have hf : fenwickEdge (2 ^ k) i.val j.val = false := by cases h : fenwickEdge (2 ^ k) i.val j.val <;> simp_all
      simp only [hf, Bool.false_eq_true, ↓reduceIte]

theorem minor00_fenwickUQAdj_eq_fenwickB (k : Nat) :
    minor (fenwickUQAdj (R := Int) k 1) ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩ = fenwickB (R := Int) (2 ^ k) := by
  funext i j
  unfold minor fenwickUQAdj fenwickB
  simp only [skipIdx_zero, Fin.succ]
  by_cases hfe : fenwickEdge (2 ^ k) (i.val + 1) (j.val + 1) = true
  · simp only [hfe, ↓reduceIte]; split <;> rfl
  · have hf : fenwickEdge (2 ^ k) (i.val + 1) (j.val + 1) = false := by
      cases h : fenwickEdge (2 ^ k) (i.val + 1) (j.val + 1) <;> simp_all
    simp only [hf, Bool.false_eq_true, ↓reduceIte]

/-- Exact Schur Quadratic Form Collapse: `u_k^T B_{2^k}^{-1} u_k = 4` for ALL `k ≥ 2`!
Proved by uniting Mechanism A (`det A = -4`, `det B = 1`) with Mechanism B (`det_bordered_schur`)! -/
theorem fenwickUQ_schur_quad_eq_four (k : Nat) (hk : 2 ≤ k) :
    sumFin (R := Int) (fun r : Fin (2 ^ k) =>
      fenwickU k r *ᵣ sumFin (R := Int) (fun s : Fin (2 ^ k) => fenwickBPow2Inv k (by omega) r s *ᵣ fenwickU k s)) = 4 := by
  have hsch := det_bordered_schur (R := Int) (fenwickB (2 ^ k)) (fenwickBPow2Inv k (by omega)) (fenwickU k)
    (fenwickBPow2Inv_mul k (by omega)) (fenwickB_symm (2 ^ k)) (fenwickBPow2Inv_symm k (by omega))
  dsimp only at hsch
  rw [← fenwickUQAdj_eq_bordered k] at hsch
  rw [fenwickUQ_det_const_int k hk] at hsch
  have hdetB : det (fenwickB (R := Int) (2 ^ k)) = 1 := by
    rw [← minor00_fenwickUQAdj_eq_fenwickB k]
    exact fenwickUQ_unimodular (R := Int) 1 k hk
  rw [hdetB] at hsch
  change (-4 : Int) = -(sumFin (R := Int) (fun r : Fin (2 ^ k) =>
      fenwickU k r *ᵣ sumFin (R := Int) (fun s : Fin (2 ^ k) => fenwickBPow2Inv k (by omega) r s *ᵣ fenwickU k s))) * 1 at hsch
  omega

/-- Theorem 5b (Exact 1/4-Dyadic Inverse for ALL `k ≥ 2`):
For EVERY `k ≥ 2`, `A(G_k) * J_k = 4 * I_{2^k + 1}` over `ℤ` (so `A(G_k)^{-1} ∈ (1/4) ℤ^{(2^k+1)×(2^k+1)}`)! -/
theorem fenwickUQ_dyadic_inv (k : Nat) (hk : 2 ≤ k) :
    matMul (fenwickUQAdj (R := Int) k 1) (fenwickUQDyadicInv k hk) =
    fun i j => if i = j then (4 : Int) else 0 := by
  have hb := bordered_schur_inv (R := Int) (fenwickB (2 ^ k)) (fenwickBPow2Inv k (by omega)) (fenwickU k) 4
    (fenwickBPow2Inv_mul k (by omega)) (fenwickB_symm (2 ^ k)) (fenwickBPow2Inv_symm k (by omega))
    (fenwickUQ_schur_quad_eq_four k hk)
  dsimp only at hb
  rw [← fenwickUQAdj_eq_bordered k] at hb
  exact hb

/-! ### Theorem 6: Second Bit-Structure Family — Binary Heap `H_k` Chebyshev-Product Factorization (`∀ k ≥ 1`) -/

section BinaryHeapFamily
variable {R : Type} [CRing R]

theorem heapEdge_symm (u v : Nat) : heapEdge u v = heapEdge v u := by
  unfold heapEdge
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact Or.comm

theorem heapEdge_irrefl (u : Nat) : heapEdge u u = false := by
  unfold heapEdge
  simp only [decide_eq_false_iff_not, not_or]
  have hle := lowbit_le u
  constructor <;> (intro ⟨h2, hdir⟩; omega)

theorem heapEdge_cross {k u v : Nat} (hu1 : 0 < u) (hu2 : u < 2 ^ k)
    (hv1 : 2 ^ k < v) (hv2 : v < 2 ^ (k + 1)) : heapEdge u v = false := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  unfold heapEdge
  simp only [decide_eq_false_iff_not, not_or]
  constructor
  · intro ⟨h2, hdir⟩
    have hle := add_lowbit_le_two_pow k u hu1 hu2
    omega
  · intro ⟨h2, hdir⟩
    have hv'1 : 0 < v - 2 ^ k := by omega
    have hv'2 : v - 2 ^ k < 2 ^ k := by omega
    have hlb : lowbit v = lowbit (v - 2 ^ k) := by
      have heq : v = 2 ^ k + (v - 2 ^ k) := by omega
      conv => lhs; rw [heq]
      exact lowbit_add_two_pow k (v - 2 ^ k) hv'1 hv'2
    have hle := lowbit_le (v - 2 ^ k)
    rw [hlb] at h2 hdir
    omega

theorem heapEdge_root_left {k u : Nat} (hk : 1 ≤ k) (hu1 : 0 < u) (hu2 : u < 2 ^ k) :
    heapEdge (2 ^ k) u = decide (u = 2 ^ (k - 1)) := by
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have heq : (k - 1) + 1 = k := by omega
    conv => lhs; rw [← heq]
    rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ (k - 1) := Nat.two_pow_pos (k - 1)
  have hlbR : lowbit (2 ^ k) = 2 ^ k := lowbit_two_pow k
  unfold heapEdge
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    rcases h with ⟨h2, hdir⟩ | ⟨h2, hdir⟩
    · rw [hlbR] at hdir; omega
    · have hle := add_lowbit_le_two_pow k u hu1 hu2
      omega
  · intro heq
    left
    rw [hlbR]
    exact ⟨by omega, Or.inl (by omega)⟩

theorem heapEdge_root_right {k v : Nat} (hk : 1 ≤ k) (hv1 : 2 ^ k < v) (hv2 : v < 2 ^ (k + 1)) :
    heapEdge (2 ^ k) v = decide (v = 2 ^ k + 2 ^ (k - 1)) := by
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have heq : (k - 1) + 1 = k := by omega
    conv => lhs; rw [← heq]
    rw [Nat.pow_succ]; omega
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ (k - 1) := Nat.two_pow_pos (k - 1)
  have hlbR : lowbit (2 ^ k) = 2 ^ k := lowbit_two_pow k
  unfold heapEdge
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    rcases h with ⟨h2, hdir⟩ | ⟨h2, hdir⟩
    · rw [hlbR] at hdir; omega
    · have hv'1 : 0 < v - 2 ^ k := by omega
      have hv'2 : v - 2 ^ k < 2 ^ k := by omega
      have hlb : lowbit v = lowbit (v - 2 ^ k) := by
        have heq : v = 2 ^ k + (v - 2 ^ k) := by omega
        conv => lhs; rw [heq]
        exact lowbit_add_two_pow k (v - 2 ^ k) hv'1 hv'2
      have hle := lowbit_le (v - 2 ^ k)
      rw [hlb] at h2 hdir
      omega
  · intro heq
    left
    rw [hlbR]
    exact ⟨by omega, Or.inr (by omega)⟩

theorem heapEdge_shift_right {k u v : Nat}
    (hu1 : 2 ^ k < u) (hu2 : u < 2 ^ (k + 1))
    (hv1 : 2 ^ k < v) (hv2 : v < 2 ^ (k + 1)) :
    heapEdge u v = heapEdge (u - 2 ^ k) (v - 2 ^ k) := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hlbU : lowbit u = lowbit (u - 2 ^ k) := by
    have heq : u = 2 ^ k + (u - 2 ^ k) := by omega
    conv => lhs; rw [heq]
    exact lowbit_add_two_pow k (u - 2 ^ k) (by omega) (by omega)
  have hlbV : lowbit v = lowbit (v - 2 ^ k) := by
    have heq : v = 2 ^ k + (v - 2 ^ k) := by omega
    conv => lhs; rw [heq]
    exact lowbit_add_two_pow k (v - 2 ^ k) (by omega) (by omega)
  have hleU := lowbit_le (u - 2 ^ k)
  have hleV := lowbit_le (v - 2 ^ k)
  unfold heapEdge
  rw [hlbU, hlbV]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h; rcases h with ⟨h2, hdir⟩ | ⟨h2, hdir⟩
    · left; exact ⟨h2, by omega⟩
    · right; exact ⟨h2, by omega⟩
  · intro h; rcases h with ⟨h2, hdir⟩ | ⟨h2, hdir⟩
    · left; exact ⟨h2, by omega⟩
    · right; exact ⟨h2, by omega⟩

/-- Helper: any matrix with an all-zero column has determinant zero (division-free induction). -/
private theorem det_eq_zero_of_col_zero : ∀ {n : Nat} (M : Mat n R) (c : Fin n),
    (∀ i : Fin n, M i c = zᵣ) → det M = zᵣ
  | 0, _, c, _ => Fin.elim0 c
  | m + 1, M, c, hc => by
    conv => lhs; unfold det
    rw [sumFin_congr (g := fun _ => zᵣ)]
    · exact sumFin_const_zero
    · intro j
      by_cases hjc : j = c
      · subst hjc
        rw [hc ⟨0, Nat.zero_lt_succ m⟩, mul_zero, zero_mul]
      · have hne : c.val ≠ j.val := fun h => hjc (Fin.ext h.symm)
        by_cases hlt : c.val < j.val
        · have hz : det (minor M ⟨0, Nat.zero_lt_succ m⟩ j) = zᵣ := by
            apply det_eq_zero_of_col_zero _ ⟨c.val, by have := j.isLt; omega⟩
            intro i; unfold minor skipIdx
            simp only [hlt]
            exact hc (skipIdx ⟨0, Nat.zero_lt_succ m⟩ i)
          rw [hz, mul_zero]
        · have hgt : j.val < c.val := by omega
          have hz : det (minor M ⟨0, Nat.zero_lt_succ m⟩ j) = zᵣ := by
            apply det_eq_zero_of_col_zero _ ⟨c.val - 1, by have := c.isLt; omega⟩
            intro i; unfold minor skipIdx
            have hnot : ¬ (c.val - 1 < j.val) := by omega
            simp only [hnot]
            have hidx : (⟨c.val - 1 + 1, by have := c.isLt; omega⟩ : Fin (m + 1)) = c := Fin.ext (by dsimp only; omega)
            rw [hidx]
            exact hc (skipIdx ⟨0, Nat.zero_lt_succ m⟩ i)
          rw [hz, mul_zero]

/-- Single-entry column Laplace expansion (companion to `det_single_entry_row`). -/
private theorem det_single_entry_col {n : Nat} (M : Mat (n + 1) R) (r c : Fin (n + 1)) (s : R)
    (hc : ∀ i : Fin (n + 1), M i c = if i = r then s else zᵣ) :
    det M = rsign (r.val + c.val) *ᵣ s *ᵣ det (minor M r c) := by
  have hmv := det_moveRowToZero M r
  have hM : det M = rsign r.val *ᵣ det (moveRowToZero M r) := by
    rw [hmv, ← CRing.mul_assoc, rsign_mul_self, CRing.one_mul]
  rw [hM]
  let M' := moveRowToZero M r
  have hM'0c : M' ⟨0, Nat.zero_lt_succ n⟩ c = s := by
    unfold M' moveRowToZero
    simp only [↓reduceDIte]
    rw [hc r]; simp only [↓reduceIte]
  have hM'col : ∀ i : Fin n, M' i.succ c = zᵣ := by
    intro i; unfold M' moveRowToZero
    have hne : i.succ.val ≠ 0 := by simp [Fin.succ]
    simp only [hne, ↓reduceDIte]
    have hner : skipIdx r ⟨i.succ.val - 1, by have := i.isLt; simp [Fin.succ]⟩ ≠ r := by
      have hsucc : i.succ.val = i.val + 1 := Fin.val_succ i
      unfold skipIdx
      by_cases h : i.succ.val - 1 < r.val
      · simp only [h, ↓reduceDIte]; exact fin_ne (by dsimp only; omega)
      · simp only [h, ↓reduceDIte]; exact fin_ne (by dsimp only; omega)
    rw [hc]; simp only [hner, ↓reduceIte]
  have hdetM' : det M' = rsign c.val *ᵣ s *ᵣ det (minor M' ⟨0, Nat.zero_lt_succ n⟩ c) := by
    conv => lhs; unfold det
    rw [sumFin_single c]
    · rw [hM'0c]
    · intro j hj
      have hne : c.val ≠ j.val := fun h => hj (Fin.ext h.symm)
      have hz : det (minor M' ⟨0, Nat.zero_lt_succ n⟩ j) = zᵣ := by
        by_cases hlt : c.val < j.val
        · apply det_eq_zero_of_col_zero _ ⟨c.val, by have := j.isLt; omega⟩
          intro i; unfold minor
          rw [skipIdx_zero]
          have hsc : skipIdx j ⟨c.val, by have := j.isLt; omega⟩ = c := by
            unfold skipIdx; simp only [hlt, ↓reduceDIte]
          rw [hsc]
          exact hM'col i
        · apply det_eq_zero_of_col_zero _ ⟨c.val - 1, by have := c.isLt; omega⟩
          intro i; unfold minor
          rw [skipIdx_zero]
          have hsc : skipIdx j ⟨c.val - 1, by have := c.isLt; omega⟩ = c := by
            unfold skipIdx
            have hnot : ¬ (c.val - 1 < j.val) := by omega
            simp only [hnot, ↓reduceDIte]
            exact Fin.ext (by dsimp only; omega)
          rw [hsc]
          exact hM'col i
      rw [hz, mul_zero]
  have hmin : minor M' ⟨0, Nat.zero_lt_succ n⟩ c = minor M r c := by
    funext i j
    unfold minor M' moveRowToZero
    rw [skipIdx_zero]
    have hne : i.succ.val ≠ 0 := by simp [Fin.succ]
    simp only [hne, ↓reduceDIte]
    have hi : (⟨i.succ.val - 1, by have := i.isLt; simp [Fin.succ]⟩ : Fin n) = i :=
      Fin.ext (by simp [Fin.succ])
    rw [hi]
  rw [hdetM', hmin, rsign_add]
  simp only [CRing.mul_assoc]

private theorem rsign_two_mul (k : Nat) : rsign (R := R) (2 * k) = eᵣ := by
  unfold rsign; simp

/-- Determinant of a matrix bordered on row/col `m + 1` by a single `-1` at `mid` equals `- det(minor M mid mid)`. -/
private theorem det_border_last_unit {m : Nat} (M : Mat (m + 1) R) (mid : Fin (m + 1)) :
    let A : Mat ((m + 1) + 1) R := fun i j =>
      if hi : i.val < m + 1 then
        if hj : j.val < m + 1 then M ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else if i.val = mid.val then -ᵣeᵣ else zᵣ
      else
        if _hj : j.val < m + 1 then (if j.val = mid.val then -ᵣeᵣ else zᵣ)
        else zᵣ
    det A = -ᵣ(det (minor M mid mid)) := by
  intro A
  have hrow : ∀ j : Fin (m + 2), A ⟨m + 1, by omega⟩ j =
      if j = ⟨mid.val, by have := mid.isLt; omega⟩ then -ᵣeᵣ else zᵣ := by
    intro j; unfold A
    have hn : ¬ (m + 1 < m + 1) := Nat.lt_irrefl (m + 1)
    simp only [hn, ↓reduceDIte]
    by_cases hj : j.val < m + 1
    · simp only [hj, ↓reduceDIte]
      by_cases hm : j.val = mid.val
      · have heq : j = ⟨mid.val, by have := mid.isLt; omega⟩ := Fin.ext hm
        simp only [heq, ↓reduceIte]
      · have hne : j ≠ ⟨mid.val, by have := mid.isLt; omega⟩ := fin_ne (by dsimp only; exact hm)
        simp only [hm, hne, ↓reduceIte]
    · have hne : j ≠ ⟨mid.val, by have := mid.isLt; omega⟩ := fin_ne (by dsimp only; have := mid.isLt; omega)
      simp only [hj, hne, ↓reduceDIte, ↓reduceIte]
  rw [det_single_entry_row A ⟨m + 1, by omega⟩ ⟨mid.val, by have := mid.isLt; omega⟩ (-ᵣeᵣ) hrow]
  have hcol : ∀ i : Fin (m + 1), minor A ⟨m + 1, by omega⟩ ⟨mid.val, by have := mid.isLt; omega⟩ i ⟨m, by omega⟩ =
      if i = mid then -ᵣeᵣ else zᵣ := by
    intro i; unfold minor A
    rw [skipIdx_last]
    have hi : i.val < m + 1 := i.isLt
    have hsc : (skipIdx (⟨mid.val, by have := mid.isLt; omega⟩ : Fin (m + 2)) (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))).val = m + 1 := by
      unfold skipIdx
      have hnot : ¬ (m < mid.val) := by have := mid.isLt; omega
      simp only [hnot, ↓reduceDIte]
    have hnotlt : ¬ ((skipIdx (⟨mid.val, by have := mid.isLt; omega⟩ : Fin (m + 2)) (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))).val < m + 1) := by
      rw [hsc]; exact Nat.lt_irrefl _
    simp only [dite_eq_left hi, dite_eq_right hnotlt]
    by_cases him : i = mid
    · subst him; simp only [↓reduceIte]
    · have hne : i.val ≠ mid.val := fun h => him (Fin.ext h)
      simp only [him, hne, ↓reduceIte]
  rw [det_single_entry_col _ mid ⟨m, by omega⟩ (-ᵣeᵣ) hcol]
  have hmin : minor (minor A ⟨m + 1, by omega⟩ ⟨mid.val, by have := mid.isLt; omega⟩) mid ⟨m, by omega⟩ =
              minor M mid mid := by
    funext i j; unfold minor A
    rw [skipIdx_last, skipIdx_last]
    have hi : (skipIdx mid i).val < m + 1 := (skipIdx mid i).isLt
    have hjval : (skipIdx (⟨mid.val, by have := mid.isLt; omega⟩ : Fin (m + 2)) (⟨j.val, by have := j.isLt; omega⟩ : Fin (m + 1))).val =
                 (skipIdx mid j).val := by
      unfold skipIdx
      by_cases h : j.val < mid.val
      · simp only [h, ↓reduceDIte]
      · simp only [h, ↓reduceDIte]
    have hj : (skipIdx (⟨mid.val, by have := mid.isLt; omega⟩ : Fin (m + 2)) (⟨j.val, by have := j.isLt; omega⟩ : Fin (m + 1))).val < m + 1 := by
      rw [hjval]; exact (skipIdx mid j).isLt
    simp only [dite_eq_left hi, dite_eq_left hj]
    have hc : (⟨(skipIdx (⟨mid.val, by have := mid.isLt; omega⟩ : Fin (m + 2)) (⟨j.val, by have := j.isLt; omega⟩ : Fin (m + 1))).val, hj⟩ : Fin (m + 1)) = skipIdx mid j :=
      Fin.ext hjval
    rw [hc]
  rw [hmin]
  have hneg1 : (-ᵣ(eᵣ : R)) *ᵣ (-ᵣ(eᵣ : R)) = eᵣ := by
    rw [neg_mul, mul_neg, neg_neg, CRing.one_mul]
  have hsign : rsign (R := R) (m + 1 + mid.val) *ᵣ (-ᵣeᵣ) *ᵣ (rsign (R := R) (mid.val + m) *ᵣ (-ᵣeᵣ)) = -ᵣeᵣ := by
    have heq : m + 1 + mid.val + (mid.val + m) = 2 * (m + mid.val) + 1 := by omega
    calc rsign (R := R) (m + 1 + mid.val) *ᵣ (-ᵣeᵣ) *ᵣ (rsign (R := R) (mid.val + m) *ᵣ (-ᵣeᵣ))
        = (rsign (R := R) (m + 1 + mid.val) *ᵣ rsign (R := R) (mid.val + m)) *ᵣ ((-ᵣeᵣ) *ᵣ (-ᵣeᵣ)) := by
          simp only [CRing.mul_assoc]; apply congrArg (CRing.mul _)
          rw [mul_left_comm (-ᵣeᵣ) (rsign (mid.val + m))]
      _ = rsign (R := R) (2 * (m + mid.val) + 1) *ᵣ eᵣ := by
          rw [← rsign_add, heq, hneg1]
      _ = -ᵣeᵣ := by
          rw [mul_one, rsign_succ, rsign_two_mul]
  calc rsign (R := R) (m + 1 + mid.val) *ᵣ (-ᵣeᵣ) *ᵣ (rsign (R := R) (mid.val + m) *ᵣ (-ᵣeᵣ) *ᵣ det (minor M mid mid))
      = (rsign (R := R) (m + 1 + mid.val) *ᵣ (-ᵣeᵣ) *ᵣ (rsign (R := R) (mid.val + m) *ᵣ (-ᵣeᵣ))) *ᵣ det (minor M mid mid) := by
        rw [← CRing.mul_assoc]
    _ = (-ᵣeᵣ) *ᵣ det (minor M mid mid) := by rw [hsign]
    _ = -ᵣ(det (minor M mid mid)) := by rw [neg_mul, CRing.one_mul]

/-- Determinant of a matrix bordered on row/col `0` by a single `-1` at `mid + 1` equals `- det(minor M mid mid)`. -/
private theorem det_border_first_unit {m : Nat} (M : Mat (m + 1) R) (mid : Fin (m + 1)) :
    let B : Mat ((m + 1) + 1) R := fun i j =>
      if hi : i.val = 0 then
        if _hj : j.val = 0 then zᵣ
        else if j.val - 1 = mid.val then -ᵣeᵣ else zᵣ
      else
        if _hj : j.val = 0 then (if i.val - 1 = mid.val then -ᵣeᵣ else zᵣ)
        else M ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
    det B = -ᵣ(det (minor M mid mid)) := by
  intro B
  have hrow : ∀ j : Fin (m + 2), B ⟨0, by omega⟩ j =
      if j = mid.succ then -ᵣeᵣ else zᵣ := by
    intro j; unfold B
    simp only [↓reduceDIte]
    by_cases hj : j.val = 0
    · have hne : j ≠ mid.succ := fin_ne (by simp [Fin.succ]; omega)
      simp only [hj, hne, ↓reduceDIte, ↓reduceIte]
    · simp only [hj, ↓reduceDIte]
      by_cases hm : j.val - 1 = mid.val
      · have heq : j = mid.succ := Fin.ext (by simp [Fin.succ]; omega)
        simp only [ite_eq_left hm, ite_eq_left heq]
      · have hne : j ≠ mid.succ := fin_ne (by simp [Fin.succ]; omega)
        simp only [hm, hne, ↓reduceIte]
  rw [det_single_entry_row B ⟨0, by omega⟩ mid.succ (-ᵣeᵣ) hrow]
  have hcol : ∀ i : Fin (m + 1), minor B ⟨0, by omega⟩ mid.succ i ⟨0, by omega⟩ =
      if i = mid then -ᵣeᵣ else zᵣ := by
    intro i; unfold minor B
    rw [skipIdx_zero]
    have hi : i.succ.val ≠ 0 := by simp [Fin.succ]
    have hsc : (skipIdx mid.succ ⟨0, by omega⟩).val = 0 := by
      unfold skipIdx
      have hlt : (0 : Nat) < mid.succ.val := by simp [Fin.succ]
      simp only [hlt, ↓reduceDIte]
    simp only [dite_eq_right hi, dite_eq_left hsc]
    have hsub : i.succ.val - 1 = i.val := by simp [Fin.succ]
    rw [hsub]
    by_cases him : i = mid
    · subst him; simp only [↓reduceIte]
    · have hne : i.val ≠ mid.val := fun h => him (Fin.ext h)
      simp only [him, hne, ↓reduceIte]
  rw [det_single_entry_col _ mid ⟨0, by omega⟩ (-ᵣeᵣ) hcol]
  have hmin : minor (minor B ⟨0, by omega⟩ mid.succ) mid ⟨0, by omega⟩ =
              minor M mid mid := by
    funext i j; unfold minor B
    rw [skipIdx_zero, skipIdx_zero]
    have hi : (skipIdx mid i).succ.val ≠ 0 := by simp [Fin.succ]
    have hjval : (skipIdx mid.succ j.succ).val = (skipIdx mid j).val + 1 := by
      unfold skipIdx; simp only [Fin.succ]
      by_cases h : j.val < mid.val
      · have h' : j.val + 1 < mid.val + 1 := by omega
        simp only [h, h', ↓reduceDIte]
      · have h' : ¬ (j.val + 1 < mid.val + 1) := by omega
        simp only [h, h', ↓reduceDIte]
    have hj : (skipIdx mid.succ j.succ).val ≠ 0 := by omega
    simp only [dite_eq_right hi, dite_eq_right hj]
    have h1 : (⟨(skipIdx mid i).succ.val - 1, by omega⟩ : Fin (m + 1)) = skipIdx mid i := Fin.ext (by simp [Fin.succ])
    have h2 : (⟨(skipIdx mid.succ j.succ).val - 1, by omega⟩ : Fin (m + 1)) = skipIdx mid j := Fin.ext (by dsimp only; omega)
    rw [h1, h2]
  rw [hmin]
  have hneg1 : (-ᵣ(eᵣ : R)) *ᵣ (-ᵣ(eᵣ : R)) = eᵣ := by
    rw [neg_mul, mul_neg, neg_neg, CRing.one_mul]
  have hsign : rsign (R := R) (0 + mid.succ.val) *ᵣ (-ᵣeᵣ) *ᵣ (rsign (R := R) (mid.val + 0) *ᵣ (-ᵣeᵣ)) = -ᵣeᵣ := by
    have heq : 0 + mid.succ.val + (mid.val + 0) = 2 * mid.val + 1 := by simp [Fin.succ]; omega
    calc rsign (R := R) (0 + mid.succ.val) *ᵣ (-ᵣeᵣ) *ᵣ (rsign (R := R) (mid.val + 0) *ᵣ (-ᵣeᵣ))
        = (rsign (R := R) (0 + mid.succ.val) *ᵣ rsign (R := R) (mid.val + 0)) *ᵣ ((-ᵣeᵣ) *ᵣ (-ᵣeᵣ)) := by
          simp only [CRing.mul_assoc]; apply congrArg (CRing.mul _)
          rw [mul_left_comm (-ᵣeᵣ) (rsign (mid.val + 0))]
      _ = rsign (R := R) (2 * mid.val + 1) *ᵣ eᵣ := by
          rw [← rsign_add, heq, hneg1]
      _ = -ᵣeᵣ := by
          rw [mul_one, rsign_succ, rsign_two_mul]
  calc rsign (R := R) (0 + mid.succ.val) *ᵣ (-ᵣeᵣ) *ᵣ (rsign (R := R) (mid.val + 0) *ᵣ (-ᵣeᵣ) *ᵣ det (minor M mid mid))
      = (rsign (R := R) (0 + mid.succ.val) *ᵣ (-ᵣeᵣ) *ᵣ (rsign (R := R) (mid.val + 0) *ᵣ (-ᵣeᵣ))) *ᵣ det (minor M mid mid) := by
        rw [← CRing.mul_assoc]
    _ = (-ᵣeᵣ) *ᵣ det (minor M mid mid) := by rw [hsign]
    _ = -ᵣ(det (minor M mid mid)) := by rw [neg_mul, CRing.one_mul]

theorem det_castHeap (m : Nat) (x : R) : det (castHeap (R := R) m x) = det (inOrderHeapChar (R := R) (m + 1) x) :=
  det_eq_of_dim_eq (heapDim_eq m) _ _ (fun _ _ => rfl)

/-- Theorem 6a (Binary Heap `H_k` Chebyshev-Product Factorization over ANY `CRing R`, `∀ k ≥ 1`):
Reusing `det_junction` from Mechanism A on the bitwise in-order heap `inOrderHeapChar k x`,
both `det(x I - H_k) = T_k(x) * R_{k-1}(x)` and the root-deleted minor `Q_k(x) = T_{k-1}(x) * R_{k-1}(x)`! -/
theorem inOrderHeap_charpoly_pair (x : R) (m : Nat) :
    let root : Fin (heapDim m + 1) := ⟨2 ^ m - 1, by have := heapDim_eq m; have := Nat.two_pow_pos m; have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := (by rw [Nat.pow_succ]; omega); omega⟩
    det (castHeap (R := R) m x) = chebT x (m + 1) *ᵣ heapR x m ∧
    det (minor (castHeap (R := R) m x) root root) = chebT x m *ᵣ heapR x m := by
  induction m with
  | zero =>
    constructor
    · have h1 : det (castHeap (R := R) 0 x) = castHeap (R := R) 0 x ⟨0, by omega⟩ ⟨0, by omega⟩ :=
        det_fin1 (castHeap (R := R) 0 x)
      rw [h1]
      unfold castHeap inOrderHeapChar inOrderHeapAdj chebT heapR rsub
      have hr : heapEdge 1 1 = false := heapEdge_irrefl 1
      simp only [hr, ↓reduceIte, Bool.false_eq_true, neg_zero, add_zero, mul_one]
    · unfold chebT heapR
      change det (minor (castHeap (R := R) 0 x) _ _ : Mat 0 R) = _
      rw [det_fin0, CRing.one_mul]
  | succ m ih =>
    rcases ih with ⟨ihP, ihQ⟩
    let d := heapDim m
    let n := d + 1
    have hn_eq : n = 2 ^ (m + 1) - 1 := heapDim_eq m
    have h2m1 : 2 ^ (m + 1) = n + 1 := by have := Nat.two_pow_pos (m + 1); omega
    have h2m_pos := Nat.two_pow_pos m
    have h2m_lt : 2 ^ m - 1 < n := by have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := (by rw [Nat.pow_succ]; omega); omega
    let mid : Fin (d + 1) := ⟨2 ^ m - 1, h2m_lt⟩
    have h2m : 2 ^ m = mid.val + 1 := by dsimp [mid]; omega
    have hdim : heapDim (m + 1) + 1 = n + 1 + n := by unfold heapDim; dsimp [d, n]; omega
    let Ck : Mat (d + 1) R := castHeap (R := R) m x
    let L : Mat ((d + 1) + 1) R := fun i j =>
      if hi : i.val < n then
        if hj : j.val < n then Ck ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else if i.val = mid.val then -ᵣeᵣ else zᵣ
      else
        if hj : j.val < n then (if j.val = mid.val then -ᵣeᵣ else zᵣ)
        else zᵣ
    let U : Mat ((d + 1) + 1) R := fun i j =>
      if hi : i.val = 0 then
        if hj : j.val = 0 then zᵣ
        else if j.val - 1 = mid.val then -ᵣeᵣ else zᵣ
      else
        if hj : j.val = 0 then (if i.val - 1 = mid.val then -ᵣeᵣ else zᵣ)
        else Ck ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
    have hKeq :
        det (castHeap (R := R) (m + 1) x) =
        det (fun (i j : Fin (n + 1 + n)) =>
          if hi : i.val < n then
            if hj : j.val ≤ n then L ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ else zᵣ
          else if hi2 : i.val = n then
            if hj : j.val < n then L ⟨n, by omega⟩ ⟨j.val, by omega⟩
            else if hj2 : j.val = n then L ⟨n, by omega⟩ ⟨n, by omega⟩ +ᵣ U ⟨0, by omega⟩ ⟨0, by omega⟩ +ᵣ x
            else U ⟨0, by omega⟩ ⟨j.val - n, by omega⟩
          else
            if hj : j.val < n then zᵣ else U ⟨i.val - n, by omega⟩ ⟨j.val - n, by omega⟩) := by
      apply det_eq_of_dim_eq hdim
      intro i j
      have hdim2 : 2 ^ (m + 2) - 1 = n + 1 + n := by rw [← heapDim_eq (m + 1)]; exact hdim
      have hpow2 : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
      unfold castHeap inOrderHeapChar inOrderHeapAdj rsub
      dsimp only
      by_cases hi1 : i.val < n
      · simp only [dite_eq_left hi1]
        by_cases hj1 : j.val < n
        · have hjle : j.val ≤ n := by omega
          simp only [dite_eq_left hjle]
          unfold L; simp only [dite_eq_left hi1, dite_eq_left hj1]
          unfold Ck castHeap inOrderHeapChar inOrderHeapAdj rsub
          dsimp only
          by_cases hij : i.val = j.val
          · have h1 : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) = ⟨j.val, by have := j.isLt; omega⟩ := Fin.ext hij
            have h2 : (⟨i.val, by omega⟩ : Fin (2 ^ (m + 1) - 1)) = ⟨j.val, by omega⟩ := Fin.ext hij
            simp only [ite_eq_left h1, ite_eq_left h2]
          · have h1 : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; exact hij)
            have h2 : (⟨i.val, by omega⟩ : Fin (2 ^ (m + 1) - 1)) ≠ ⟨j.val, by omega⟩ := fin_ne (by dsimp only; exact hij)
            simp only [ite_eq_right h1, ite_eq_right h2]
        · by_cases hj2 : j.val = n
          · have hjle : j.val ≤ n := by omega
            have hne : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
            simp only [dite_eq_left hjle, ite_eq_right hne, CRing.zero_add]
            unfold L; simp only [dite_eq_left hi1, dite_eq_right hj1]
            have hje : j.val + 1 = 2 ^ (m + 1) := by omega
            rw [heapEdge_symm, hje, heapEdge_root_left (by omega) (by omega) (by omega)]
            have hsub : m + 1 - 1 = m := by omega
            rw [hsub]
            by_cases hm : i.val = mid.val
            · have heq : i.val + 1 = 2 ^ m := by omega
              simp only [ite_eq_left hm, decide_eq_true heq, ↓reduceIte]
            · have hnem : i.val + 1 ≠ 2 ^ m := by omega
              have hdf : decide (i.val + 1 = 2 ^ m) = false := decide_eq_false hnem
              simp only [ite_eq_right hm, hdf, Bool.false_eq_true, ↓reduceIte, neg_zero]
          · have hnotle : ¬ (j.val ≤ n) := by omega
            have hne : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
            simp only [dite_eq_right hnotle, ite_eq_right hne, CRing.zero_add]
            have hcr : heapEdge (i.val + 1) (j.val + 1) = false :=
              heapEdge_cross (k := m + 1) (by omega) (by omega) (by omega) (by have := j.isLt; omega)
            simp only [hcr, Bool.false_eq_true, ↓reduceIte, neg_zero]
      · by_cases hi2 : i.val = n
        · simp only [dite_eq_right hi1, dite_eq_left hi2]
          by_cases hj1 : j.val < n
          · have hne : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
            simp only [dite_eq_left hj1, ite_eq_right hne, CRing.zero_add]
            unfold L
            have hnl : ¬ (n < n) := Nat.lt_irrefl n
            simp only [dite_eq_right hnl, dite_eq_left hj1]
            have hie : i.val + 1 = 2 ^ (m + 1) := by omega
            rw [hie, heapEdge_root_left (by omega) (by omega) (by omega)]
            have hsub : m + 1 - 1 = m := by omega
            rw [hsub]
            by_cases hm : j.val = mid.val
            · have heq : j.val + 1 = 2 ^ m := by omega
              simp only [ite_eq_left hm, decide_eq_true heq, ↓reduceIte]
            · have hnem : j.val + 1 ≠ 2 ^ m := by omega
              have hdf : decide (j.val + 1 = 2 ^ m) = false := decide_eq_false hnem
              simp only [ite_eq_right hm, hdf, Bool.false_eq_true, ↓reduceIte, neg_zero]
          · by_cases hj2 : j.val = n
            · have hij : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) = ⟨j.val, by have := j.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
              simp only [dite_eq_right hj1, dite_eq_left hj2, ite_eq_left hij]
              unfold L U
              have hnl : ¬ (n < n) := Nat.lt_irrefl n
              simp only [dite_eq_right hnl, ↓reduceDIte, CRing.zero_add]
              have hir : heapEdge (i.val + 1) (j.val + 1) = false := by rw [hi2, hj2]; exact heapEdge_irrefl _
              simp only [hir, Bool.false_eq_true, ↓reduceIte, neg_zero, add_zero]
            · have hne : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
              simp only [dite_eq_right hj1, dite_eq_right hj2, ite_eq_right hne, CRing.zero_add]
              unfold U
              have hjn0 : j.val - n ≠ 0 := by omega
              simp only [↓reduceDIte, dite_eq_right hjn0]
              have hie : i.val + 1 = 2 ^ (m + 1) := by omega
              rw [hie, heapEdge_root_right (by omega) (by omega) (by have := j.isLt; omega)]
              have hsub : m + 1 - 1 = m := by omega
              rw [hsub]
              by_cases hm : j.val - n - 1 = mid.val
              · have heq : j.val + 1 = 2 ^ (m + 1) + 2 ^ m := by omega
                simp only [ite_eq_left hm, decide_eq_true heq, ↓reduceIte]
              · have hnem : j.val + 1 ≠ 2 ^ (m + 1) + 2 ^ m := by omega
                have hdf : decide (j.val + 1 = 2 ^ (m + 1) + 2 ^ m) = false := decide_eq_false hnem
                simp only [ite_eq_right hm, hdf, Bool.false_eq_true, ↓reduceIte, neg_zero]
        · simp only [dite_eq_right hi1, dite_eq_right hi2]
          by_cases hj1 : j.val < n
          · have hne : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
            simp only [dite_eq_left hj1, ite_eq_right hne, CRing.zero_add]
            have hcr : heapEdge (i.val + 1) (j.val + 1) = false := by
              rw [heapEdge_symm]
              exact heapEdge_cross (k := m + 1) (by omega) (by omega) (by omega) (by have := i.isLt; omega)
            simp only [hcr, Bool.false_eq_true, ↓reduceIte, neg_zero]
          · simp only [dite_eq_right hj1]
            by_cases hj2 : j.val = n
            · have hne : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
              simp only [ite_eq_right hne, CRing.zero_add]
              unfold U
              have hin0 : i.val - n ≠ 0 := by omega
              have hjn0 : j.val - n = 0 := by omega
              simp only [dite_eq_right hin0, dite_eq_left hjn0]
              have hje : j.val + 1 = 2 ^ (m + 1) := by omega
              rw [heapEdge_symm, hje, heapEdge_root_right (by omega) (by omega) (by have := i.isLt; omega)]
              have hsub : m + 1 - 1 = m := by omega
              rw [hsub]
              by_cases hm : i.val - n - 1 = mid.val
              · have heq : i.val + 1 = 2 ^ (m + 1) + 2 ^ m := by omega
                simp only [ite_eq_left hm, decide_eq_true heq, ↓reduceIte]
              · have hnem : i.val + 1 ≠ 2 ^ (m + 1) + 2 ^ m := by omega
                have hdf : decide (i.val + 1 = 2 ^ (m + 1) + 2 ^ m) = false := decide_eq_false hnem
                simp only [ite_eq_right hm, hdf, Bool.false_eq_true, ↓reduceIte, neg_zero]
            · unfold U
              have hin0 : i.val - n ≠ 0 := by omega
              have hjn0 : j.val - n ≠ 0 := by omega
              simp only [dite_eq_right hin0, dite_eq_right hjn0]
              unfold Ck castHeap inOrderHeapChar inOrderHeapAdj rsub
              dsimp only
              have hsh : heapEdge (i.val + 1) (j.val + 1) = heapEdge (i.val - n - 1 + 1) (j.val - n - 1 + 1) := by
                have h1 := heapEdge_shift_right (k := m + 1) (u := i.val + 1) (v := j.val + 1)
                  (by omega) (by have := i.isLt; omega) (by omega) (by have := j.isLt; omega)
                have ha : i.val + 1 - 2 ^ (m + 1) = i.val - n - 1 + 1 := by omega
                have hb : j.val + 1 - 2 ^ (m + 1) = j.val - n - 1 + 1 := by omega
                rw [ha, hb] at h1
                exact h1
              rw [hsh]
              by_cases hij : i.val = j.val
              · have h1 : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) = ⟨j.val, by have := j.isLt; omega⟩ := Fin.ext hij
                have h2 : (⟨i.val - n - 1, by omega⟩ : Fin (2 ^ (m + 1) - 1)) = ⟨j.val - n - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
                simp only [ite_eq_left h1, ite_eq_left h2]
              · have h1 : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; exact hij)
                have h2 : (⟨i.val - n - 1, by omega⟩ : Fin (2 ^ (m + 1) - 1)) ≠ ⟨j.val - n - 1, by omega⟩ := fin_ne (by dsimp only; omega)
                simp only [ite_eq_right h1, ite_eq_right h2]
    have hdetL : det L = -ᵣ(det (minor Ck mid mid)) := det_border_last_unit Ck mid
    have hdetU : det U = -ᵣ(det (minor Ck mid mid)) := det_border_first_unit Ck mid
    have hminL : minor L ⟨n, Nat.lt_succ_self n⟩ ⟨n, Nat.lt_succ_self n⟩ = Ck := by
      funext i j; unfold minor L; rw [skipIdx_last, skipIdx_last]
      have hi : i.val < n := i.isLt
      have hj : j.val < n := j.isLt
      simp only [dite_eq_left hi, dite_eq_left hj]
    have hminU : minor U ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩ = Ck := by
      funext i j; unfold minor U; rw [skipIdx_zero, skipIdx_zero]
      have hi : i.succ.val ≠ 0 := by simp [Fin.succ]
      have hj : j.succ.val ≠ 0 := by simp [Fin.succ]
      simp only [dite_eq_right hi, dite_eq_right hj]; rfl
    have hPstep : det (castHeap (R := R) (m + 1) x) =
        x *ᵣ (det Ck *ᵣ det Ck) -ᵣ (eᵣ +ᵣ eᵣ) *ᵣ (det Ck *ᵣ det (minor Ck mid mid)) := by
      rw [hKeq, det_junction L U x, hdetL, hdetU, hminL, hminU]
      unfold rsub
      rw [neg_mul, mul_neg, CRing.mul_comm (det (minor Ck mid mid)) (det Ck),
          right_distrib, CRing.one_mul, neg_add, CRing.add_comm]
    have hQstep :
        det (minor (castHeap (R := R) (m + 1) x)
          ⟨2 ^ (m + 1) - 1, by have := heapDim_eq (m + 1); have := Nat.two_pow_pos (m + 1); have : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := (by rw [Nat.pow_succ]; omega); omega⟩
          ⟨2 ^ (m + 1) - 1, by have := heapDim_eq (m + 1); have := Nat.two_pow_pos (m + 1); have : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := (by rw [Nat.pow_succ]; omega); omega⟩) =
        det Ck *ᵣ det Ck := by
      have hdimQ : heapDim (m + 1) = n + n := by unfold heapDim; dsimp [d, n]; omega
      let Mblk : Mat (n + n) R := fun i j =>
        if hi : i.val < n then
          if hj : j.val < n then Ck ⟨i.val, hi⟩ ⟨j.val, hj⟩ else zᵣ
        else
          if hj : j.val < n then zᵣ else Ck ⟨i.val - n, by omega⟩ ⟨j.val - n, by omega⟩
      have hMeq :
          det (minor (castHeap (R := R) (m + 1) x)
            ⟨2 ^ (m + 1) - 1, by have := heapDim_eq (m + 1); have := Nat.two_pow_pos (m + 1); have : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := (by rw [Nat.pow_succ]; omega); omega⟩
            ⟨2 ^ (m + 1) - 1, by have := heapDim_eq (m + 1); have := Nat.two_pow_pos (m + 1); have : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := (by rw [Nat.pow_succ]; omega); omega⟩) =
          det Mblk := by
        apply det_eq_of_dim_eq hdimQ
        intro i j
        have hdim2 : 2 ^ (m + 2) - 1 = n + 1 + n := by rw [← heapDim_eq (m + 1)]; exact hdim
        have hpow2 : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
        unfold minor Mblk castHeap inOrderHeapChar inOrderHeapAdj rsub skipIdx
        dsimp only
        by_cases hi : i.val < n <;> by_cases hj : j.val < n
        · have hi' : i.val < 2 ^ (m + 1) - 1 := by omega
          have hj' : j.val < 2 ^ (m + 1) - 1 := by omega
          simp only [dite_eq_left hi, dite_eq_left hj, dite_eq_left hi', dite_eq_left hj']
          unfold Ck castHeap inOrderHeapChar inOrderHeapAdj rsub
          dsimp only
          by_cases hij : i.val = j.val
          · have h1 : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) = ⟨j.val, by have := j.isLt; omega⟩ := Fin.ext hij
            have h2 : (⟨i.val, by omega⟩ : Fin (2 ^ (m + 1) - 1)) = ⟨j.val, by omega⟩ := Fin.ext hij
            simp only [ite_eq_left h1, ite_eq_left h2]
          · have h1 : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; exact hij)
            have h2 : (⟨i.val, by omega⟩ : Fin (2 ^ (m + 1) - 1)) ≠ ⟨j.val, by omega⟩ := fin_ne (by dsimp only; exact hij)
            simp only [ite_eq_right h1, ite_eq_right h2]
        · have hi' : i.val < 2 ^ (m + 1) - 1 := by omega
          have hj' : ¬ (j.val < 2 ^ (m + 1) - 1) := by omega
          simp only [dite_eq_left hi, dite_eq_right hj, dite_eq_left hi', dite_eq_right hj']
          have hne : (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val + 1, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
          have hcr : heapEdge (i.val + 1) (j.val + 1 + 1) = false :=
            heapEdge_cross (k := m + 1) (by omega) (by omega) (by omega) (by have := j.isLt; omega)
          simp only [ite_eq_right hne, hcr, Bool.false_eq_true, ↓reduceIte, neg_zero, add_zero]
        · have hi' : ¬ (i.val < 2 ^ (m + 1) - 1) := by omega
          have hj' : j.val < 2 ^ (m + 1) - 1 := by omega
          simp only [dite_eq_right hi, dite_eq_left hj, dite_eq_right hi', dite_eq_left hj']
          have hne : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
          have hcr : heapEdge (i.val + 1 + 1) (j.val + 1) = false := by
            rw [heapEdge_symm]
            exact heapEdge_cross (k := m + 1) (by omega) (by omega) (by omega) (by have := i.isLt; omega)
          simp only [ite_eq_right hne, hcr, Bool.false_eq_true, ↓reduceIte, neg_zero, add_zero]
        · have hi' : ¬ (i.val < 2 ^ (m + 1) - 1) := by omega
          have hj' : ¬ (j.val < 2 ^ (m + 1) - 1) := by omega
          simp only [dite_eq_right hi, dite_eq_right hj, dite_eq_right hi', dite_eq_right hj']
          unfold Ck castHeap inOrderHeapChar inOrderHeapAdj rsub
          dsimp only
          have hsh : heapEdge (i.val + 1 + 1) (j.val + 1 + 1) = heapEdge (i.val - n + 1) (j.val - n + 1) := by
            have h1 := heapEdge_shift_right (k := m + 1) (u := i.val + 1 + 1) (v := j.val + 1 + 1)
              (by omega) (by have := i.isLt; omega) (by omega) (by have := j.isLt; omega)
            have ha : i.val + 1 + 1 - 2 ^ (m + 1) = i.val - n + 1 := by omega
            have hb : j.val + 1 + 1 - 2 ^ (m + 1) = j.val - n + 1 := by omega
            rw [ha, hb] at h1
            exact h1
          rw [hsh]
          by_cases hij : i.val = j.val
          · have h1 : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) = ⟨j.val + 1, by have := j.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
            have h2 : (⟨i.val - n, by omega⟩ : Fin (2 ^ (m + 1) - 1)) = ⟨j.val - n, by omega⟩ := Fin.ext (by dsimp only; omega)
            simp only [ite_eq_left h1, ite_eq_left h2]
          · have h1 : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (2 ^ (m + 2) - 1)) ≠ ⟨j.val + 1, by have := j.isLt; omega⟩ := fin_ne (by dsimp only; omega)
            have h2 : (⟨i.val - n, by omega⟩ : Fin (2 ^ (m + 1) - 1)) ≠ ⟨j.val - n, by omega⟩ := fin_ne (by dsimp only; omega)
            simp only [ite_eq_right h1, ite_eq_right h2]
      rw [hMeq]
      have hbl := det_blockLower Mblk (fun i j => by
        unfold Mblk
        have hi : i.val < n := i.isLt
        have hj : ¬ (n + j.val < n) := by omega
        simp only [dite_eq_left hi, dite_eq_right hj])
      rw [hbl]
      have hTL : (fun i j : Fin n => Mblk ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) = Ck := by
        funext i j; unfold Mblk; simp only [dite_eq_left i.isLt, dite_eq_left j.isLt]; rfl
      have hBR : (fun i j : Fin n => Mblk ⟨n + i.val, by omega⟩ ⟨n + j.val, by omega⟩) = Ck := by
        funext i j; unfold Mblk
        have hi : ¬ (n + i.val < n) := by omega
        have hj : ¬ (n + j.val < n) := by omega
        simp only [dite_eq_right hi, dite_eq_right hj]
        congr 1 <;> (exact Fin.ext (by dsimp only; omega))
      rw [hTL, hBR]
    constructor
    · rw [hPstep, ihP, ihQ]
      have hT : chebT x (m + 2) = x *ᵣ chebT x (m + 1) -ᵣ (eᵣ +ᵣ eᵣ) *ᵣ chebT x m := rfl
      have hR : heapR x (m + 1) = chebT x (m + 1) *ᵣ (heapR x m *ᵣ heapR x m) := rfl
      rw [hT, hR]
      unfold rsub
      let T1 := chebT x (m + 1)
      let T0 := chebT x m
      let Rm := heapR x m
      change x *ᵣ ((T1 *ᵣ Rm) *ᵣ (T1 *ᵣ Rm)) +ᵣ -ᵣ((eᵣ +ᵣ eᵣ) *ᵣ ((T1 *ᵣ Rm) *ᵣ (T0 *ᵣ Rm))) =
             (x *ᵣ T1 +ᵣ -ᵣ((eᵣ +ᵣ eᵣ) *ᵣ T0)) *ᵣ (T1 *ᵣ (Rm *ᵣ Rm))
      conv => rhs; rw [right_distrib, neg_mul]
      congr 1
      · simp only [CRing.mul_assoc]
        apply congrArg (CRing.mul x)
        apply congrArg (CRing.mul T1)
        rw [mul_left_comm Rm T1]
      · apply congrArg CRing.neg
        simp only [CRing.mul_assoc]
        apply congrArg (CRing.mul (eᵣ +ᵣ eᵣ))
        rw [mul_left_comm Rm T0, mul_left_comm T1 T0]
    · rw [hQstep, ihP]
      have hR : heapR x (m + 1) = chebT x (m + 1) *ᵣ (heapR x m *ᵣ heapR x m) := rfl
      rw [hR]
      let T1 := chebT x (m + 1)
      let Rm := heapR x m
      change (T1 *ᵣ Rm) *ᵣ (T1 *ᵣ Rm) = T1 *ᵣ (T1 *ᵣ (Rm *ᵣ Rm))
      simp only [CRing.mul_assoc]
      apply congrArg (CRing.mul T1)
      rw [mul_left_comm Rm T1]

/-- Theorem 6b (Binary Heap `H_k` Characteristic Polynomial Factorization over ANY `CRing R`, `∀ k ≥ 1`): -/
theorem inOrderHeap_charpoly_factorization (x : R) (k : Nat) (hk : 1 ≤ k) :
    det (inOrderHeapChar (R := R) k x) = chebT x k *ᵣ heapR x (k - 1) := by
  rcases (⟨k - 1, by omega⟩ : ∃ m, k = m + 1) with ⟨m, rfl⟩
  have h := (inOrderHeap_charpoly_pair (R := R) x m).1
  rw [det_castHeap] at h
  have hsub : m + 1 - 1 = m := by omega
  rw [hsub]
  exact h

/-- Theorem 6c (Exact Polynomial-Ring `Z[X]` Factorization of Binary Heap `H_k` via `FPS`): -/
theorem inOrderHeap_charpoly_fps (k : Nat) (hk : 1 ≤ k) :
    det (inOrderHeapChar (R := FPS) k FPS.X) = chebT FPS.X k *ᵣ heapR FPS.X (k - 1) :=
  inOrderHeap_charpoly_factorization (R := FPS) FPS.X k hk

/-- Corollary 6d (Universal Singularity of Complete Binary Heaps): `det(H_k) = 0` for ALL `k ≥ 1`! -/
theorem inOrderHeap_char_zero (k : Nat) (hk : 1 ≤ k) :
    det (inOrderHeapChar (R := R) k zᵣ) = zᵣ := by
  rw [inOrderHeap_charpoly_factorization zᵣ k hk]
  match k with
  | 0 => omega
  | 1 =>
    unfold chebT heapR
    exact zero_mul eᵣ
  | n + 2 =>
    have hR : ∀ t : Nat, heapR (R := R) zᵣ (t + 1) = zᵣ := by
      intro t
      induction t with
      | zero =>
        unfold heapR chebT
        exact zero_mul _
      | succ t iht =>
        unfold heapR
        rw [iht, zero_mul, mul_zero]
    rw [show n + 2 - 1 = n + 1 by omega, hR n, mul_zero]

end BinaryHeapFamily
end MainTheorems
section WitnessesAndSharpness
/-- Witness 1: `A(G_2(1))` (5×5) has `det = -4` and unimodular minor `+1`. -/
theorem witness_fenwickUQ_k2 :
    det (fenwickUQAdj (R := Int) 2 1) = -4 ∧
    det (minor (fenwickUQAdj (R := Int) 2 1) ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩) = 1 :=
  ⟨fenwickUQ_det_const_int 2 (by omega), fenwickUQ_unimodular (R := Int) 1 2 (by omega)⟩

/-- Witness 2: `A(G_3(1))` (9×9) has `det = -4` and Farey chord `det = -2`. -/
theorem witness_fenwickUQ_k3 :
    det (fenwickUQAdj (R := Int) 3 1) = -4 ∧
    det (perturb (castPortal (by omega : 1 ≤ 3) (fenwickUQAdj (R := Int) 3 1)) 0 1 1 0) = -2 := by
  refine ⟨fenwickUQ_det_const_int 3 (by omega), ?_⟩
  have h := farey_det_const (R := Int) 1 3 (by omega)
  rw [rnat_int] at h
  exact h

/-- Witness 3: Laplacian `x = 2` spectral collapse at `k = 3`: `det(2I - L(G_3)) = -14` and `det(2I - Q(G_3)) = -6`. -/
theorem witness_eval_two_k3 :
    det (fenwickUQLapChar (R := Int) 3 2) = -14 ∧
    det (fenwickUQSignlessChar (R := Int) 3 2) = -6 := by
  constructor
  · rw [fenwickUQLap_eval_two 3 (by omega)]; decide
  · rw [fenwickUQSignless_eval_two 3 (by omega)]; decide

/-- Witness 4: Spanning trees & dyadic resistance at `k = 3`: `τ_3 = 441 = 21^2`, `d_3 = 504`, `7 * 504 = 8 * 441`. -/
theorem witness_spanning_trees_k3 :
    tauSeq 3 = 441 ∧ dSeq 3 = 504 ∧ ((2 : Int) ^ 3 - 1) * dSeq 3 = (2 : Int) ^ 3 * tauSeq 3 :=
  ⟨rfl, rfl, fenwickUQLap_effective_resistance 3 (by omega)⟩

/-- Witness 5: Non-power-of-two even Fenwick matrix `B_6` (`m = 3`) is invertible over `ℤ` via `interleaveInv`! -/
theorem witness_B6_inv :
    matMul (fenwickB (R := Int) 6) (interleaveInv (fenwickB (R := Int) 3)) = matId 6 :=
  fenwickB_closed_form_inv (R := Int) 3

/-- Witness 6: Exact 1/4-dyadic inverse `A(G_2) * J_2 = 4 * I_5` and `A(G_3) * J_3 = 4 * I_9`. -/
theorem witness_dyadic_inv_k2 :
    matMul (fenwickUQAdj (R := Int) 2 1) (fenwickUQDyadicInv 2 (by omega)) =
    fun i j => if i = j then (4 : Int) else 0 :=
  fenwickUQ_dyadic_inv 2 (by omega)

/-- Witness 7: Binary heap `H_3` (7×7) characteristic polynomial evaluated at `x = 3`:
`det(3 I - H_3) = T_3(3) * R_2(3) = 15 * (7 * 3^2) = 945`! -/
theorem witness_binaryHeap_k3 :
    det (inOrderHeapChar (R := Int) 3 3) = 945 := by
  rw [inOrderHeap_charpoly_factorization (R := Int) 3 3 (by omega)]
  decide

/-! ### 9.2 Kernel-Checked Sharpness Counterexamples (Falsifying Relaxed Hypotheses) -/

/-- Sharpness 1 (`k ≥ 2` is sharp for `det(A(G_k)) = -4`): at `k = 1`, `det(A(G_1)) = 0 ≠ -4`! -/
theorem sharpness_k1_fails_const :
    det (fenwickUQAdj (R := Int) 1 1) = 0 ∧ det (fenwickUQAdj (R := Int) 1 1) ≠ -4 := by
  have h0 : det (fenwickUQAdj (R := Int) 1 1) = 0 := by
    rw [← det_castPortal (Nat.le_refl 1)]
    exact congrArg PortalState.d0 (portalTuple_fenwickUQAdj_one (R := Int) 1)
  exact ⟨h0, by omega⟩

/-- Sharpness 2 (Even dimension `2m` is sharp for unimodularity of `B_n`):
at odd `n = 3`, `det(B_3) = 0 ≠ 1`! -/
theorem sharpness_odd_B3_singular :
    det (fenwickB (R := Int) 3) = 0 := by
  have hlb1 : lowbit 1 = 1 := lowbit_odd (by omega)
  have hlb2 : lowbit 2 = 2 := by rw [lowbit_even (by omega) (by omega), lowbit_odd (by omega)]
  have hlb3 : lowbit 3 = 1 := lowbit_odd (by omega)
  rw [det_fin3]
  have h00 : fenwickB (R := Int) 3 ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by unfold fenwickB fenwickEdge; simp only [hlb1]; rfl
  have h01 : fenwickB (R := Int) 3 ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 := by unfold fenwickB fenwickEdge; simp only [hlb1, hlb2]; rfl
  have h02 : fenwickB (R := Int) 3 ⟨0, by omega⟩ ⟨2, by omega⟩ = 0 := by unfold fenwickB fenwickEdge; simp only [hlb1, hlb3]; rfl
  have h10 : fenwickB (R := Int) 3 ⟨1, by omega⟩ ⟨0, by omega⟩ = 1 := by unfold fenwickB fenwickEdge; simp only [hlb1, hlb2]; rfl
  have h11 : fenwickB (R := Int) 3 ⟨1, by omega⟩ ⟨1, by omega⟩ = 0 := by unfold fenwickB fenwickEdge; simp only [hlb2]; rfl
  have h12 : fenwickB (R := Int) 3 ⟨1, by omega⟩ ⟨2, by omega⟩ = 0 := by unfold fenwickB fenwickEdge; simp only [hlb2, hlb3]; rfl
  have h20 : fenwickB (R := Int) 3 ⟨2, by omega⟩ ⟨0, by omega⟩ = 0 := by unfold fenwickB fenwickEdge; simp only [hlb1, hlb3]; rfl
  have h21 : fenwickB (R := Int) 3 ⟨2, by omega⟩ ⟨1, by omega⟩ = 0 := by unfold fenwickB fenwickEdge; simp only [hlb2, hlb3]; rfl
  have h22 : fenwickB (R := Int) 3 ⟨2, by omega⟩ ⟨2, by omega⟩ = 0 := by unfold fenwickB fenwickEdge; simp only [hlb3]; rfl
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  rfl

/-- Sharpness 3 (Equal query/update base weights are sharp):
giving query edges `(i, i - lowbit i)` weight `1` and update edges `(i, i + lowbit i)` weight `2`
gives `det = -24 ≠ -4` already at `k = 2` (`5 × 5`)! -/
theorem sharpness_asymmetric_weights_k2 :
    let st1 : PortalState Int := ⟨0, -4, -1, 0, 2, 2⟩
    let st1L := stepPerturb st1 0 1 1 0
    let st1R := stepPerturb st1 0 2 2 0
    (stepGlue st1L st1R 0).d0 = -24 ∧ (stepGlue st1L st1R 0).d0 ≠ -4 := by
  refine ⟨by decide, by decide⟩

end WitnessesAndSharpness
end SpecMat7
