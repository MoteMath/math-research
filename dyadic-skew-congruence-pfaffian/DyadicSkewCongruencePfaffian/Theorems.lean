import DyadicSkewCongruencePfaffian.Defs

namespace SiliconPfaffian
theorem pfaffian_blockUpperId {p q r : Nat} (hpq : p + q = 2 * r)
    (X : Fin p → Fin q → Int) {A : Mat (2 * r)} (hA : IsSkew A) :
    pfaffian r (congruence (castMat hpq (blockUpperId X)) A) = pfaffian r A := by
  by_cases hp0 : p = 0
  · have hid : castMat hpq (blockUpperId X) = matId (2 * r) := by
      funext i j; unfold castMat blockUpperId matId
      have : ¬ (i.val < p) := by omega
      simp [this, Fin.ext_iff]
    rw [hid, congruence_id]
  · -- Build blockUpperId X one entry at a time via k = 0 .. p * q
    let pref (k : Nat) : Mat (2 * r) := fun i j =>
      (if i = j then 1 else 0) +
      if hi : i.val < p then
        if hj : j.val < p then 0
        else if (j.val - p) * p + i.val < k then X ⟨i.val, hi⟩ ⟨j.val - p, by omega⟩ else 0
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
        have hp_pos : 0 < p := by omega
        let jj : Nat := k / p
        let ii : Nat := k % p
        have hii : ii < p := Nat.mod_lt k hp_pos
        have hjj : jj < q := by
          dsimp [jj]
          exact Nat.div_lt_of_lt_mul (by omega)
        have hdecomp : jj * p + ii = k := by
          dsimp [jj, ii]; have := Nat.div_add_mod k p; rw [Nat.mul_comm] at this; exact this
        let a : Fin (2 * r) := ⟨p + jj, by omega⟩
        let b : Fin (2 * r) := ⟨ii, by omega⟩
        have hab : a ≠ b := fin_ne_of_val (by dsimp [a, b]; have := Nat.le_add_right p jj; omega)
        have hmul : pref (k + 1) = matMul (pref k) (elemShear a b (X ⟨ii, hii⟩ ⟨jj, hjj⟩)) := by
          funext row col
          rw [matMul_elemShear_right]
          have hcolb : pref k row b = if row = b then 1 else 0 := by
            dsimp only [pref, b]
            by_cases hr : row.val < p <;> simp [hr, hii]
          rw [hcolb]
          dsimp only [pref, a, b]
          by_cases hr : row.val < p <;> by_cases hc : col.val < p
          · have hne : col ≠ ⟨p + jj, by omega⟩ := fin_ne_of_val (by dsimp; have := Nat.le_add_right p jj; omega)
            simp [hr, hc, hne]
          · by_cases hca : col = ⟨p + jj, by omega⟩
            · have hcv : col.val = p + jj := congrArg Fin.val hca
              have hcsub : col.val - p = jj := by omega
              by_cases hrb : row = ⟨ii, by omega⟩
              · have hrv : row.val = ii := congrArg Fin.val hrb
                have hidx : (col.val - p) * p + row.val = k := by rw [hcsub, hrv, hdecomp]
                have hlt1 : (col.val - p) * p + row.val < k + 1 := by omega
                have hlt0 : ¬ ((col.val - p) * p + row.val < k) := by omega
                have hX : X ⟨row.val, hr⟩ ⟨col.val - p, by omega⟩ = X ⟨ii, hii⟩ ⟨jj, hjj⟩ := by
                  congr 1 <;> (apply Fin.ext; dsimp; omega)
                simp only [hr, hc, ↓reduceDIte, hlt1, hlt0, ↓reduceIte, hX]
                simp only [hca, hrb, ↓reduceIte, Int.mul_one, Int.add_zero]
              · have hrv : row.val ≠ ii := fun h => hrb (Fin.ext h)
                have hneq : (col.val - p) * p + row.val ≠ k := by rw [hcsub]; omega
                have hiff : ((col.val - p) * p + row.val < k + 1) ↔ ((col.val - p) * p + row.val < k) := by omega
                simp only [hr, hc, ↓reduceDIte, hiff]
                simp only [hca, hrb, ↓reduceIte, Int.mul_zero, Int.add_zero]
            · have hcv : col.val ≠ p + jj := fun h => hca (Fin.ext h)
              have hcne : col.val - p ≠ jj := by omega
              have hneq : (col.val - p) * p + row.val ≠ k := by
                intro heq
                have h1 : (col.val - p) * p + row.val = jj * p + ii := by omega
                by_cases hlt : col.val - p < jj
                · have hle : (col.val - p + 1) * p ≤ jj * p := Nat.mul_le_mul_right p (by omega)
                  rw [Nat.add_mul, Nat.one_mul] at hle; omega
                · have hle : (jj + 1) * p ≤ (col.val - p) * p := Nat.mul_le_mul_right p (by omega)
                  rw [Nat.add_mul, Nat.one_mul] at hle; omega
              have hiff : ((col.val - p) * p + row.val < k + 1) ↔ ((col.val - p) * p + row.val < k) := by omega
              simp only [hr, hc, ↓reduceDIte, hiff]
              simp only [hca, ↓reduceIte, Int.add_zero]
          · have hne1 : col ≠ ⟨p + jj, by omega⟩ := fin_ne_of_val (by dsimp; have := Nat.le_add_right p jj; omega)
            simp [hr, hne1]
          · have hne2 : row ≠ ⟨ii, by omega⟩ := fin_ne_of_val (by dsimp; omega)
            simp [hr, hne2]
        rw [hmul, congruence_comp, pfaffian_elemShear_congruence a b hab _ (isSkew_congruence _ _ hA)]
        exact ih (by omega)
    have hfull : pref (p * q) = castMat hpq (blockUpperId X) := by
      funext i j; dsimp only [pref]; unfold castMat blockUpperId
      by_cases hi : i.val < p <;> by_cases hj : j.val < p
      · simp [hi, hj, Fin.ext_iff]
      · have hlt : (j.val - p) * p + i.val < p * q := by
          have hjq : j.val - p + 1 ≤ q := by omega
          have h1 : (j.val - p) * p + p = (j.val - p + 1) * p := by
            rw [Nat.add_mul, Nat.one_mul]
          have h2 : (j.val - p + 1) * p ≤ q * p := Nat.mul_le_mul_right p hjq
          rw [Nat.mul_comm q p] at h2
          omega
        simp [hi, hj, hlt, Fin.ext_iff]
      · simp [hi, Fin.ext_iff]
      · simp [hi, Fin.ext_iff]
    rw [← hfull]
    exact hstep (p * q) (Nat.le_refl _)

theorem pfaffian_blockSchur_top {m n : Nat}
    (A00 : Mat (2 * m)) (A01 : Fin (2 * m) → Fin (2 * n) → Int) (A11 : Mat (2 * n))
    (h00 : IsSkew A00) (h11 : IsSkew A11)
    (d : Int) (X : Fin (2 * m) → Fin (2 * n) → Int)
    (hcert : ∀ i j, matMul A00 X i j + d * A01 i j = 0) :
    d ^ (2 * n) * pfaffian (m + n) (castMat (by omega) (blockMat A00 A01 (fun i j => -A01 j i) A11)) =
    pfaffian m A00 * pfaffian n (fun i j => d * d * A11 i j - d * matMul (matTrans A01) X i j) := by
  let A : Mat (2 * (m + n)) := castMat (by omega) (blockMat A00 A01 (fun i j => -A01 j i) A11)
  have hA : IsSkew A := by
    constructor
    · intro i; dsimp only [A]; unfold castMat blockMat
      by_cases hi : i.val < 2 * m <;> simp [hi, h00.1, h11.1]
    · intro i j; dsimp only [A]; unfold castMat blockMat
      by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
      · simp only [hi, hj, ↓reduceDIte]; exact h00.2 _ _
      · simp only [hi, hj, ↓reduceDIte, Int.neg_neg]
      · simp only [hi, hj, ↓reduceDIte]
      · simp only [hi, hj, ↓reduceDIte]; exact h11.2 _ _
  -- Step 1: scale bottom-right indices by d
  let sc : Fin (2 * (m + n)) → Int := fun i => if i.val < 2 * m then 1 else d
  have hprod_sc : prodFin sc = d ^ (2 * n) := by
    rw [← prodFin_cast (show 2 * m + 2 * n = 2 * (m + n) by omega) sc]
    rw [prodFin_split]
    have hL : prodFin (fun i : Fin (2 * m) => sc ⟨i.val, by omega⟩) = 1 := by
      have : prodFin (fun i : Fin (2 * m) => sc ⟨i.val, by omega⟩) = prodFin (fun _ : Fin (2 * m) => (1 : Int)) :=
        prodFin_congr (fun i => by dsimp only [sc]; simp [i.isLt])
      rw [this, prodFin_const]; exact Int.one_pow
    have hR : prodFin (fun j : Fin (2 * n) => sc ⟨2 * m + j.val, by omega⟩) = d ^ (2 * n) := by
      have : prodFin (fun j : Fin (2 * n) => sc ⟨2 * m + j.val, by omega⟩) = prodFin (fun _ : Fin (2 * n) => d) :=
        prodFin_congr (fun j => by
          dsimp only [sc]
          have hnj : ¬ ((⟨2 * m + j.val, by omega⟩ : Fin (2 * (m + n))).val < 2 * m) := by dsimp; omega
          simp only [hnj, ↓reduceIte])
      rw [this, prodFin_const]
    rw [hL, hR, Int.one_mul]
  have hdiag : d ^ (2 * n) * pfaffian (m + n) A = pfaffian (m + n) (diagCong sc A) := by
    rw [pfaffian_diagCong, hprod_sc]
  rw [hdiag]
  -- Step 2: apply blockUpperId X to diagCong sc A
  have hskew_sc : IsSkew (diagCong sc A) := by
    constructor
    · intro i; unfold diagCong; rw [hA.1 i]; simp
    · intro i j; unfold diagCong; rw [hA.2 i j]; rw [Int.mul_neg, Int.neg_mul]; ac_rfl
  rw [← pfaffian_blockUpperId (show 2 * m + 2 * n = 2 * (m + n) by omega) X hskew_sc]
  -- Step 3: evaluate congruence (castMat _ (blockUpperId X)) (diagCong sc A) = blockDiag A00 S
  let S : Mat (2 * n) := fun i j => d * d * A11 i j - d * matMul (matTrans A01) X i j
  have hcong : congruence (castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockUpperId X)) (diagCong sc A) =
               castMat (by omega) (blockDiag A00 S) := by
    funext i j
    unfold congruence matMul matTrans
    -- Evaluate inner sum: (diagCong sc A * U) k j
    have hU : ∀ k l : Fin (2 * (m + n)),
        castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockUpperId X) k l =
        (if k = l then 1 else 0) +
        (if hk : k.val < 2 * m then
          if hl : l.val < 2 * m then 0 else X ⟨k.val, hk⟩ ⟨l.val - 2 * m, by omega⟩
        else 0) := by
      intro k l; unfold castMat blockUpperId; simp [Fin.ext_iff]
    have hright : ∀ k : Fin (2 * (m + n)),
        sumFin (fun l => diagCong sc A k l *
          castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockUpperId X) l j) =
        diagCong sc A k j +
        if hj : j.val < 2 * m then 0
        else sumFin (fun l : Fin (2 * m) => diagCong sc A k ⟨l.val, by omega⟩ * X l ⟨j.val - 2 * m, by omega⟩) := by
      intro k
      have hsp : ∀ l : Fin (2 * (m + n)),
          diagCong sc A k l * castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockUpperId X) l j =
          diagCong sc A k l * (if l = j then 1 else 0) +
          diagCong sc A k l * (if hl : l.val < 2 * m then
            if hj : j.val < 2 * m then 0 else X ⟨l.val, hl⟩ ⟨j.val - 2 * m, by omega⟩ else 0) := by
        intro l; rw [hU l j, Int.mul_add]
      rw [sumFin_congr hsp, sumFin_add]
      rw [sumFin_single j _ (fun l hl => by simp [hl])]
      simp only [↓reduceIte, Int.mul_one]
      congr 1
      by_cases hj : j.val < 2 * m
      · simp only [hj, ↓reduceDIte]
        exact sumFin_eq_zero (fun l => by by_cases hl : l.val < 2 * m <;> simp [hl])
      · simp only [hj, ↓reduceDIte]
        rw [← sumFin_cast (show 2 * m + 2 * n = 2 * (m + n) by omega)]
        rw [sumFin_split]
        rw [← Int.add_zero (sumFin (fun l : Fin (2 * m) => diagCong sc A k ⟨l.val, by omega⟩ * X l ⟨j.val - 2 * m, by omega⟩))]
        congr 1
        · exact sumFin_congr (fun l => by simp [l.isLt])
        · exact sumFin_eq_zero (fun l => by
            dsimp only
            have hnl : ¬ (2 * m + l.val < 2 * m) := by omega
            simp only [hnl, ↓reduceDIte, Int.mul_zero])
    simp only [hright]
    -- Now split outer sum over k similarly!
    have hleft : ∀ f : Fin (2 * (m + n)) → Int,
        sumFin (fun k => castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockUpperId X) k i * f k) =
        f i + if hi : i.val < 2 * m then 0
              else sumFin (fun k : Fin (2 * m) => X k ⟨i.val - 2 * m, by omega⟩ * f ⟨k.val, by omega⟩) := by
      intro f
      have hsp : ∀ k : Fin (2 * (m + n)),
          castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockUpperId X) k i * f k =
          (if k = i then 1 else 0) * f k +
          (if hk : k.val < 2 * m then
            if hi : i.val < 2 * m then 0 else X ⟨k.val, hk⟩ ⟨i.val - 2 * m, by omega⟩ else 0) * f k := by
        intro k; rw [hU k i, Int.add_mul]
      rw [sumFin_congr hsp, sumFin_add]
      rw [sumFin_single i _ (fun k hk => by simp [hk])]
      simp only [↓reduceIte, Int.one_mul]
      congr 1
      by_cases hi : i.val < 2 * m
      · simp only [hi, ↓reduceDIte]
        exact sumFin_eq_zero (fun k => by by_cases hk : k.val < 2 * m <;> simp [hk])
      · simp only [hi, ↓reduceDIte]
        rw [← sumFin_cast (show 2 * m + 2 * n = 2 * (m + n) by omega)]
        rw [sumFin_split]
        rw [← Int.add_zero (sumFin (fun k : Fin (2 * m) => X k ⟨i.val - 2 * m, by omega⟩ * f ⟨k.val, by omega⟩))]
        congr 1
        · exact sumFin_congr (fun k => by simp [k.isLt])
        · exact sumFin_eq_zero (fun k => by
            dsimp only
            have hnk : ¬ (2 * m + k.val < 2 * m) := by omega
            simp only [hnk, ↓reduceDIte, Int.zero_mul])
    rw [hleft]
    -- Helper evaluations of diagCong sc A in the 4 quadrants directly on Fin (2*(m+n))
    have hD00 : ∀ (r c : Fin (2 * (m + n))) (hr : r.val < 2 * m) (hc : c.val < 2 * m),
        diagCong sc A r c = A00 ⟨r.val, hr⟩ ⟨c.val, hc⟩ := by
      intro r c hr hc; unfold diagCong; dsimp only [sc, A]; unfold castMat blockMat; simp [hr, hc]
    have hD01 : ∀ (r c : Fin (2 * (m + n))) (hr : r.val < 2 * m) (hc : ¬ c.val < 2 * m),
        diagCong sc A r c = d * A01 ⟨r.val, hr⟩ ⟨c.val - 2 * m, by omega⟩ := by
      intro r c hr hc; unfold diagCong; dsimp only [sc, A]; unfold castMat blockMat
      simp only [hr, hc, ↓reduceIte, ↓reduceDIte, Int.one_mul]; rw [Int.mul_comm]
    have hD10 : ∀ (r c : Fin (2 * (m + n))) (hr : ¬ r.val < 2 * m) (hc : c.val < 2 * m),
        diagCong sc A r c = -(d * A01 ⟨c.val, hc⟩ ⟨r.val - 2 * m, by omega⟩) := by
      intro r c hr hc; unfold diagCong; dsimp only [sc, A]; unfold castMat blockMat
      simp only [hr, hc, ↓reduceIte, ↓reduceDIte, Int.mul_one, Int.mul_neg]
    have hD11 : ∀ (r c : Fin (2 * (m + n))) (hr : ¬ r.val < 2 * m) (hc : ¬ c.val < 2 * m),
        diagCong sc A r c = d * d * A11 ⟨r.val - 2 * m, by omega⟩ ⟨c.val - 2 * m, by omega⟩ := by
      intro r c hr hc; unfold diagCong; dsimp only [sc, A]; unfold castMat blockMat
      simp only [hr, hc, ↓reduceIte, ↓reduceDIte]; ac_rfl
    unfold castMat blockDiag
    by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
    · simp only [hi, hj, ↓reduceDIte, Int.add_zero]
      exact hD00 i j hi hj
    · simp only [hi, hj, ↓reduceDIte, Int.add_zero]
      rw [hD01 i j hi hj]
      have h2 : sumFin (fun l : Fin (2 * m) => diagCong sc A i ⟨l.val, by omega⟩ * X l ⟨j.val - 2 * m, by omega⟩) =
                matMul A00 X ⟨i.val, hi⟩ ⟨j.val - 2 * m, by omega⟩ := by
        unfold matMul; exact sumFin_congr (fun l => by rw [hD00 i ⟨l.val, by omega⟩ hi l.isLt])
      rw [h2, Int.add_comm]
      exact hcert ⟨i.val, hi⟩ ⟨j.val - 2 * m, by omega⟩
    · simp only [hi, hj, ↓reduceDIte, Int.add_zero]
      rw [hD10 i j hi hj]
      have h2 : sumFin (fun k : Fin (2 * m) => X k ⟨i.val - 2 * m, by omega⟩ * diagCong sc A ⟨k.val, by omega⟩ j) =
                -matMul A00 X ⟨j.val, hj⟩ ⟨i.val - 2 * m, by omega⟩ := by
        unfold matMul; rw [← sumFin_neg]; apply sumFin_congr; intro k
        rw [hD00 ⟨k.val, by omega⟩ j k.isLt hj, h00.2 k ⟨j.val, hj⟩, Int.mul_neg, Int.mul_comm]
      rw [h2]
      have hc0 := hcert ⟨j.val, hj⟩ ⟨i.val - 2 * m, by omega⟩
      omega
    · simp only [hi, hj, ↓reduceDIte]
      rw [hD11 i j hi hj]
      have h2 : sumFin (fun l : Fin (2 * m) => diagCong sc A i ⟨l.val, by omega⟩ * X l ⟨j.val - 2 * m, by omega⟩) =
                -(d * matMul (matTrans A01) X ⟨i.val - 2 * m, by omega⟩ ⟨j.val - 2 * m, by omega⟩) := by
        unfold matMul matTrans; rw [← sumFin_mul_left, ← sumFin_neg]
        apply sumFin_congr; intro l
        rw [hD10 i ⟨l.val, by omega⟩ hi l.isLt, Int.neg_mul, Int.mul_assoc]
      have h3 : sumFin (fun k : Fin (2 * m) => X k ⟨i.val - 2 * m, by omega⟩ *
          (diagCong sc A ⟨k.val, by omega⟩ j +
           sumFin (fun l : Fin (2 * m) => diagCong sc A ⟨k.val, by omega⟩ ⟨l.val, by omega⟩ * X l ⟨j.val - 2 * m, by omega⟩))) = 0 := by
        apply sumFin_eq_zero; intro k
        rw [hD01 ⟨k.val, by omega⟩ j k.isLt hj]
        have hb : sumFin (fun l : Fin (2 * m) => diagCong sc A ⟨k.val, by omega⟩ ⟨l.val, by omega⟩ * X l ⟨j.val - 2 * m, by omega⟩) =
                  matMul A00 X k ⟨j.val - 2 * m, by omega⟩ := by
          unfold matMul; exact sumFin_congr (fun l => by rw [hD00 ⟨k.val, by omega⟩ ⟨l.val, by omega⟩ k.isLt l.isLt])
        rw [hb, Int.add_comm, hcert k ⟨j.val - 2 * m, by omega⟩, Int.mul_zero]
      rw [h2, h3, Int.add_zero]
      dsimp only [S]
      rw [Int.sub_eq_add_neg]
  rw [hcong, pfaffian_blockDiag]

-- ----------------------------------------------------------------------------
-- Mechanism 1B: General Integral Block-Schur Elimination (Bottom-Right Pivot)
-- ----------------------------------------------------------------------------
theorem pfaffian_blockSchur_bot {m n : Nat}
    (A00 : Mat (2 * m)) (A01 : Fin (2 * m) → Fin (2 * n) → Int) (A11 : Mat (2 * n))
    (h00 : IsSkew A00) (h11 : IsSkew A11)
    (d : Int) (Y : Fin (2 * n) → Fin (2 * m) → Int)
    (hcert : ∀ i j, d * A01 i j + matMul (matTrans Y) A11 i j = 0) :
    d ^ (2 * m) * pfaffian (m + n) (castMat (by omega) (blockMat A00 A01 (fun i j => -A01 j i) A11)) =
    pfaffian m (fun i j => d * d * A00 i j - d * matMul (matTrans Y) (matTrans A01) i j) * pfaffian n A11 := by
  let A : Mat (2 * (m + n)) := castMat (by omega) (blockMat A00 A01 (fun i j => -A01 j i) A11)
  have hA : IsSkew A := by
    constructor
    · intro i; dsimp only [A]; unfold castMat blockMat
      by_cases hi : i.val < 2 * m <;> simp [hi, h00.1, h11.1]
    · intro i j; dsimp only [A]; unfold castMat blockMat
      by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
      · simp only [hi, hj, ↓reduceDIte]; exact h00.2 _ _
      · simp only [hi, hj, ↓reduceDIte, Int.neg_neg]
      · simp only [hi, hj, ↓reduceDIte]
      · simp only [hi, hj, ↓reduceDIte]; exact h11.2 _ _
  let sc : Fin (2 * (m + n)) → Int := fun i => if i.val < 2 * m then d else 1
  have hprod_sc : prodFin sc = d ^ (2 * m) := by
    rw [← prodFin_cast (show 2 * m + 2 * n = 2 * (m + n) by omega) sc]
    rw [prodFin_split]
    have hL : prodFin (fun i : Fin (2 * m) => sc ⟨i.val, by omega⟩) = d ^ (2 * m) := by
      have : prodFin (fun i : Fin (2 * m) => sc ⟨i.val, by omega⟩) = prodFin (fun _ : Fin (2 * m) => d) :=
        prodFin_congr (fun i => by dsimp only [sc]; simp [i.isLt])
      rw [this, prodFin_const]
    have hR : prodFin (fun j : Fin (2 * n) => sc ⟨2 * m + j.val, by omega⟩) = 1 := by
      have : prodFin (fun j : Fin (2 * n) => sc ⟨2 * m + j.val, by omega⟩) = prodFin (fun _ : Fin (2 * n) => (1 : Int)) :=
        prodFin_congr (fun j => by
          dsimp only [sc]
          have hnj : ¬ ((⟨2 * m + j.val, by omega⟩ : Fin (2 * (m + n))).val < 2 * m) := by dsimp; omega
          simp only [hnj, ↓reduceIte])
      rw [this, prodFin_const]; exact Int.one_pow
    rw [hL, hR, Int.mul_one]
  have hdiag : d ^ (2 * m) * pfaffian (m + n) A = pfaffian (m + n) (diagCong sc A) := by
    rw [pfaffian_diagCong, hprod_sc]
  rw [hdiag]
  have hskew_sc : IsSkew (diagCong sc A) := by
    constructor
    · intro i; unfold diagCong; rw [hA.1 i]; simp
    · intro i j; unfold diagCong; rw [hA.2 i j]; rw [Int.mul_neg, Int.neg_mul]; ac_rfl
  rw [← pfaffian_blockLowerId (show 2 * m + 2 * n = 2 * (m + n) by omega) Y hskew_sc]
  let S : Mat (2 * m) := fun i j => d * d * A00 i j - d * matMul (matTrans Y) (matTrans A01) i j
  have hcong : congruence (castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockLowerId Y)) (diagCong sc A) =
               castMat (by omega) (blockDiag S A11) := by
    funext i j
    unfold congruence matMul matTrans
    have hLmat : ∀ k l : Fin (2 * (m + n)),
        castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockLowerId Y) k l =
        (if k = l then 1 else 0) +
        (if hk : k.val < 2 * m then 0
        else if hl : l.val < 2 * m then Y ⟨k.val - 2 * m, by omega⟩ ⟨l.val, hl⟩ else 0) := by
      intro k l; unfold castMat blockLowerId; simp [Fin.ext_iff]
    have hright : ∀ k : Fin (2 * (m + n)),
        sumFin (fun l => diagCong sc A k l *
          castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockLowerId Y) l j) =
        diagCong sc A k j +
        if hj : j.val < 2 * m then
          sumFin (fun l : Fin (2 * n) => diagCong sc A k ⟨2 * m + l.val, by omega⟩ * Y l ⟨j.val, hj⟩)
        else 0 := by
      intro k
      have hsp : ∀ l : Fin (2 * (m + n)),
          diagCong sc A k l * castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockLowerId Y) l j =
          diagCong sc A k l * (if l = j then 1 else 0) +
          diagCong sc A k l * (if hl : l.val < 2 * m then 0
            else if hj : j.val < 2 * m then Y ⟨l.val - 2 * m, by omega⟩ ⟨j.val, hj⟩ else 0) := by
        intro l; rw [hLmat l j, Int.mul_add]
      rw [sumFin_congr hsp, sumFin_add]
      rw [sumFin_single j _ (fun l hl => by simp [hl])]
      simp only [↓reduceIte, Int.mul_one]
      congr 1
      by_cases hj : j.val < 2 * m
      · simp only [hj, ↓reduceDIte]
        rw [← sumFin_cast (show 2 * m + 2 * n = 2 * (m + n) by omega)]
        rw [sumFin_split]
        rw [← Int.zero_add (sumFin (fun l : Fin (2 * n) => diagCong sc A k ⟨2 * m + l.val, by omega⟩ * Y l ⟨j.val, hj⟩))]
        congr 1
        · exact sumFin_eq_zero (fun l => by simp [l.isLt])
        · apply sumFin_congr; intro l
          dsimp only
          have hnl : ¬ (2 * m + l.val < 2 * m) := by omega
          simp only [hnl, ↓reduceDIte]
          congr 2; apply Fin.ext; dsimp; omega
      · simp only [hj, ↓reduceDIte]
        exact sumFin_eq_zero (fun l => by by_cases hl : l.val < 2 * m <;> simp [hl])
    simp only [hright]
    have hleft : ∀ f : Fin (2 * (m + n)) → Int,
        sumFin (fun k => castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockLowerId Y) k i * f k) =
        f i + if hi : i.val < 2 * m then
                sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ * f ⟨2 * m + k.val, by omega⟩)
              else 0 := by
      intro f
      have hsp : ∀ k : Fin (2 * (m + n)),
          castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockLowerId Y) k i * f k =
          (if k = i then 1 else 0) * f k +
          (if hk : k.val < 2 * m then 0
            else if hi : i.val < 2 * m then Y ⟨k.val - 2 * m, by omega⟩ ⟨i.val, hi⟩ else 0) * f k := by
        intro k; rw [hLmat k i, Int.add_mul]
      rw [sumFin_congr hsp, sumFin_add]
      rw [sumFin_single i _ (fun k hk => by simp [hk])]
      simp only [↓reduceIte, Int.one_mul]
      congr 1
      by_cases hi : i.val < 2 * m
      · simp only [hi, ↓reduceDIte]
        rw [← sumFin_cast (show 2 * m + 2 * n = 2 * (m + n) by omega)]
        rw [sumFin_split]
        rw [← Int.zero_add (sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ * f ⟨2 * m + k.val, by omega⟩))]
        congr 1
        · exact sumFin_eq_zero (fun k => by simp [k.isLt])
        · apply sumFin_congr; intro k
          dsimp only
          have hnk : ¬ (2 * m + k.val < 2 * m) := by omega
          simp only [hnk, ↓reduceDIte]
          congr 2; apply Fin.ext; dsimp; omega
      · simp only [hi, ↓reduceDIte]
        exact sumFin_eq_zero (fun k => by by_cases hk : k.val < 2 * m <;> simp [hk])
    rw [hleft]
    have hD00 : ∀ (r c : Fin (2 * (m + n))) (hr : r.val < 2 * m) (hc : c.val < 2 * m),
        diagCong sc A r c = d * d * A00 ⟨r.val, hr⟩ ⟨c.val, hc⟩ := by
      intro r c hr hc; unfold diagCong; dsimp only [sc, A]; unfold castMat blockMat
      simp only [hr, hc, ↓reduceIte, ↓reduceDIte]; ac_rfl
    have hD01 : ∀ (r c : Fin (2 * (m + n))) (hr : r.val < 2 * m) (hc : ¬ c.val < 2 * m),
        diagCong sc A r c = d * A01 ⟨r.val, hr⟩ ⟨c.val - 2 * m, by omega⟩ := by
      intro r c hr hc; unfold diagCong; dsimp only [sc, A]; unfold castMat blockMat
      simp only [hr, hc, ↓reduceIte, ↓reduceDIte, Int.mul_one]
    have hD10 : ∀ (r c : Fin (2 * (m + n))) (hr : ¬ r.val < 2 * m) (hc : c.val < 2 * m),
        diagCong sc A r c = -(d * A01 ⟨c.val, hc⟩ ⟨r.val - 2 * m, by omega⟩) := by
      intro r c hr hc; unfold diagCong; dsimp only [sc, A]; unfold castMat blockMat
      simp only [hr, hc, ↓reduceIte, ↓reduceDIte, Int.one_mul]
      rw [Int.neg_mul, Int.mul_comm]
    have hD11 : ∀ (r c : Fin (2 * (m + n))) (hr : ¬ r.val < 2 * m) (hc : ¬ c.val < 2 * m),
        diagCong sc A r c = A11 ⟨r.val - 2 * m, by omega⟩ ⟨c.val - 2 * m, by omega⟩ := by
      intro r c hr hc; unfold diagCong; dsimp only [sc, A]; unfold castMat blockMat
      simp only [hr, hc, ↓reduceIte, ↓reduceDIte, Int.one_mul, Int.mul_one]
    unfold castMat blockDiag
    by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
    · simp only [hi, hj, ↓reduceDIte]
      rw [hD00 i j hi hj]
      have h2 : sumFin (fun l : Fin (2 * n) => diagCong sc A i ⟨2 * m + l.val, by omega⟩ * Y l ⟨j.val, hj⟩) +
                sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ *
                  (diagCong sc A ⟨2 * m + k.val, by omega⟩ j +
                   sumFin (fun l : Fin (2 * n) => diagCong sc A ⟨2 * m + k.val, by omega⟩ ⟨2 * m + l.val, by omega⟩ * Y l ⟨j.val, hj⟩))) =
                -(d * matMul (matTrans Y) (matTrans A01) ⟨i.val, hi⟩ ⟨j.val, hj⟩) := by
        have hsum1 : sumFin (fun l : Fin (2 * n) => diagCong sc A i ⟨2 * m + l.val, by omega⟩ * Y l ⟨j.val, hj⟩) =
                     -sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ *
                       sumFin (fun l : Fin (2 * n) => A11 k l * Y l ⟨j.val, hj⟩)) := by
          have ha : ∀ l : Fin (2 * n), diagCong sc A i ⟨2 * m + l.val, by omega⟩ * Y l ⟨j.val, hj⟩ =
              -(sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ * A11 k l) * Y l ⟨j.val, hj⟩) := by
            intro l
            have hnl : ¬ ((⟨2 * m + l.val, by omega⟩ : Fin (2 * (m + n))).val < 2 * m) := by dsimp; omega
            rw [hD01 i ⟨2 * m + l.val, by omega⟩ hi hnl]
            have hl' : (⟨(⟨2 * m + l.val, by omega⟩ : Fin (2 * (m + n))).val - 2 * m, by omega⟩ : Fin (2 * n)) = l :=
              Fin.ext (by dsimp; omega)
            rw [hl']
            have hc0 := hcert ⟨i.val, hi⟩ l
            unfold matMul matTrans at hc0
            have : d * A01 ⟨i.val, hi⟩ l = -sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ * A11 k l) := by omega
            rw [this, Int.neg_mul]
          rw [sumFin_congr ha, sumFin_neg]
          congr 1
          have hb : ∀ l : Fin (2 * n), sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ * A11 k l) * Y l ⟨j.val, hj⟩ =
              sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ * (A11 k l * Y l ⟨j.val, hj⟩)) := by
            intro l; rw [← sumFin_mul_right]
            exact sumFin_congr (fun k => Int.mul_assoc _ _ _)
          rw [sumFin_congr hb, sumFin_comm]
          exact sumFin_congr (fun k => sumFin_mul_left _ _)
        have hsum2 : sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ *
            (diagCong sc A ⟨2 * m + k.val, by omega⟩ j +
             sumFin (fun l : Fin (2 * n) => diagCong sc A ⟨2 * m + k.val, by omega⟩ ⟨2 * m + l.val, by omega⟩ * Y l ⟨j.val, hj⟩))) =
            -(d * matMul (matTrans Y) (matTrans A01) ⟨i.val, hi⟩ ⟨j.val, hj⟩) +
            sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ *
              sumFin (fun l : Fin (2 * n) => A11 k l * Y l ⟨j.val, hj⟩)) := by
          have hsp : ∀ k : Fin (2 * n),
              Y k ⟨i.val, hi⟩ * (diagCong sc A ⟨2 * m + k.val, by omega⟩ j +
                sumFin (fun l : Fin (2 * n) => diagCong sc A ⟨2 * m + k.val, by omega⟩ ⟨2 * m + l.val, by omega⟩ * Y l ⟨j.val, hj⟩)) =
              (-(d * (Y k ⟨i.val, hi⟩ * A01 ⟨j.val, hj⟩ k))) +
              Y k ⟨i.val, hi⟩ * sumFin (fun l : Fin (2 * n) => A11 k l * Y l ⟨j.val, hj⟩) := by
            intro k
            have hnk : ¬ ((⟨2 * m + k.val, by omega⟩ : Fin (2 * (m + n))).val < 2 * m) := by dsimp; omega
            have hk' : (⟨(⟨2 * m + k.val, by omega⟩ : Fin (2 * (m + n))).val - 2 * m, by omega⟩ : Fin (2 * n)) = k :=
              Fin.ext (by dsimp; omega)
            rw [Int.mul_add, hD10 ⟨2 * m + k.val, by omega⟩ j hnk hj, hk']
            have hsub : sumFin (fun l : Fin (2 * n) => diagCong sc A ⟨2 * m + k.val, by omega⟩ ⟨2 * m + l.val, by omega⟩ * Y l ⟨j.val, hj⟩) =
                        sumFin (fun l : Fin (2 * n) => A11 k l * Y l ⟨j.val, hj⟩) := by
              apply sumFin_congr; intro l
              have hnl : ¬ ((⟨2 * m + l.val, by omega⟩ : Fin (2 * (m + n))).val < 2 * m) := by dsimp; omega
              have hl' : (⟨(⟨2 * m + l.val, by omega⟩ : Fin (2 * (m + n))).val - 2 * m, by omega⟩ : Fin (2 * n)) = l :=
                Fin.ext (by dsimp; omega)
              rw [hD11 ⟨2 * m + k.val, by omega⟩ ⟨2 * m + l.val, by omega⟩ hnk hnl, hk', hl']
            rw [hsub, Int.mul_neg]
            congr 1; congr 1; ac_rfl
          rw [sumFin_congr hsp, sumFin_add]
          congr 1
          unfold matMul matTrans
          rw [← sumFin_mul_left, ← sumFin_neg]
        rw [hsum1, hsum2]; omega
      rw [Int.add_assoc, h2]
      dsimp only [S]
      rw [Int.sub_eq_add_neg]
    · simp only [hi, hj, ↓reduceDIte, Int.add_zero]
      rw [hD01 i j hi hj]
      have hsum : sumFin (fun k : Fin (2 * n) => Y k ⟨i.val, hi⟩ * diagCong sc A ⟨2 * m + k.val, by omega⟩ j) =
                  matMul (matTrans Y) A11 ⟨i.val, hi⟩ ⟨j.val - 2 * m, by omega⟩ := by
        unfold matMul matTrans; apply sumFin_congr; intro k
        have hnk : ¬ ((⟨2 * m + k.val, by omega⟩ : Fin (2 * (m + n))).val < 2 * m) := by dsimp; omega
        have hk' : (⟨(⟨2 * m + k.val, by omega⟩ : Fin (2 * (m + n))).val - 2 * m, by omega⟩ : Fin (2 * n)) = k :=
          Fin.ext (by dsimp; omega)
        rw [hD11 ⟨2 * m + k.val, by omega⟩ j hnk hj, hk']
      rw [hsum]
      exact hcert ⟨i.val, hi⟩ ⟨j.val - 2 * m, by omega⟩
    · simp only [hi, hj, ↓reduceDIte, Int.add_zero]
      rw [hD10 i j hi hj]
      have hsum : sumFin (fun l : Fin (2 * n) => diagCong sc A i ⟨2 * m + l.val, by omega⟩ * Y l ⟨j.val, hj⟩) =
                  -matMul (matTrans Y) A11 ⟨j.val, hj⟩ ⟨i.val - 2 * m, by omega⟩ := by
        unfold matMul matTrans; rw [← sumFin_neg]; apply sumFin_congr; intro l
        have hnl : ¬ ((⟨2 * m + l.val, by omega⟩ : Fin (2 * (m + n))).val < 2 * m) := by dsimp; omega
        have hl' : (⟨(⟨2 * m + l.val, by omega⟩ : Fin (2 * (m + n))).val - 2 * m, by omega⟩ : Fin (2 * n)) = l :=
          Fin.ext (by dsimp; omega)
        rw [hD11 i ⟨2 * m + l.val, by omega⟩ hi hnl, hl', h11.2, Int.neg_mul, Int.mul_comm]
      rw [hsum]
      have hc0 := hcert ⟨j.val, hj⟩ ⟨i.val - 2 * m, by omega⟩
      omega
    · simp only [hi, hj, ↓reduceDIte, Int.add_zero]
      exact hD11 i j hi hj
  rw [hcong, pfaffian_blockDiag]

-- ----------------------------------------------------------------------------
-- Mechanism 2: Zero-Corner Upper-Triangular Pfaffian Theorem
-- ----------------------------------------------------------------------------
/-- Pure-Pfaffian Self-Congruence Theorem:
    For any `2n × 2n` skew matrix `D` and any `2(m+n) × 2(m+n)` skew matrix `A`,
    `Pf((I_{2m} ⊕ D)^T A (I_{2m} ⊕ D)) = Pf(D)^2 * Pf(A)` (proved purely by fraction-free
    skew-symmetric congruence elimination, zero determinant theory required!). -/
theorem pfaffian_congruence_blockIdSkew : ∀ (n m : Nat) (D : Mat (2 * n)) (A : Mat (2 * (m + n))),
    IsSkew D → IsSkew A →
    pfaffian (m + n) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) D)) A) =
    pfaffian n D * pfaffian n D * pfaffian (m + n) A
  | 0, m, _, A, _, _ => by
    have h0 : m + 0 = m := Nat.add_zero m
    have hid : castMat (show 2 * m + 2 * 0 = 2 * (m + 0) by omega) (blockDiag (matId (2 * m)) (fun i j : Fin 0 => 0)) =
               matId (2 * (m + 0)) := by
      funext i j; unfold castMat blockDiag matId
      have hi : i.val < 2 * m := by omega
      have hj : j.val < 2 * m := by omega
      simp [hi, hj, Fin.ext_iff]
    have hid' : ∀ D : Mat 0,
        castMat (show 2 * m + 2 * 0 = 2 * (m + 0) by omega) (blockDiag (matId (2 * m)) D) =
        matId (2 * (m + 0)) := by
      intro D; funext i j; unfold castMat blockDiag matId
      have hi : i.val < 2 * m := by omega
      have hj : j.val < 2 * m := by omega
      simp [hi, hj, Fin.ext_iff]
    rw [hid', congruence_id]
    simp [pfaffian]
  | n + 1, m, D, A, hD, hA => by
    -- Search row 0 of D for a nonzero entry D 0 j
    by_cases hex : ∃ j : Fin (2 * (n + 1)), D ⟨0, by omega⟩ j ≠ 0
    · -- Nonzero pivot exists!
      let j := Classical.choose hex
      have hj_ne0 : D ⟨0, by omega⟩ j ≠ 0 := Classical.choose_spec hex
      have hj_pos : j ≠ ⟨0, by omega⟩ := by
        intro heq; rw [heq, hD.1] at hj_ne0; exact hj_ne0 rfl
      -- Step 1: swap j and 1 in D (if j ≠ 1) to put nonzero pivot p at (0, 1)
      let i0 : Fin (2 * (n + 1)) := ⟨0, by omega⟩
      let i1 : Fin (2 * (n + 1)) := ⟨1, by omega⟩
      let Eswap : Mat (2 * (n + 1)) := if j = i1 then matId _ else elemSwap i1 j
      let D1 : Mat (2 * (n + 1)) := congruence Eswap D
      have hD1_skew : IsSkew D1 := isSkew_congruence _ _ hD
      have hD1_01 : D1 i0 i1 ≠ 0 := by
        dsimp only [D1, Eswap]
        by_cases hji1 : j = i1
        · have hj1 : D i0 i1 ≠ 0 := by rw [← hji1]; exact hj_ne0
          simp only [hji1, ↓reduceIte, congruence_id]; exact hj1
        · simp only [hji1, ↓reduceIte, congruence_elemSwap]; unfold swapRC
          have hs0 : swapIdx i1 j i0 = i0 := swapIdx_other (fin_ne_of_val (by dsimp [i0, i1]; omega)) (Ne.symm hj_pos)
          rw [hs0, swapIdx_left]; exact hj_ne0
      let p : Int := D1 i0 i1
      let P0 : Mat 2 := fun r c => D1 ⟨r.val, by omega⟩ ⟨c.val, by omega⟩
      let B : Fin 2 → Fin (2 * n) → Int := fun r c => D1 ⟨r.val, by omega⟩ ⟨2 + c.val, by omega⟩
      let Drem : Mat (2 * n) := fun r c => D1 ⟨2 + r.val, by omega⟩ ⟨2 + c.val, by omega⟩
      let X : Fin 2 → Fin (2 * n) → Int := fun r c =>
        if r.val = 0 then B ⟨1, by omega⟩ c else -B ⟨0, by omega⟩ c
      have hcert : ∀ r c, matMul P0 X r c + p * B r c = 0 := by
        intro r c
        unfold matMul
        change P0 r ⟨0, by omega⟩ * X ⟨0, by omega⟩ c + (P0 r ⟨1, by omega⟩ * X ⟨1, by omega⟩ c + 0) + p * B r c = 0
        have hr01 : r.val = 0 ∨ r.val = 1 := by omega
        rcases hr01 with hr0 | hr1
        · have hrf : r = ⟨0, by omega⟩ := Fin.ext hr0
          rw [hrf]; dsimp only [P0, B, X, p, i0, i1]
          rw [hD1_skew.1 ⟨0, by omega⟩]; simp only [↓reduceIte, Nat.one_ne_zero, Int.zero_mul, Int.zero_add, Int.add_zero, Int.mul_neg]; omega
        · have hrf : r = ⟨1, by omega⟩ := Fin.ext hr1
          rw [hrf]; dsimp only [P0, B, X, p, i0, i1]
          rw [hD1_skew.1 ⟨1, by omega⟩, hD1_skew.2 ⟨1, by omega⟩ ⟨0, by omega⟩]
          simp only [↓reduceIte, Int.zero_mul, Int.add_zero, Int.neg_mul]; omega
      let S : Mat (2 * n) := fun r c => p * p * Drem r c - p * matMul (matTrans B) X r c
      have hS_skew : IsSkew S := by
        constructor
        · intro r; dsimp only [S, Drem]; rw [hD1_skew.1]
          unfold matMul matTrans
          change p * p * 0 - p * (B ⟨0, by omega⟩ r * X ⟨0, by omega⟩ r + (B ⟨1, by omega⟩ r * X ⟨1, by omega⟩ r + 0)) = 0
          dsimp only [X]; simp only [↓reduceIte, Nat.one_ne_zero, Int.mul_zero, Int.add_zero, Int.mul_neg]
          rw [Int.mul_comm (B ⟨1, by omega⟩ r), Int.add_right_neg, Int.mul_zero]; rfl
        · intro r c; dsimp only [S, Drem]; rw [hD1_skew.2]
          unfold matMul matTrans
          change p * p * (-D1 ⟨2 + c.val, by omega⟩ ⟨2 + r.val, by omega⟩) -
            p * (B ⟨0, by omega⟩ r * X ⟨0, by omega⟩ c + (B ⟨1, by omega⟩ r * X ⟨1, by omega⟩ c + 0)) =
            -(p * p * D1 ⟨2 + c.val, by omega⟩ ⟨2 + r.val, by omega⟩ -
              p * (B ⟨0, by omega⟩ c * X ⟨0, by omega⟩ r + (B ⟨1, by omega⟩ c * X ⟨1, by omega⟩ r + 0)))
          dsimp only [X]; simp only [↓reduceIte, Nat.one_ne_zero, Int.add_zero]
          have h1 : B ⟨0, by omega⟩ r * B ⟨1, by omega⟩ c + B ⟨1, by omega⟩ r * -B ⟨0, by omega⟩ c =
                    -(B ⟨0, by omega⟩ c * B ⟨1, by omega⟩ r + B ⟨1, by omega⟩ c * -B ⟨0, by omega⟩ r) := by
            rw [Int.mul_neg, Int.mul_neg, Int.mul_comm (B ⟨0, by omega⟩ r), Int.mul_comm (B ⟨1, by omega⟩ r)]
            omega
          rw [h1, Int.mul_neg, Int.mul_neg]; omega
      -- Now relate congruence (I ⊕ D1) with congruence (I ⊕ (P0 ⊕ S))!
      -- Let E = E_diag_p * U_X where E_diag_p = diag(1, 1, p, ..., p) and U_X = blockUpperId X.
      -- Then congruence E D1 = P0 ⊕ S!
      let Ed : Mat (2 * (n + 1)) := fun r c => if r = c then (if r.val < 2 then 1 else p) else 0
      let Ux : Mat (2 * (n + 1)) := castMat (show 2 + 2 * n = 2 * (n + 1) by omega) (blockUpperId X)
      let E : Mat (2 * (n + 1)) := matMul Ed Ux
      have hD1_eq : D1 = castMat (show 2 + 2 * n = 2 * (n + 1) by omega) (blockMat P0 B (fun r c => -B c r) Drem) := by
        funext r c; unfold castMat blockMat; dsimp only [P0, B, Drem]
        by_cases hr : r.val < 2 <;> by_cases hc : c.val < 2
        · simp [hr, hc]
        · simp only [hr, hc, ↓reduceDIte]; congr 1; apply Fin.ext; dsimp; omega
        · simp only [hr, hc, ↓reduceDIte]; rw [hD1_skew.2 r c]; congr 2; apply Fin.ext; dsimp; omega
        · simp only [hr, hc, ↓reduceDIte]; congr 1 <;> (apply Fin.ext; dsimp; omega)
      have hschur_D1 : p ^ (2 * n) * pfaffian (n + 1) D1 = p * pfaffian n S := by
        have h1 := pfaffian_blockSchur_top (m := 1) (n := n) P0 B Drem
          ⟨fun r => hD1_skew.1 _, fun r c => hD1_skew.2 _ _⟩
          ⟨fun r => hD1_skew.1 _, fun r c => hD1_skew.2 _ _⟩
          p X hcert
        have hpfP0 : pfaffian 1 P0 = p := by
          change altSign 0 * P0 ⟨0, by omega⟩ ⟨1, by omega⟩ * 1 + 0 = p
          simp [P0, p, i0, i1]
        rw [hpfP0] at h1
        have hcast : pfaffian (1 + n) (castMat (by omega) (blockMat P0 B (fun r c => -B c r) Drem)) =
                     pfaffian (n + 1) D1 := by
          rw [← pfaffian_castMat (show 1 + n = n + 1 by omega)]
          rw [hD1_eq]; exact pfaffian_congr (fun _ _ => rfl)
        rw [hcast] at h1
        exact h1
      -- Helper: congruence by (I_{2m} ⊕ Ed) scales pfaffian by p^(2*n)
      have hpf_Ed : ∀ (M : Mat (2 * (m + (n + 1)))),
          pfaffian (m + (n + 1)) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) Ed)) M) =
          p ^ (2 * n) * pfaffian (m + (n + 1)) M := by
        intro M
        let sc : Fin (2 * (m + (n + 1))) → Int := fun i => if i.val < 2 * m + 2 then 1 else p
        have heq : congruence (castMat (by omega) (blockDiag (matId (2 * m)) Ed)) M = diagCong sc M := by
          funext r c; unfold congruence matMul matTrans diagCong
          have hE : ∀ u v : Fin (2 * (m + (n + 1))),
              castMat (by omega) (blockDiag (matId (2 * m)) Ed) u v = if u = v then sc u else 0 := by
            intro u v; unfold castMat blockDiag matId; dsimp only [Ed, sc]
            by_cases hu : u.val < 2 * m <;> by_cases hv : v.val < 2 * m
            · have h2 : u.val < 2 * m + 2 := by omega
              simp [hu, hv, h2, Fin.ext_iff]
            · have hne : u ≠ v := fin_ne_of_val (by omega)
              simp [hu, hv, hne]
            · have hne : u ≠ v := fin_ne_of_val (by omega)
              simp [hu, hv, hne]
            · have hiff1 : (⟨u.val - 2 * m, by omega⟩ : Fin (2 * (n + 1))) = ⟨v.val - 2 * m, by omega⟩ ↔ u = v := by
                simp only [Fin.ext_iff]; omega
              have hiff2 : (u.val - 2 * m < 2) ↔ (u.val < 2 * m + 2) := by omega
              simp [hu, hv, hiff1, hiff2]
          have h1 : ∀ k, sumFin (fun l => M k l * castMat (by omega) (blockDiag (matId (2 * m)) Ed) l c) =
                         M k c * sc c := by
            intro k
            rw [sumFin_congr (fun l => by rw [hE l c])]
            rw [sumFin_single c _ (fun l hl => by simp [hl])]
            simp
          simp only [h1]
          rw [sumFin_congr (fun k => by rw [hE k r])]
          rw [sumFin_single r _ (fun k hk => by simp [hk])]
          simp [Int.mul_assoc]
        rw [heq, pfaffian_diagCong]
        congr 1
        rw [← prodFin_cast (show (2 * m + 2) + 2 * n = 2 * (m + (n + 1)) by omega) sc, prodFin_split]
        have hL : prodFin (fun i : Fin (2 * m + 2) => sc ⟨i.val, by omega⟩) = 1 := by
          have : prodFin (fun i : Fin (2 * m + 2) => sc ⟨i.val, by omega⟩) = prodFin (fun _ : Fin (2 * m + 2) => (1 : Int)) :=
            prodFin_congr (fun i => by dsimp only [sc]; simp [i.isLt])
          rw [this, prodFin_const]; exact Int.one_pow
        have hR : prodFin (fun j : Fin (2 * n) => sc ⟨(2 * m + 2) + j.val, by omega⟩) = p ^ (2 * n) := by
          have : prodFin (fun j : Fin (2 * n) => sc ⟨(2 * m + 2) + j.val, by omega⟩) = prodFin (fun _ : Fin (2 * n) => p) :=
            prodFin_congr (fun j => by
              dsimp only [sc]
              have hnj : ¬ ((⟨(2 * m + 2) + j.val, by omega⟩ : Fin (2 * (m + (n + 1)))).val < 2 * m + 2) := by dsimp; omega
              simp only [hnj, ↓reduceIte])
          rw [this, prodFin_const]
        rw [hL, hR, Int.one_mul]
      have hpf_Ux : ∀ (M : Mat (2 * (m + (n + 1)))), IsSkew M →
          pfaffian (m + (n + 1)) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) Ux)) M) =
          pfaffian (m + (n + 1)) M := by
        intro M hM
        let Xext : Fin (2 * m + 2) → Fin (2 * n) → Int := fun r c =>
          if hr : r.val < 2 * m then 0 else X ⟨r.val - 2 * m, by omega⟩ c
        have heq : castMat (by omega) (blockDiag (matId (2 * m)) Ux) =
                   castMat (show (2 * m + 2) + 2 * n = 2 * (m + (n + 1)) by omega) (blockUpperId Xext) := by
          funext r c; unfold castMat blockDiag matId blockUpperId; dsimp only [Ux, Xext]
          unfold castMat blockUpperId; dsimp only
          by_cases hr : r.val < 2 * m <;> by_cases hc : c.val < 2 * m
          · have hr2 : r.val < 2 * m + 2 := by omega
            have hc2 : c.val < 2 * m + 2 := by omega
            simp [hr, hc, hr2, hc2, Fin.ext_iff]
          · have hr2 : r.val < 2 * m + 2 := by omega
            have hne : r.val ≠ c.val := by omega
            by_cases hc2 : c.val < 2 * m + 2 <;> simp [hr, hc, hr2, hc2, hne, Fin.ext_iff]
          · have hc2 : c.val < 2 * m + 2 := by omega
            have hne : r.val ≠ c.val := by omega
            by_cases hr2 : r.val < 2 * m + 2 <;> simp [hr, hc, hr2, hc2, hne, Fin.ext_iff]
          · have hiff1 : (⟨r.val - 2 * m, by omega⟩ : Fin (2 + 2 * n)) = ⟨c.val - 2 * m, by omega⟩ ↔
                         (⟨r.val, by omega⟩ : Fin ((2 * m + 2) + 2 * n)) = ⟨c.val, by omega⟩ := by
              simp only [Fin.ext_iff]; omega
            by_cases hr2 : r.val < 2 * m + 2 <;> by_cases hc2 : c.val < 2 * m + 2
            · have hr' : r.val - 2 * m < 2 := by omega
              have hc' : c.val - 2 * m < 2 := by omega
              simp [hr, hc, hr2, hc2, hr', hc', hiff1]
            · have hr' : r.val - 2 * m < 2 := by omega
              have hc' : ¬ (c.val - 2 * m < 2) := by omega
              simp only [hr, hc, hr2, hc2, hr', hc', ↓reduceDIte, hiff1]
              congr 1
            · have hr' : ¬ (r.val - 2 * m < 2) := by omega
              simp [hr, hc, hr2, hr', hiff1]
            · have hr' : ¬ (r.val - 2 * m < 2) := by omega
              simp [hr, hc, hr2, hr', hiff1]
        rw [heq]
        exact pfaffian_blockUpperId (show (2 * m + 2) + 2 * n = 2 * (m + (n + 1)) by omega) Xext hM
      have hpf_UxT : ∀ (M : Mat (2 * (m + (n + 1)))), IsSkew M →
          pfaffian (m + (n + 1)) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) (matTrans Ux))) M) =
          pfaffian (m + (n + 1)) M := by
        intro M hM
        let Yext : Fin (2 * n) → Fin (2 * m + 2) → Int := fun r c =>
          if hc : c.val < 2 * m then 0 else X ⟨c.val - 2 * m, by omega⟩ r
        have heq : castMat (by omega) (blockDiag (matId (2 * m)) (matTrans Ux)) =
                   castMat (show (2 * m + 2) + 2 * n = 2 * (m + (n + 1)) by omega) (blockLowerId Yext) := by
          funext r c; unfold castMat blockDiag matId matTrans blockLowerId; dsimp only [Ux, Yext]
          unfold castMat blockUpperId; dsimp only
          by_cases hr : r.val < 2 * m <;> by_cases hc : c.val < 2 * m
          · have hr2 : r.val < 2 * m + 2 := by omega
            simp [hr, hc, hr2, Fin.ext_iff]
          · have hr2 : r.val < 2 * m + 2 := by omega
            have hne : r.val ≠ c.val := by omega
            simp [hr, hc, hr2, hne, Fin.ext_iff]
          · have hc2 : c.val < 2 * m + 2 := by omega
            have hne : r.val ≠ c.val := by omega
            by_cases hr2 : r.val < 2 * m + 2 <;> simp [hr, hc, hr2, hc2, hne, Fin.ext_iff]
          · have hiff1 : (⟨c.val - 2 * m, by omega⟩ : Fin (2 + 2 * n)) = ⟨r.val - 2 * m, by omega⟩ ↔
                         (⟨r.val, by omega⟩ : Fin ((2 * m + 2) + 2 * n)) = ⟨c.val, by omega⟩ := by
              simp only [Fin.ext_iff]; omega
            by_cases hr2 : r.val < 2 * m + 2 <;> by_cases hc2 : c.val < 2 * m + 2
            · have hr' : r.val - 2 * m < 2 := by omega
              have hc' : c.val - 2 * m < 2 := by omega
              simp [hr, hc, hr2, hr', hc', hiff1]
            · have hc' : ¬ (c.val - 2 * m < 2) := by omega
              simp [hr, hc, hr2, hc', hiff1]
            · have hr' : ¬ (r.val - 2 * m < 2) := by omega
              have hc' : c.val - 2 * m < 2 := by omega
              simp only [hr, hc, hr2, hc2, hr', hc', ↓reduceDIte, hiff1]
              congr 1
            · have hc' : ¬ (c.val - 2 * m < 2) := by omega
              simp [hr, hc, hr2, hc2, hc', hiff1]
        rw [heq]
        exact pfaffian_blockLowerId (show (2 * m + 2) + 2 * n = 2 * (m + (n + 1)) by omega) Yext hM
      -- Helper: congruence E D1 = castMat _ (blockDiag P0 S)
      have hcong_E : congruence E D1 = castMat (show 2 + 2 * n = 2 * (n + 1) by omega) (blockDiag P0 S) := by
        -- Exact same calculation as in pfaffian_blockSchur_top!
        have h1 : congruence Ed D1 = diagCong (fun r : Fin (2 * (n + 1)) => if r.val < 2 then 1 else p) D1 := by
          funext r c; unfold congruence matMul matTrans diagCong; dsimp only [Ed]
          have hr : ∀ k, sumFin (fun l => D1 k l * (if l = c then (if l.val < 2 then 1 else p) else 0)) =
                         D1 k c * (if c.val < 2 then 1 else p) := by
            intro k; rw [sumFin_single c _ (fun l hl => by simp [hl])]; simp
          simp only [hr]
          rw [sumFin_single r _ (fun k hk => by simp [hk])]; simp [Int.mul_assoc]
        rw [show E = matMul Ed Ux from rfl, congruence_comp, h1]
        -- Now evaluate congruence Ux (diagCong sc0 D1) entrywise
        let sc0 : Fin (2 * (n + 1)) → Int := fun r => if r.val < 2 then 1 else p
        funext r c
        unfold congruence matMul matTrans
        have hU0 : ∀ k l : Fin (2 * (n + 1)), Ux k l = (if k = l then 1 else 0) +
            (if hk : k.val < 2 then if hl : l.val < 2 then 0 else X ⟨k.val, hk⟩ ⟨l.val - 2, by omega⟩ else 0) := by
          intro k l; dsimp only [Ux]; unfold castMat blockUpperId; simp [Fin.ext_iff]
        have hright : ∀ k : Fin (2 * (n + 1)),
            sumFin (fun l => diagCong sc0 D1 k l * Ux l c) =
            diagCong sc0 D1 k c +
            if hc : c.val < 2 then 0
            else sumFin (fun l : Fin 2 => diagCong sc0 D1 k ⟨l.val, by omega⟩ * X l ⟨c.val - 2, by omega⟩) := by
          intro k
          have hsp : ∀ l, diagCong sc0 D1 k l * Ux l c =
              diagCong sc0 D1 k l * (if l = c then 1 else 0) +
              diagCong sc0 D1 k l * (if hl : l.val < 2 then if hc : c.val < 2 then 0 else X ⟨l.val, hl⟩ ⟨c.val - 2, by omega⟩ else 0) := by
            intro l; rw [hU0 l c, Int.mul_add]
          rw [sumFin_congr hsp, sumFin_add, sumFin_single c _ (fun l hl => by simp [hl])]
          simp only [↓reduceIte, Int.mul_one]; congr 1
          by_cases hc : c.val < 2
          · simp only [hc, ↓reduceDIte]; exact sumFin_eq_zero (fun l => by by_cases hl : l.val < 2 <;> simp [hl])
          · simp only [hc, ↓reduceDIte]
            rw [← sumFin_cast (show 2 + 2 * n = 2 * (n + 1) by omega), sumFin_split]
            rw [← Int.add_zero (sumFin (fun l : Fin 2 => diagCong sc0 D1 k ⟨l.val, by omega⟩ * X l ⟨c.val - 2, by omega⟩))]
            exact congr (congrArg (· + ·)
              (sumFin_congr (fun l => by simp [l.isLt])))
              (sumFin_eq_zero (fun l => by
                dsimp only
                have hnl : ¬ (2 + l.val < 2) := by omega
                simp only [hnl, ↓reduceDIte, Int.mul_zero]))
        change sumFin (fun k => Ux k r * sumFin (fun l => diagCong sc0 D1 k l * Ux l c)) = _
        simp only [hright]
        have hleft : ∀ f : Fin (2 * (n + 1)) → Int,
            sumFin (fun k => Ux k r * f k) =
            f r + if hr : r.val < 2 then 0
                  else sumFin (fun k : Fin 2 => X k ⟨r.val - 2, by omega⟩ * f ⟨k.val, by omega⟩) := by
          intro f
          have hsp : ∀ k, Ux k r * f k = (if k = r then 1 else 0) * f k +
              (if hk : k.val < 2 then if hr : r.val < 2 then 0 else X ⟨k.val, hk⟩ ⟨r.val - 2, by omega⟩ else 0) * f k := by
            intro k; rw [hU0 k r, Int.add_mul]
          rw [sumFin_congr hsp, sumFin_add, sumFin_single r _ (fun k hk => by simp [hk])]
          simp only [↓reduceIte, Int.one_mul]; congr 1
          by_cases hr : r.val < 2
          · simp only [hr, ↓reduceDIte]; exact sumFin_eq_zero (fun k => by by_cases hk : k.val < 2 <;> simp [hk])
          · simp only [hr, ↓reduceDIte]
            rw [← sumFin_cast (show 2 + 2 * n = 2 * (n + 1) by omega), sumFin_split]
            rw [← Int.add_zero (sumFin (fun k : Fin 2 => X k ⟨r.val - 2, by omega⟩ * f ⟨k.val, by omega⟩))]
            exact congr (congrArg (· + ·)
              (sumFin_congr (fun k => by simp [k.isLt])))
              (sumFin_eq_zero (fun k => by
                dsimp only
                have hnk : ¬ (2 + k.val < 2) := by omega
                simp only [hnk, ↓reduceDIte, Int.zero_mul]))
        rw [hleft]
        have hD00 : ∀ (u v : Fin (2 * (n + 1))) (hu : u.val < 2) (hv : v.val < 2),
            diagCong sc0 D1 u v = P0 ⟨u.val, hu⟩ ⟨v.val, hv⟩ := by
          intro u v hu hv; unfold diagCong; dsimp [sc0, P0]; simp [hu, hv]
        have hD01 : ∀ (u v : Fin (2 * (n + 1))) (hu : u.val < 2) (hv : ¬ v.val < 2),
            diagCong sc0 D1 u v = p * B ⟨u.val, hu⟩ ⟨v.val - 2, by omega⟩ := by
          intro u v hu hv; unfold diagCong; dsimp [sc0, B]
          simp only [hu, hv, ↓reduceIte, Int.one_mul]
          have hv' : (⟨2 + (v.val - 2), by omega⟩ : Fin (2 * (n + 1))) = v := Fin.ext (by dsimp; omega)
          rw [hv', Int.mul_comm]
        have hD10 : ∀ (u v : Fin (2 * (n + 1))) (hu : ¬ u.val < 2) (hv : v.val < 2),
            diagCong sc0 D1 u v = -(p * B ⟨v.val, hv⟩ ⟨u.val - 2, by omega⟩) := by
          intro u v hu hv; unfold diagCong; dsimp [sc0, B]
          simp only [hu, hv, ↓reduceIte, Int.mul_one]
          have hu' : (⟨2 + (u.val - 2), by omega⟩ : Fin (2 * (n + 1))) = u := Fin.ext (by dsimp; omega)
          rw [hu', hD1_skew.2 u v, Int.mul_neg]
        have hD11 : ∀ (u v : Fin (2 * (n + 1))) (hu : ¬ u.val < 2) (hv : ¬ v.val < 2),
            diagCong sc0 D1 u v = p * p * Drem ⟨u.val - 2, by omega⟩ ⟨v.val - 2, by omega⟩ := by
          intro u v hu hv; unfold diagCong; dsimp [sc0, Drem]
          simp only [hu, hv, ↓reduceIte]
          have hu' : (⟨2 + (u.val - 2), by omega⟩ : Fin (2 * (n + 1))) = u := Fin.ext (by dsimp; omega)
          have hv' : (⟨2 + (v.val - 2), by omega⟩ : Fin (2 * (n + 1))) = v := Fin.ext (by dsimp; omega)
          rw [hu', hv', Int.mul_right_comm]
        unfold castMat blockDiag
        by_cases hr : r.val < 2 <;> by_cases hc : c.val < 2
        · simp only [hr, hc, ↓reduceDIte, Int.add_zero]
          exact hD00 r c hr hc
        · simp only [hr, hc, ↓reduceDIte, Int.add_zero]
          rw [hD01 r c hr hc]
          have h2 : sumFin (fun l : Fin 2 => diagCong sc0 D1 r ⟨l.val, by omega⟩ * X l ⟨c.val - 2, by omega⟩) =
                    matMul P0 X ⟨r.val, hr⟩ ⟨c.val - 2, by omega⟩ := by
            unfold matMul; exact sumFin_congr (fun l => by rw [hD00 r ⟨l.val, by omega⟩ hr l.isLt])
          rw [h2, Int.add_comm]
          exact hcert ⟨r.val, hr⟩ ⟨c.val - 2, by omega⟩
        · simp only [hr, hc, ↓reduceDIte, Int.add_zero]
          rw [hD10 r c hr hc]
          have h2 : sumFin (fun k : Fin 2 => X k ⟨r.val - 2, by omega⟩ * diagCong sc0 D1 ⟨k.val, by omega⟩ c) =
                    -matMul P0 X ⟨c.val, hc⟩ ⟨r.val - 2, by omega⟩ := by
            unfold matMul; rw [← sumFin_neg]; apply sumFin_congr; intro k
            rw [hD00 ⟨k.val, by omega⟩ c k.isLt hc]
            dsimp only [P0]
            rw [hD1_skew.2 ⟨k.val, by omega⟩ ⟨c.val, by omega⟩, Int.mul_neg, Int.mul_comm]
          rw [h2]
          have hc0 := hcert ⟨c.val, hc⟩ ⟨r.val - 2, by omega⟩
          omega
        · simp only [hr, hc, ↓reduceDIte]
          rw [hD11 r c hr hc]
          have h2 : sumFin (fun l : Fin 2 => diagCong sc0 D1 r ⟨l.val, by omega⟩ * X l ⟨c.val - 2, by omega⟩) =
                    -(p * matMul (matTrans B) X ⟨r.val - 2, by omega⟩ ⟨c.val - 2, by omega⟩) := by
            unfold matMul matTrans; rw [← sumFin_mul_left, ← sumFin_neg]
            apply sumFin_congr; intro l
            rw [hD10 r ⟨l.val, by omega⟩ hr l.isLt, Int.neg_mul, Int.mul_assoc]
          have h3 : sumFin (fun k : Fin 2 => X k ⟨r.val - 2, by omega⟩ *
              (diagCong sc0 D1 ⟨k.val, by omega⟩ c +
               sumFin (fun l : Fin 2 => diagCong sc0 D1 ⟨k.val, by omega⟩ ⟨l.val, by omega⟩ * X l ⟨c.val - 2, by omega⟩))) = 0 := by
            apply sumFin_eq_zero; intro k
            rw [hD01 ⟨k.val, by omega⟩ c k.isLt hc]
            have hb : sumFin (fun l : Fin 2 => diagCong sc0 D1 ⟨k.val, by omega⟩ ⟨l.val, by omega⟩ * X l ⟨c.val - 2, by omega⟩) =
                      matMul P0 X k ⟨c.val - 2, by omega⟩ := by
              unfold matMul; exact sumFin_congr (fun l => by rw [hD00 ⟨k.val, by omega⟩ ⟨l.val, by omega⟩ k.isLt l.isLt])
            rw [hb, Int.add_comm, hcert k ⟨c.val - 2, by omega⟩, Int.mul_zero]
          rw [h2, h3, Int.add_zero]
          dsimp only [S]
          rw [Int.sub_eq_add_neg]
      -- Step 3: Now track `pfaffian (m + (n + 1))` on `congruence (I_{2m} ⊕ (E^T D1 E)) A`!
      -- LHS: factor (I ⊕ E^T D1 E) = (I ⊕ E^T)(I ⊕ Eswap^T)(I ⊕ D)(I ⊕ Eswap)(I ⊕ E)
      -- `I ⊕ (E^T D1 E) = (I ⊕ (Eswap * E)^T) * (I ⊕ D) * (I ⊕ (Eswap * E))`.
      have hfactor_L :
          castMat (show 2 * m + 2 * (n + 1) = 2 * (m + (n + 1)) by omega) (blockDiag (matId (2 * m)) (congruence E D1)) =
          matMul (castMat (by omega) (blockDiag (matId (2 * m)) (matTrans Ux)))
            (matMul (castMat (by omega) (blockDiag (matId (2 * m)) Ed))
              (matMul (castMat (by omega) (blockDiag (matId (2 * m)) Eswap))
                (matMul (castMat (by omega) (blockDiag (matId (2 * m)) D))
                  (matMul (castMat (by omega) (blockDiag (matId (2 * m)) Eswap))
                    (matMul (castMat (by omega) (blockDiag (matId (2 * m)) Ed))
                      (castMat (by omega) (blockDiag (matId (2 * m)) Ux))))))) := by
        have hEdT : matTrans Ed = Ed := by
          funext r c; dsimp only [Ed]; unfold matTrans
          by_cases h : r = c
          · subst h; simp
          · simp [h, Ne.symm h]
        have hEswapT : matTrans Eswap = Eswap := by
          dsimp only [Eswap]; split
          · exact matTrans_matId _
          · exact matTrans_elemSwap _ _
        simp only [matMul_castMat, matMul_blockDiag, matMul_matId_left]
        congr 1; congr 1
        dsimp only [D1, E]; unfold congruence
        rw [matTrans_mul, hEdT, hEswapT]
        simp only [matMul_assoc]
      have hpf_Eswap : ∀ (M : Mat (2 * (m + (n + 1)))), IsSkew M →
          pfaffian (m + (n + 1)) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) Eswap)) M) =
          (if j = i1 then 1 else -1) * pfaffian (m + (n + 1)) M := by
        intro M hM; dsimp only [Eswap]
        by_cases hji1 : j = i1
        · simp only [hji1, ↓reduceIte]
          have hid : castMat (show 2 * m + 2 * (n + 1) = 2 * (m + (n + 1)) by omega)
              (blockDiag (matId (2 * m)) (matId (2 * (n + 1)))) = matId _ := by
            funext r c; unfold castMat blockDiag matId
            by_cases hr : r.val < 2 * m <;> by_cases hc : c.val < 2 * m
            · simp [hr, hc, Fin.ext_iff]
            · have hne : r ≠ c := fin_ne_of_val (by omega); simp [hr, hc, hne]
            · have hne : r ≠ c := fin_ne_of_val (by omega); simp [hr, hc, hne]
            · have : (⟨r.val - 2 * m, by omega⟩ : Fin (2 * (n + 1))) = ⟨c.val - 2 * m, by omega⟩ ↔ r = c := by
                simp only [Fin.ext_iff]; omega
              simp [hr, hc, this]
          rw [hid, congruence_id, Int.one_mul]
        · simp only [hji1, ↓reduceIte, elemSwap_blockDiag]
          have hne : (⟨2 * m + i1.val, by omega⟩ : Fin (2 * (m + (n + 1)))) ≠ ⟨2 * m + j.val, by omega⟩ :=
            fin_ne_of_val (by intro h; apply hji1; apply Fin.ext; dsimp at h; omega)
          rw [pfaffian_elemSwap_congruence _ _ hne hM]; omega
      -- Step 3: Exact integral right-inverse trick (zero rationals!):
      -- Let Ed' = diag(p, p, 1, ..., 1), so Ed' * Ed = p * I.
      -- Let UxT_inv = blockLowerId (-X^T), so UxT_inv * Ux^T = I.
      -- Let G = Eswap * Ed' * UxT_inv; then G * (Eswap * Ed * Ux)^T = p * I!
      let Ed' : Mat (2 * (n + 1)) := fun r c => if r = c then (if r.val < 2 then p else 1) else 0
      let negXT : Fin (2 * n) → Fin 2 → Int := fun r c => -X c r
      let UxT_inv : Mat (2 * (n + 1)) := castMat (show 2 + 2 * n = 2 * (n + 1) by omega) (blockLowerId negXT)
      let G : Mat (2 * (n + 1)) := matMul Eswap (matMul Ed' UxT_inv)
      -- Verify UxT_inv * matTrans Ux = matId
      have hUx_inv : matMul UxT_inv (matTrans Ux) = matId (2 * (n + 1)) := by
        funext r c; unfold matMul matTrans matId; dsimp only [UxT_inv, Ux, negXT]
        unfold castMat blockLowerId blockUpperId
        -- Split sum at 2
        rw [← sumFin_cast (show 2 + 2 * n = 2 * (n + 1) by omega), sumFin_split]
        by_cases hr : r.val < 2 <;> by_cases hc : c.val < 2
        · rw [← Int.add_zero (if r = c then (1 : Int) else 0)]
          refine int_add_congr ?_ ?_
          · rw [sumFin_single ⟨r.val, hr⟩ _ (fun k hk => by
              have hne : (⟨r.val, by omega⟩ : Fin (2 + 2 * n)) ≠ ⟨k.val, by omega⟩ := fin_ne_of_val (by intro h; apply hk; apply Fin.ext; dsimp at h ⊢; omega)
              simp [hr, hne])]
            simp only [hr, hc, ↓reduceDIte, ↓reduceIte, Int.add_zero, Int.one_mul]
            have hiff : (⟨c.val, by omega⟩ : Fin (2 + 2 * n)) = ⟨r.val, by omega⟩ ↔ r = c := by
              simp only [Fin.ext_iff]; omega
            simp [hiff]
          · exact sumFin_eq_zero (fun k => by
              have hne : (⟨r.val, by omega⟩ : Fin (2 + 2 * n)) ≠ ⟨2 + k.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
              simp [hr, hne])
        · have hne : r ≠ c := fin_ne_of_val (by omega)
          simp only [hne, ↓reduceIte]
          rw [← Int.add_zero (0 : Int)]
          refine int_add_congr ?_ ?_
          · exact sumFin_eq_zero (fun k => by
              have hne' : (⟨c.val, by omega⟩ : Fin (2 + 2 * n)) ≠ ⟨k.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
              simp [hc, hne'])
          · exact sumFin_eq_zero (fun k => by
              have hne' : (⟨r.val, by omega⟩ : Fin (2 + 2 * n)) ≠ ⟨2 + k.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
              simp [hr, hne'])
        · have hne : r ≠ c := fin_ne_of_val (by omega)
          simp only [hne, ↓reduceIte]
          apply Eq.trans (b := -X ⟨c.val, hc⟩ ⟨r.val - 2, by omega⟩ + X ⟨c.val, hc⟩ ⟨r.val - 2, by omega⟩)
          · refine int_add_congr ?_ ?_
            · rw [sumFin_single ⟨c.val, hc⟩ _ (fun k hk => by
                have hne' : (⟨c.val, by omega⟩ : Fin (2 + 2 * n)) ≠ ⟨k.val, by omega⟩ := fin_ne_of_val (by intro h; apply hk; apply Fin.ext; dsimp at h ⊢; omega)
                simp [hc, k.isLt, hne'])]
              have hne' : (⟨r.val, by omega⟩ : Fin (2 + 2 * n)) ≠ ⟨c.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
              simp [hr, hc, hne']
            · rw [sumFin_single ⟨r.val - 2, by omega⟩ _ (fun k hk => by
                have hne' : (⟨r.val, by omega⟩ : Fin (2 + 2 * n)) ≠ ⟨2 + k.val, by omega⟩ := fin_ne_of_val (by intro h; apply hk; apply Fin.ext; dsimp at h ⊢; omega)
                have hnk : ¬ (2 + k.val < 2) := by omega
                simp [hr, hne', hnk])]
              have hnk : ¬ (2 + (r.val - 2) < 2) := by omega
              have heq : (⟨r.val, by omega⟩ : Fin (2 + 2 * n)) = ⟨2 + (r.val - 2), by omega⟩ := Fin.ext (by dsimp; omega)
              have hne' : (⟨c.val, by omega⟩ : Fin (2 + 2 * n)) ≠ ⟨2 + (r.val - 2), by omega⟩ := fin_ne_of_val (by dsimp; omega)
              simp only [hr, hc, hnk, heq, hne', ↓reduceDIte, ↓reduceIte, Int.add_zero, Int.zero_add, Int.one_mul]
              congr 1; apply Fin.ext; dsimp; omega
          · omega
        · rw [← Int.zero_add (if r = c then (1 : Int) else 0)]
          refine int_add_congr ?_ ?_
          · exact sumFin_eq_zero (fun k => by
              have hne : (⟨c.val, by omega⟩ : Fin (2 + 2 * n)) ≠ ⟨k.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
              simp [hc, hne])
          · rw [sumFin_single ⟨r.val - 2, by omega⟩ _ (fun k hk => by
              have hne' : (⟨r.val, by omega⟩ : Fin (2 + 2 * n)) ≠ ⟨2 + k.val, by omega⟩ := fin_ne_of_val (by intro h; apply hk; apply Fin.ext; dsimp at h ⊢; omega)
              have hnk : ¬ (2 + k.val < 2) := by omega
              simp [hr, hne', hnk])]
            have hnk : ¬ (2 + (r.val - 2) < 2) := by omega
            have heq : (⟨r.val, by omega⟩ : Fin (2 + 2 * n)) = ⟨2 + (r.val - 2), by omega⟩ := Fin.ext (by dsimp; omega)
            have hiff : (⟨c.val, by omega⟩ : Fin (2 + 2 * n)) = ⟨2 + (r.val - 2), by omega⟩ ↔ r = c := by
              simp only [Fin.ext_iff]; omega
            simp [hr, hc, hnk, heq, hiff]
      have hEd'_Ed : matMul Ed' Ed = scaleMat p (matId (2 * (n + 1))) := by
        funext r c; unfold matMul scaleMat matId; dsimp only [Ed', Ed]
        rw [sumFin_single r _ (fun k hk => by simp [Ne.symm hk])]
        by_cases hrc : r = c
        · subst hrc; by_cases hr : r.val < 2 <;> simp [hr]
        · simp [hrc]
      have hEswap_sq : matMul Eswap Eswap = matId (2 * (n + 1)) := by
        funext r c; dsimp only [Eswap]; by_cases hji1 : j = i1
        · simp only [hji1, ↓reduceIte]; exact congrFun (congrFun (matMul_matId_left _) r) c
        · simp only [hji1, ↓reduceIte]; unfold matMul elemSwap matId
          rw [sumFin_single (swapIdx i1 j c) _ (fun k hk => by simp [hk])]
          have hiff : (r = swapIdx i1 j (swapIdx i1 j c)) ↔ r = c := by rw [swapIdx_invol]
          simp [hiff]
      have hG_cancel : matMul G (matMul (matTrans Ux) (matMul Ed Eswap)) = scaleMat p (matId (2 * (n + 1))) := by
        dsimp only [G]
        rw [matMul_assoc, matMul_assoc, ← matMul_assoc UxT_inv (matTrans Ux), hUx_inv, matMul_matId_left,
            ← matMul_assoc Ed' Ed, hEd'_Ed]
        -- scaleMat p (matId _) commutes with Eswap!
        funext r c; unfold matMul scaleMat matId
        have h1 : ∀ k, sumFin (fun l => (if k = l then p * 1 else 0) * Eswap l c) = p * Eswap k c := by
          intro k; rw [sumFin_single k _ (fun l hl => by simp [Ne.symm hl])]; simp
        have h2 : sumFin (fun k => Eswap r k * (p * Eswap k c)) = p * matMul Eswap Eswap r c := by
          unfold matMul; rw [← sumFin_mul_left]
          exact sumFin_congr (fun k => by ac_rfl)
        calc sumFin (fun k => Eswap r k * sumFin (fun l => p * (if k = l then 1 else 0) * Eswap l c))
            = sumFin (fun k => Eswap r k * (p * Eswap k c)) := by
                apply sumFin_congr; intro k; congr 1
                rw [sumFin_single k _ (fun l hl => by simp [Ne.symm hl])]; simp
          _ = p * matMul Eswap Eswap r c := h2
          _ = p * (if r = c then 1 else 0) := by rw [hEswap_sq]; rfl
      -- Compute pfaffian of congruence (I ⊕ Ed') and (I ⊕ UxT_inv) and (I ⊕ (p * I))
      have hpf_Ed' : ∀ (M : Mat (2 * (m + (n + 1)))),
          pfaffian (m + (n + 1)) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) Ed')) M) =
          p * p * pfaffian (m + (n + 1)) M := by
        intro M
        let sc : Fin (2 * (m + (n + 1))) → Int := fun i =>
          if 2 * m ≤ i.val ∧ i.val < 2 * m + 2 then p else 1
        have heq : congruence (castMat (by omega) (blockDiag (matId (2 * m)) Ed')) M = diagCong sc M := by
          funext r c; unfold congruence matMul matTrans diagCong
          have hE : ∀ u v : Fin (2 * (m + (n + 1))),
              castMat (by omega) (blockDiag (matId (2 * m)) Ed') u v = if u = v then sc u else 0 := by
            intro u v; unfold castMat blockDiag matId; dsimp only [Ed', sc]
            by_cases hu : u.val < 2 * m <;> by_cases hv : v.val < 2 * m
            · have h2 : ¬ (2 * m ≤ u.val ∧ u.val < 2 * m + 2) := by omega
              simp [hu, hv, h2, Fin.ext_iff]
            · have hne : u ≠ v := fin_ne_of_val (by omega); simp [hu, hv, hne]
            · have hne : u ≠ v := fin_ne_of_val (by omega); simp [hu, hv, hne]
            · have hiff1 : (⟨u.val - 2 * m, by omega⟩ : Fin (2 * (n + 1))) = ⟨v.val - 2 * m, by omega⟩ ↔ u = v := by
                simp only [Fin.ext_iff]; omega
              have hiff2 : (u.val - 2 * m < 2) ↔ (2 * m ≤ u.val ∧ u.val < 2 * m + 2) := by omega
              simp [hu, hv, hiff1, hiff2]
          have h1 : ∀ k, sumFin (fun l => M k l * castMat (by omega) (blockDiag (matId (2 * m)) Ed') l c) = M k c * sc c := by
            intro k; rw [sumFin_congr (fun l => by rw [hE l c]), sumFin_single c _ (fun l hl => by simp [hl])]; simp
          simp only [h1]
          rw [sumFin_congr (fun k => by rw [hE k r]), sumFin_single r _ (fun k hk => by simp [hk])]
          simp [Int.mul_assoc]
        rw [heq, pfaffian_diagCong]
        congr 1
        rw [← prodFin_cast (show 2 * m + (2 + 2 * n) = 2 * (m + (n + 1)) by omega) sc, prodFin_split]
        have hL : prodFin (fun i : Fin (2 * m) => sc ⟨i.val, by omega⟩) = 1 := by
          have : prodFin (fun i : Fin (2 * m) => sc ⟨i.val, by omega⟩) = prodFin (fun _ : Fin (2 * m) => (1 : Int)) :=
            prodFin_congr (fun i => by
              dsimp only [sc]
              have hni : ¬ (2 * m ≤ (⟨i.val, by omega⟩ : Fin (2 * (m + (n + 1)))).val ∧
                            (⟨i.val, by omega⟩ : Fin (2 * (m + (n + 1)))).val < 2 * m + 2) := by dsimp; omega
              simp only [hni, ↓reduceIte])
          rw [this, prodFin_const]; exact Int.one_pow
        rw [hL, Int.one_mul, prodFin_split]
        have hM : prodFin (fun i : Fin 2 => sc ⟨2 * m + i.val, by omega⟩) = p * p := by
          change sc ⟨2 * m + 0, by omega⟩ * (sc ⟨2 * m + 1, by omega⟩ * 1) = p * p
          dsimp [sc]; simp
        have hR : prodFin (fun j : Fin (2 * n) => sc ⟨2 * m + (2 + j.val), by omega⟩) = 1 := by
          have : prodFin (fun j : Fin (2 * n) => sc ⟨2 * m + (2 + j.val), by omega⟩) = prodFin (fun _ : Fin (2 * n) => (1 : Int)) :=
            prodFin_congr (fun j => by
              dsimp only [sc]
              have hnj : ¬ (2 * m ≤ (⟨2 * m + (2 + j.val), by omega⟩ : Fin (2 * (m + (n + 1)))).val ∧
                            (⟨2 * m + (2 + j.val), by omega⟩ : Fin (2 * (m + (n + 1)))).val < 2 * m + 2) := by dsimp; omega
              simp only [hnj, ↓reduceIte])
          rw [this, prodFin_const]; exact Int.one_pow
        rw [hM, hR, Int.mul_one]
      have hpf_UxT_inv : ∀ (M : Mat (2 * (m + (n + 1)))), IsSkew M →
          pfaffian (m + (n + 1)) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) UxT_inv)) M) =
          pfaffian (m + (n + 1)) M := by
        intro M hM
        let Yext : Fin (2 * n) → Fin (2 * m + 2) → Int := fun r c =>
          if hc : c.val < 2 * m then 0 else -X ⟨c.val - 2 * m, by omega⟩ r
        have heq : castMat (by omega) (blockDiag (matId (2 * m)) UxT_inv) =
                   castMat (show (2 * m + 2) + 2 * n = 2 * (m + (n + 1)) by omega) (blockLowerId Yext) := by
          funext r c; unfold castMat blockDiag matId blockLowerId; dsimp only [UxT_inv, Yext, negXT]
          unfold castMat blockLowerId; dsimp only
          by_cases hr : r.val < 2 * m <;> by_cases hc : c.val < 2 * m
          · have hr2 : r.val < 2 * m + 2 := by omega
            simp [hr, hc, hr2, Fin.ext_iff]
          · have hr2 : r.val < 2 * m + 2 := by omega
            have hne : r.val ≠ c.val := by omega
            simp [hr, hc, hr2, hne, Fin.ext_iff]
          · have hc2 : c.val < 2 * m + 2 := by omega
            have hne : r.val ≠ c.val := by omega
            by_cases hr2 : r.val < 2 * m + 2 <;> simp [hr, hc, hr2, hc2, hne, Fin.ext_iff]
          · have hiff1 : (⟨r.val - 2 * m, by omega⟩ : Fin (2 + 2 * n)) = ⟨c.val - 2 * m, by omega⟩ ↔
                         (⟨r.val, by omega⟩ : Fin ((2 * m + 2) + 2 * n)) = ⟨c.val, by omega⟩ := by
              simp only [Fin.ext_iff]; omega
            by_cases hr2 : r.val < 2 * m + 2 <;> by_cases hc2 : c.val < 2 * m + 2
            · have hr' : r.val - 2 * m < 2 := by omega
              simp [hr, hc, hr2, hr', hiff1]
            · have hr' : r.val - 2 * m < 2 := by omega
              simp [hr, hc, hr2, hr', hiff1]
            · have hr' : ¬ (r.val - 2 * m < 2) := by omega
              have hc' : c.val - 2 * m < 2 := by omega
              simp only [hr, hc, hr2, hc2, hr', hc', ↓reduceDIte, hiff1]
              congr 1
            · have hr' : ¬ (r.val - 2 * m < 2) := by omega
              have hc' : ¬ (c.val - 2 * m < 2) := by omega
              simp [hr, hc, hr2, hc2, hr', hc', hiff1]
        rw [heq]
        exact pfaffian_blockLowerId (show (2 * m + 2) + 2 * n = 2 * (m + (n + 1)) by omega) Yext hM
      have hpf_pI : ∀ (M : Mat (2 * (m + (n + 1)))),
          pfaffian (m + (n + 1)) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) (scaleMat p (matId (2 * (n + 1)))))) M) =
          p ^ (2 * (n + 1)) * pfaffian (m + (n + 1)) M := by
        intro M
        let sc : Fin (2 * (m + (n + 1))) → Int := fun i => if i.val < 2 * m then 1 else p
        have heq : congruence (castMat (by omega) (blockDiag (matId (2 * m)) (scaleMat p (matId (2 * (n + 1)))))) M = diagCong sc M := by
          funext r c; unfold congruence matMul matTrans diagCong
          have hE : ∀ u v : Fin (2 * (m + (n + 1))),
              castMat (by omega) (blockDiag (matId (2 * m)) (scaleMat p (matId (2 * (n + 1))))) u v =
              if u = v then sc u else 0 := by
            intro u v; unfold castMat blockDiag matId scaleMat; dsimp only [sc]
            by_cases hu : u.val < 2 * m <;> by_cases hv : v.val < 2 * m
            · simp [hu, hv, Fin.ext_iff]
            · have hne : u ≠ v := fin_ne_of_val (by omega); simp [hu, hv, hne]
            · have hne : u ≠ v := fin_ne_of_val (by omega); simp [hu, hv, hne]
            · have hiff1 : (⟨u.val - 2 * m, by omega⟩ : Fin (2 * (n + 1))) = ⟨v.val - 2 * m, by omega⟩ ↔ u = v := by
                simp only [Fin.ext_iff]; omega
              by_cases huv : u = v <;> simp [hu, hv, hiff1, huv]
          have h1 : ∀ k, sumFin (fun l => M k l * castMat (by omega) (blockDiag (matId (2 * m)) (scaleMat p (matId (2 * (n + 1))))) l c) = M k c * sc c := by
            intro k; rw [sumFin_congr (fun l => by rw [hE l c]), sumFin_single c _ (fun l hl => by simp [hl])]; simp
          simp only [h1]
          rw [sumFin_congr (fun k => by rw [hE k r]), sumFin_single r _ (fun k hk => by simp [hk])]
          simp [Int.mul_assoc]
        rw [heq, pfaffian_diagCong]
        congr 1
        rw [← prodFin_cast (show 2 * m + 2 * (n + 1) = 2 * (m + (n + 1)) by omega) sc, prodFin_split]
        have hL : prodFin (fun i : Fin (2 * m) => sc ⟨i.val, by omega⟩) = 1 := by
          have : prodFin (fun i : Fin (2 * m) => sc ⟨i.val, by omega⟩) = prodFin (fun _ : Fin (2 * m) => (1 : Int)) :=
            prodFin_congr (fun i => by dsimp only [sc]; simp [i.isLt])
          rw [this, prodFin_const]; exact Int.one_pow
        have hR : prodFin (fun j : Fin (2 * (n + 1)) => sc ⟨2 * m + j.val, by omega⟩) = p ^ (2 * (n + 1)) := by
          have : prodFin (fun j : Fin (2 * (n + 1)) => sc ⟨2 * m + j.val, by omega⟩) = prodFin (fun _ : Fin (2 * (n + 1)) => p) :=
            prodFin_congr (fun j => by
              dsimp only [sc]
              have hnj : ¬ ((⟨2 * m + j.val, by omega⟩ : Fin (2 * (m + (n + 1)))).val < 2 * m) := by dsimp; omega
              simp only [hnj, ↓reduceIte])
          rw [this, prodFin_const]
        rw [hL, hR, Int.one_mul]
      -- Now evaluate `pfaffian` on `congruence (I ⊕ (G * (E^T D1 E))) A` in TWO ways!
      let A0 : Mat (2 * (m + (n + 1))) := congruence (castMat (by omega) (blockDiag (matId (2 * m)) G)) A
      have hA0_skew : IsSkew A0 := isSkew_congruence _ _ hA
      have hpf_A0 : pfaffian (m + (n + 1)) A0 = (if j = i1 then 1 else -1) * (p * p) * pfaffian (m + (n + 1)) A := by
        dsimp only [A0, G]
        have hfac : castMat (show 2 * m + 2 * (n + 1) = 2 * (m + (n + 1)) by omega)
            (blockDiag (matId (2 * m)) (matMul Eswap (matMul Ed' UxT_inv))) =
            matMul (castMat (by omega) (blockDiag (matId (2 * m)) Eswap))
              (matMul (castMat (by omega) (blockDiag (matId (2 * m)) Ed'))
                (castMat (by omega) (blockDiag (matId (2 * m)) UxT_inv))) := by
          simp only [matMul_castMat, matMul_blockDiag, matMul_matId_left]
        rw [hfac, congruence_comp, congruence_comp,
            hpf_UxT_inv _ (isSkew_congruence _ _ (isSkew_congruence _ _ hA)),
            hpf_Ed', hpf_Eswap _ hA]
        ac_rfl
      -- Way 1: G * (E^T D1 E) = (p * I) * D * (Eswap * Ed * Ux) = D * (p * I) * Eswap * Ed * Ux!
      have hWay1 : pfaffian (m + (n + 1)) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) (congruence E D1))) A0) =
          (if j = i1 then 1 else -1) * p ^ (2 * n) * p ^ (2 * (n + 1)) *
          pfaffian (m + (n + 1)) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) D)) A) := by
        dsimp only [A0]
        rw [← congruence_comp]
        have hEdT : matTrans Ed = Ed := by
          funext r c; dsimp only [Ed]; unfold matTrans; by_cases h : r = c
          · subst h; simp
          · simp [h, Ne.symm h]
        have hEswapT : matTrans Eswap = Eswap := by
          dsimp only [Eswap]; split
          · exact matTrans_matId _
          · exact matTrans_elemSwap _ _
        have hGDE : matMul G (congruence E D1) =
            matMul D (matMul (scaleMat p (matId (2 * (n + 1)))) (matMul Eswap (matMul Ed Ux))) := by
          dsimp only [D1, E]; unfold congruence
          rw [matTrans_mul, hEdT, hEswapT]
          have h1 : matMul G (matMul (matMul (matTrans Ux) Ed) (matMul (matMul Eswap (matMul D Eswap)) (matMul Ed Ux))) =
                    matMul (matMul G (matMul (matTrans Ux) (matMul Ed Eswap))) (matMul D (matMul Eswap (matMul Ed Ux))) := by
            simp only [matMul_assoc]
          rw [h1, hG_cancel]
          have hcomm_p : matMul (scaleMat p (matId (2 * (n + 1)))) D = matMul D (scaleMat p (matId (2 * (n + 1)))) := by
            funext r c; unfold matMul scaleMat matId
            rw [sumFin_single r _ (fun k hk => by simp [Ne.symm hk])]
            rw [sumFin_single c _ (fun k hk => by simp [hk])]
            simp [Int.mul_comm]
          rw [← matMul_assoc (scaleMat p (matId _)) D, hcomm_p, matMul_assoc]
        have hfac : matMul (castMat (show 2 * m + 2 * (n + 1) = 2 * (m + (n + 1)) by omega) (blockDiag (matId (2 * m)) G))
            (castMat (by omega) (blockDiag (matId (2 * m)) (congruence E D1))) =
            matMul (castMat (by omega) (blockDiag (matId (2 * m)) D))
              (matMul (castMat (by omega) (blockDiag (matId (2 * m)) (scaleMat p (matId (2 * (n + 1))))))
                (matMul (castMat (by omega) (blockDiag (matId (2 * m)) Eswap))
                  (matMul (castMat (by omega) (blockDiag (matId (2 * m)) Ed))
                    (castMat (by omega) (blockDiag (matId (2 * m)) Ux))))) := by
          simp only [matMul_castMat, matMul_blockDiag, matMul_matId_left, hGDE]
        rw [hfac]
        simp only [congruence_comp]
        rw [hpf_Ux _ (isSkew_congruence _ _ (isSkew_congruence _ _ (isSkew_congruence _ _ (isSkew_congruence _ _ hA)))),
            hpf_Ed,
            hpf_Eswap _ (isSkew_congruence _ _ (isSkew_congruence _ _ hA)),
            hpf_pI]
        simp only [Int.mul_assoc]
        rw [Int.mul_left_comm (p ^ (2 * n)) (if j = i1 then 1 else -1)]
      -- Way 2: congruence E D1 = P0 ⊕ S! Factor (I_{2m} ⊕ (P0 ⊕ S)) = (I_{2m} ⊕ P0 ⊕ I_{2n}) * (I_{2m+2} ⊕ S)!
      have hWay2 : pfaffian (m + (n + 1)) (congruence (castMat (by omega) (blockDiag (matId (2 * m)) (congruence E D1))) A0) =
          p * p * (pfaffian n S * pfaffian n S) * pfaffian (m + (n + 1)) A0 := by
        rw [hcong_E]
        -- Factor blockDiag I_{2m} (P0 ⊕ S) = (I_{2m} ⊕ P0 ⊕ I_{2n}) * (I_{2(m+1)} ⊕ S)
        let P0ext : Mat (2 * (m + (n + 1))) :=
          matMul (elemSwap ⟨2 * m, by omega⟩ ⟨2 * m + 1, by omega⟩)
            (matMul (elemScale ⟨2 * m, by omega⟩ (-p)) (elemScale ⟨2 * m + 1, by omega⟩ p))
        let Sext : Mat (2 * (m + (n + 1))) :=
          castMat (show 2 * (m + 1) + 2 * n = 2 * (m + (n + 1)) by omega) (blockDiag (matId (2 * (m + 1))) S)
        have hP0_entry : ∀ r c : Fin (2 * (m + (n + 1))), P0ext r c =
            if r.val = 2 * m ∧ c.val = 2 * m + 1 then p
            else if r.val = 2 * m + 1 ∧ c.val = 2 * m then -p
            else if r = c ∧ r.val ≠ 2 * m ∧ r.val ≠ 2 * m + 1 then 1 else 0 := by
          intro r c; dsimp only [P0ext]; unfold matMul elemSwap elemScale
          have h1 : ∀ k : Fin (2 * (m + (n + 1))),
              sumFin (fun l => (if k = l then (if k = ⟨2 * m, by omega⟩ then -p else 1) else 0) *
                               (if l = c then (if l = ⟨2 * m + 1, by omega⟩ then p else 1) else 0)) =
              if k = c then (if c = ⟨2 * m, by omega⟩ then -p else if c = ⟨2 * m + 1, by omega⟩ then p else 1) else 0 := by
            intro k
            rw [sumFin_single c _ (fun l hl => by simp [hl])]
            by_cases hkc : k = c
            · subst hkc
              by_cases h1 : k = ⟨2 * m, by omega⟩
              · simp [h1]
              · by_cases h2 : k = ⟨2 * m + 1, by omega⟩ <;> simp [h1, h2]
            · simp [hkc]
          simp only [h1]
          rw [sumFin_single c _ (fun k hk => by simp [hk])]
          by_cases hc0 : c.val = 2 * m
          · have hsw : swapIdx ⟨2 * m, by omega⟩ ⟨2 * m + 1, by omega⟩ c = ⟨2 * m + 1, by omega⟩ := by
              apply Fin.ext; unfold swapIdx; simp [Fin.ext_iff, hc0]
            rw [hsw]
            by_cases hr1 : r.val = 2 * m + 1
            · simp [hr1, hc0, Fin.ext_iff]
            · simp [hr1, hc0, Fin.ext_iff]
          · by_cases hc1 : c.val = 2 * m + 1
            · have hsw : swapIdx ⟨2 * m, by omega⟩ ⟨2 * m + 1, by omega⟩ c = ⟨2 * m, by omega⟩ := by
                apply Fin.ext; unfold swapIdx; simp [Fin.ext_iff, hc1]
              rw [hsw]
              by_cases hr0 : r.val = 2 * m
              · simp [hr0, hc1, Fin.ext_iff]
              · simp [hr0, hc1, Fin.ext_iff]
            · have hcne0 : c ≠ ⟨2 * m, by omega⟩ := fin_ne_of_val (by dsimp; omega)
              have hcne1 : c ≠ ⟨2 * m + 1, by omega⟩ := fin_ne_of_val (by dsimp; omega)
              rw [swapIdx_other hcne0 hcne1]
              by_cases hrc : r = c
              · subst hrc; simp [hc0, hc1, hcne0, hcne1]
              · simp [hrc, hc0, hc1, hcne0, hcne1]
        have hfac2 : castMat (show 2 * m + 2 * (n + 1) = 2 * (m + (n + 1)) by omega)
            (blockDiag (matId (2 * m)) (castMat (show 2 + 2 * n = 2 * (n + 1) by omega) (blockDiag P0 S))) =
            matMul P0ext Sext := by
          funext r c
          unfold matMul; rw [sumFin_congr (fun k => by rw [hP0_entry r k])]
          dsimp only [Sext]; unfold castMat blockDiag matId; dsimp only
          by_cases hr0 : r.val = 2 * m
          · have h1 : sumFin (fun k : Fin (2 * (m + (n + 1))) =>
                (if r.val = 2 * m ∧ k.val = 2 * m + 1 then p
                 else if r.val = 2 * m + 1 ∧ k.val = 2 * m then -p
                 else if r = k ∧ r.val ≠ 2 * m ∧ r.val ≠ 2 * m + 1 then 1 else 0) *
                (if hk : k.val < 2 * (m + 1) then
                  if hc : c.val < 2 * (m + 1) then (if (⟨k.val, hk⟩ : Fin (2 * (m + 1))) = ⟨c.val, hc⟩ then 1 else 0) else 0
                else if hc : c.val < 2 * (m + 1) then 0 else S ⟨k.val - 2 * (m + 1), by omega⟩ ⟨c.val - 2 * (m + 1), by omega⟩)) =
                if c.val = 2 * m + 1 then p else 0 := by
              rw [sumFin_single ⟨2 * m + 1, by omega⟩ _ (fun k hk => by
                have : k.val ≠ 2 * m + 1 := fun h => hk (Fin.ext h)
                simp [hr0, this])]
              have hlt : 2 * m + 1 < 2 * (m + 1) := by omega
              by_cases hc : c.val < 2 * (m + 1)
              · by_cases hc1 : c.val = 2 * m + 1
                · have heq : (⟨2 * m + 1, hlt⟩ : Fin (2 * (m + 1))) = ⟨c.val, hc⟩ := Fin.ext (by dsimp; omega)
                  simp [hr0, hlt, hc1, heq]
                · have hne : (⟨2 * m + 1, hlt⟩ : Fin (2 * (m + 1))) ≠ ⟨c.val, hc⟩ := fin_ne_of_val (by dsimp; omega)
                  simp [hr0, hc, hlt, hc1, hne]
              · have hc1 : c.val ≠ 2 * m + 1 := by omega
                simp [hr0, hc, hlt, hc1]
            rw [h1]
            have hrnm : ¬ (r.val < 2 * m) := by omega
            have hr2 : r.val - 2 * m < 2 := by omega
            by_cases hc : c.val < 2 * m
            · have hc1 : c.val ≠ 2 * m + 1 := by omega
              simp [hrnm, hc, hc1]
            · by_cases hc2 : c.val - 2 * m < 2
              · by_cases hc1 : c.val = 2 * m + 1
                · simp only [hrnm, hc, hr2, hc2, ↓reduceDIte]; simp only [hc1, ↓reduceIte]
                  dsimp only [P0, p, i0, i1]
                  congr 1 <;> (apply Fin.ext; dsimp; omega)
                · have hc0 : c.val = 2 * m := by omega
                  simp only [hrnm, hc, hr2, hc2, ↓reduceDIte]; simp only [hc1, ↓reduceIte]
                  dsimp only [P0]
                  have heq : (⟨r.val - 2 * m, by omega⟩ : Fin (2 * (n + 1))) = ⟨c.val - 2 * m, by omega⟩ := Fin.ext (by dsimp; omega)
                  rw [heq, hD1_skew.1]
              · have hc1 : c.val ≠ 2 * m + 1 := by omega
                simp [hrnm, hc, hr2, hc2, hc1]
          · by_cases hr1 : r.val = 2 * m + 1
            · have h1 : sumFin (fun k : Fin (2 * (m + (n + 1))) =>
                  (if r.val = 2 * m ∧ k.val = 2 * m + 1 then p
                   else if r.val = 2 * m + 1 ∧ k.val = 2 * m then -p
                   else if r = k ∧ r.val ≠ 2 * m ∧ r.val ≠ 2 * m + 1 then 1 else 0) *
                  (if hk : k.val < 2 * (m + 1) then
                    if hc : c.val < 2 * (m + 1) then (if (⟨k.val, hk⟩ : Fin (2 * (m + 1))) = ⟨c.val, hc⟩ then 1 else 0) else 0
                  else if hc : c.val < 2 * (m + 1) then 0 else S ⟨k.val - 2 * (m + 1), by omega⟩ ⟨c.val - 2 * (m + 1), by omega⟩)) =
                  if c.val = 2 * m then -p else 0 := by
                rw [sumFin_single ⟨2 * m, by omega⟩ _ (fun k hk => by
                  have : k.val ≠ 2 * m := fun h => hk (Fin.ext h)
                  simp [hr1, this])]
                have hlt : 2 * m < 2 * (m + 1) := by omega
                by_cases hc : c.val < 2 * (m + 1)
                · by_cases hc0 : c.val = 2 * m
                  · have heq : (⟨2 * m, hlt⟩ : Fin (2 * (m + 1))) = ⟨c.val, hc⟩ := Fin.ext (by dsimp; omega)
                    simp [hr1, hlt, hc0, heq]
                  · have hne : (⟨2 * m, hlt⟩ : Fin (2 * (m + 1))) ≠ ⟨c.val, hc⟩ := fin_ne_of_val (by dsimp; omega)
                    simp [hr1, hc, hlt, hc0, hne]
                · have hc0 : c.val ≠ 2 * m := by omega
                  simp [hr1, hc, hlt, hc0]
              rw [h1]
              have hrnm : ¬ (r.val < 2 * m) := by omega
              have hr2 : r.val - 2 * m < 2 := by omega
              by_cases hc : c.val < 2 * m
              · have hc0 : c.val ≠ 2 * m := by omega
                simp [hrnm, hc, hc0]
              · by_cases hc2 : c.val - 2 * m < 2
                · by_cases hc0 : c.val = 2 * m
                  · simp only [hrnm, hc, hr2, hc2, ↓reduceDIte]; simp only [hc0, ↓reduceIte]
                    dsimp only [P0, p, i0, i1]
                    rw [hD1_skew.2]; congr 1
                    congr 1 <;> (apply Fin.ext; dsimp; omega)
                  · have hc1 : c.val = 2 * m + 1 := by omega
                    simp only [hrnm, hc, hr2, hc2, ↓reduceDIte]; simp only [hc0, ↓reduceIte]
                    dsimp only [P0]
                    have heq : (⟨r.val - 2 * m, by omega⟩ : Fin (2 * (n + 1))) = ⟨c.val - 2 * m, by omega⟩ := Fin.ext (by dsimp; omega)
                    rw [heq, hD1_skew.1]
                · have hc0 : c.val ≠ 2 * m := by omega
                  simp [hrnm, hc, hr2, hc2, hc0]
            · rw [sumFin_single r _ (fun k hk => by simp [hr0, hr1, Ne.symm hk])]
              simp [hr0, hr1]
              by_cases hr : r.val < 2 * m
              · have hr2 : r.val < 2 * (m + 1) := by omega
                by_cases hc : c.val < 2 * m
                · have hc2 : c.val < 2 * (m + 1) := by omega
                  simp [hr, hr2, hc, hc2]
                · by_cases hc2 : c.val < 2 * (m + 1)
                  · have hne : r.val ≠ c.val := by omega
                    simp [hr, hr2, hc, hc2, hne]
                  · simp [hr, hr2, hc, hc2]
              · have hr2 : ¬ (r.val < 2 * (m + 1)) := by omega
                have hr2' : ¬ (r.val - 2 * m < 2) := by omega
                by_cases hc : c.val < 2 * m
                · have hc2 : c.val < 2 * (m + 1) := by omega
                  simp [hr, hr2, hc, hc2]
                · by_cases hc2 : c.val < 2 * (m + 1)
                  · have hc2' : c.val - 2 * m < 2 := by omega
                    simp [hr, hr2, hr2', hc, hc2, hc2']
                  · have hc2' : ¬ (c.val - 2 * m < 2) := by omega
                    simp only [hr, hr2, hr2', hc, hc2, hc2', ↓reduceDIte]
                    have hr' : (⟨r.val - 2 * m - 2, by omega⟩ : Fin (2 * n)) = ⟨r.val - 2 * (m + 1), by omega⟩ :=
                      Fin.ext (by dsimp; omega)
                    have hc' : (⟨c.val - 2 * m - 2, by omega⟩ : Fin (2 * n)) = ⟨c.val - 2 * (m + 1), by omega⟩ :=
                      Fin.ext (by dsimp; omega)
                    rw [hr', hc']
        rw [hfac2, congruence_comp]
        have hih_S := pfaffian_congruence_blockIdSkew n (m + 1) S
          (castMat (show 2 * (m + (n + 1)) = 2 * ((m + 1) + n) by omega) (congruence P0ext A0))
          hS_skew
          (⟨fun r => (isSkew_congruence P0ext A0 hA0_skew).1 _, fun r c => (isSkew_congruence P0ext A0 hA0_skew).2 _ _⟩)
        have hcast_S : pfaffian (m + (n + 1)) (congruence Sext (congruence P0ext A0)) =
                       pfaffian ((m + 1) + n) (congruence (castMat (by omega) (blockDiag (matId (2 * (m + 1))) S))
                         (castMat (show 2 * (m + (n + 1)) = 2 * ((m + 1) + n) by omega) (congruence P0ext A0))) := by
          rw [← pfaffian_castMat (show m + (n + 1) = (m + 1) + n by omega)]
          apply pfaffian_congr; intro r c
          dsimp only [Sext]; unfold castMat congruence matMul matTrans
          rw [← sumFin_cast (show 2 * ((m + 1) + n) = 2 * (m + (n + 1)) by omega)]
          apply sumFin_congr; intro k; congr 1
          rw [← sumFin_cast (show 2 * ((m + 1) + n) = 2 * (m + (n + 1)) by omega)]
        rw [hcast_S, hih_S, pfaffian_castMat (show m + (n + 1) = (m + 1) + n by omega)]
        -- Evaluate pfaffian (congruence P0ext A0) = p * p * pfaffian A0!
        have hpf_P0ext : pfaffian (m + (n + 1)) (congruence P0ext A0) = p * p * pfaffian (m + (n + 1)) A0 := by
          dsimp only [P0ext]
          simp only [congruence_comp]
          rw [pfaffian_elemScale_congruence, pfaffian_elemScale_congruence,
              pfaffian_elemSwap_congruence _ _ (fin_ne_of_val (by dsimp; omega)) hA0_skew]
          rw [Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_assoc]
        rw [hpf_P0ext]
        ac_rfl
      -- Combine Way 1 and Way 2, substitute hpf_A0 and hschur_D1, and cancel nonzero factor!
      have hcomb := hWay1.symm.trans hWay2
      rw [hpf_A0] at hcomb
      -- Note: pfaffian D1 = (if j = i1 then 1 else -1) * pfaffian D, so Pf(D1)^2 = Pf(D)^2!
      have hpf_D1_sq : pfaffian (n + 1) D1 * pfaffian (n + 1) D1 = pfaffian (n + 1) D * pfaffian (n + 1) D := by
        dsimp only [D1, Eswap]
        by_cases hji1 : j = i1
        · simp only [hji1, ↓reduceIte, congruence_id]
        · simp only [hji1, ↓reduceIte, pfaffian_elemSwap_congruence _ _ (Ne.symm hji1) hD]
          rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      have hp_ne0 : p ≠ 0 := hD1_01
      have hpow_ne0 : ∀ k : Nat, p ^ k ≠ 0 := by
        intro k; induction k with
        | zero => simp
        | succ k ih => rw [Int.pow_succ]; exact Int.mul_ne_zero ih hp_ne0
      have hsign_ne0 : (if j = i1 then (1 : Int) else -1) ≠ 0 := by split <;> decide
      have hfac_ne0 : (if j = i1 then (1 : Int) else -1) * p ^ (2 * n) * p ^ (2 * (n + 1)) ≠ 0 :=
        Int.mul_ne_zero (Int.mul_ne_zero hsign_ne0 (hpow_ne0 _)) (hpow_ne0 _)
      apply Int.eq_of_mul_eq_mul_left hfac_ne0
      rw [hcomb]
      -- Show RHS equals hfac * (Pf(D)^2 * Pf(A)) using hschur_D1: p^(2n) * Pf(D1) = p * Pf(S)!
      have hsq_schur : p * p * (pfaffian n S * pfaffian n S) =
                       p ^ (2 * n) * p ^ (2 * n) * (pfaffian (n + 1) D * pfaffian (n + 1) D) := by
        have h1 : (p * pfaffian n S) * (p * pfaffian n S) =
                  (p ^ (2 * n) * pfaffian (n + 1) D1) * (p ^ (2 * n) * pfaffian (n + 1) D1) := by
          rw [hschur_D1]
        have hL : (p * pfaffian n S) * (p * pfaffian n S) = p * p * (pfaffian n S * pfaffian n S) := by ac_rfl
        have hR : (p ^ (2 * n) * pfaffian (n + 1) D1) * (p ^ (2 * n) * pfaffian (n + 1) D1) =
                  p ^ (2 * n) * p ^ (2 * n) * (pfaffian (n + 1) D1 * pfaffian (n + 1) D1) := by ac_rfl
        rw [hL, hR, hpf_D1_sq] at h1
        exact h1
      have hpow_split : p ^ (2 * (n + 1)) = p ^ (2 * n) * (p * p) := by
        have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
        rw [h2, Int.pow_add, Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
      rw [hsq_schur, hpow_split]
      ac_rfl
    · -- Row 0 of D is all zeros!
      have hrow0_D : ∀ j, D ⟨0, by omega⟩ j = 0 := by
        intro j; exact Classical.byContradiction (fun hne => hex ⟨j, hne⟩)
      have hpfD : pfaffian (n + 1) D = 0 := pfaffian_zero_row0 hrow0_D
      rw [hpfD]; simp only [Int.zero_mul]
      apply pfaffian_zero_row ⟨2 * m, by omega⟩ (isSkew_congruence _ _ hA)
      intro j
      unfold congruence matMul matTrans
      apply sumFin_eq_zero; intro k
      have hcol : castMat (show 2 * m + 2 * (n + 1) = 2 * (m + (n + 1)) by omega)
          (blockDiag (matId (2 * m)) D) k ⟨2 * m, by omega⟩ = 0 := by
        unfold castMat blockDiag matId
        have hnm : ¬ (2 * m < 2 * m) := by omega
        by_cases hk : k.val < 2 * m
        · simp [hk, hnm]
        · simp only [hk, hnm, ↓reduceDIte]
          have h0 : (⟨2 * m - 2 * m, by omega⟩ : Fin (2 * (n + 1))) = ⟨0, by omega⟩ := Fin.ext (by simp)
          rw [h0, hD.2, hrow0_D]; rfl
      rw [hcol, Int.zero_mul]

/-- Reusable Mechanism 3: Skew-Conference Complementary-Minor Reflection Theorem.
    For ANY `2(m+n) × 2(m+n)` skew-symmetric integer matrix `A` satisfying `A^2 = -μ I`,
    let `B` be its leading `2m × 2m` principal submatrix and `D` its trailing `2n × 2n`
    complementary principal submatrix. Then:
      `Pf(D)^2 * Pf(A) = μ^n * Pf(D) * Pf(B)` (and if `Pf(D) ≠ 0`, `Pf(D) * Pf(A) = μ^n * Pf(B)`). -/
theorem pfaffian_skewConference_compl {m n : Nat} (A : Mat (2 * (m + n))) (μ : Int)
    (hA : IsSkew A)
    (hconf : ∀ i j, matMul A A i j = if i = j then -μ else 0) :
    let B : Mat (2 * m) := fun i j => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    let D : Mat (2 * n) := fun i j => A ⟨2 * m + i.val, by omega⟩ ⟨2 * m + j.val, by omega⟩
    pfaffian n D * pfaffian n D * pfaffian (m + n) A =
    μ ^ n * pfaffian n D * pfaffian m B := by
  intro B D
  let C : Fin (2 * m) → Fin (2 * n) → Int := fun i j => A ⟨i.val, by omega⟩ ⟨2 * m + j.val, by omega⟩
  have hD_skew : IsSkew D := ⟨fun i => hA.1 _, fun i j => hA.2 _ _⟩
  -- M = (I_{2m} ⊕ D) * blockUpperId C = [[I, C], [0, D]]!
  let U : Mat (2 * (m + n)) := castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockUpperId C)
  let ID : Mat (2 * (m + n)) := castMat (show 2 * m + 2 * n = 2 * (m + n) by omega) (blockDiag (matId (2 * m)) D)
  -- First, by pfaffian_congruence_blockIdSkew and pfaffian_blockUpperId:
  -- Pf(congruence (ID * U) A) = Pf(congruence U (congruence ID A)) = Pf(congruence ID A) = Pf(D)^2 * Pf(A)!
  have hLHS : pfaffian (m + n) (congruence (matMul ID U) A) =
              pfaffian n D * pfaffian n D * pfaffian (m + n) A := by
    rw [congruence_comp, pfaffian_blockUpperId (show 2 * m + 2 * n = 2 * (m + n) by omega) C (isSkew_congruence _ _ hA)]
    exact pfaffian_congruence_blockIdSkew n m D A hD_skew hA
  -- Second, evaluate congruence (ID * U) A = B ⊕ (μ * D)!
  -- Compute M = ID * U = [[I, C], [0, D]] explicitly:
  have hM_entry : ∀ r c : Fin (2 * (m + n)), matMul ID U r c =
      if hr : r.val < 2 * m then
        if hc : c.val < 2 * m then (if r = c then 1 else 0)
        else C ⟨r.val, hr⟩ ⟨c.val - 2 * m, by omega⟩
      else
        if hc : c.val < 2 * m then 0
        else D ⟨r.val - 2 * m, by omega⟩ ⟨c.val - 2 * m, by omega⟩ := by
    intro r c; unfold matMul; dsimp only [ID, U]; unfold castMat blockDiag matId blockUpperId
    rw [← sumFin_cast (show 2 * m + 2 * n = 2 * (m + n) by omega), sumFin_split]
    by_cases hr : r.val < 2 * m
    · simp only [hr, ↓reduceDIte]
      rw [← Int.add_zero (if hc : c.val < 2 * m then (if r = c then 1 else 0) else C ⟨r.val, hr⟩ ⟨c.val - 2 * m, by omega⟩)]
      refine int_add_congr ?_ ?_
      · rw [sumFin_single ⟨r.val, hr⟩ _ (fun k hk => by
          have hne : (⟨r.val, hr⟩ : Fin (2 * m)) ≠ k := fun h => hk h.symm
          simp [k.isLt, hne])]
        simp only [hr, ↓reduceDIte, ↓reduceIte, Int.one_mul]
        by_cases hc : c.val < 2 * m
        · have hiff : (⟨r.val, by omega⟩ : Fin (2 * m + 2 * n)) = ⟨c.val, by omega⟩ ↔ r = c := by
            simp only [Fin.ext_iff]
          simp [hc, hiff]
        · have hne : (⟨r.val, by omega⟩ : Fin (2 * m + 2 * n)) ≠ ⟨c.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
          simp [hc, hne]
      · exact sumFin_eq_zero (fun k => by
          have hnk : ¬ (2 * m + k.val < 2 * m) := by omega
          simp [hnk])
    · simp only [hr, ↓reduceDIte]
      rw [← Int.zero_add (if hc : c.val < 2 * m then 0 else D ⟨r.val - 2 * m, by omega⟩ ⟨c.val - 2 * m, by omega⟩)]
      refine int_add_congr ?_ ?_
      · exact sumFin_eq_zero (fun k => by simp [k.isLt])
      · by_cases hc : c.val < 2 * m
        · simp only [hc, ↓reduceDIte]
          apply sumFin_eq_zero; intro k
          have hnk : ¬ (2 * m + k.val < 2 * m) := by omega
          have hne : (⟨2 * m + k.val, by omega⟩ : Fin (2 * m + 2 * n)) ≠ ⟨c.val, by omega⟩ := fin_ne_of_val (by dsimp; omega)
          simp [hnk, hne]
        · simp only [hc, ↓reduceDIte]
          rw [sumFin_single ⟨c.val - 2 * m, by omega⟩ _ (fun k hk => by
            have hnk : ¬ (2 * m + k.val < 2 * m) := by omega
            have hne : (⟨2 * m + k.val, by omega⟩ : Fin (2 * m + 2 * n)) ≠ ⟨c.val, by omega⟩ :=
              fin_ne_of_val (by intro h; apply hk; apply Fin.ext; dsimp at h ⊢; omega)
            simp [hnk, hne])]
          have hnk : ¬ (2 * m + (c.val - 2 * m) < 2 * m) := by omega
          have heq : (⟨2 * m + (c.val - 2 * m), by omega⟩ : Fin (2 * m + 2 * n)) = ⟨c.val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          simp only [hnk, heq, ↓reduceDIte, ↓reduceIte, Int.add_zero, Int.mul_one]
          congr 1; apply Fin.ext; dsimp; omega
  have hAM : ∀ r c : Fin (2 * (m + n)), matMul A (matMul ID U) r c =
      if c.val < 2 * m then A r c else if r = c then -μ else 0 := by
    intro r c
    change sumFin (fun k => A r k * matMul ID U k c) = _
    rw [sumFin_congr (fun k => by rw [hM_entry k c])]
    by_cases hc : c.val < 2 * m
    · simp only [hc, ↓reduceIte, ↓reduceDIte]
      rw [sumFin_single c _ (fun k hk => by
        by_cases hkm : k.val < 2 * m <;> simp [hkm, hk])]
      simp [hc]
    · simp only [hc, ↓reduceIte, ↓reduceDIte]
      have hcol : ∀ k : Fin (2 * (m + n)),
          (if hk : k.val < 2 * m then C ⟨k.val, hk⟩ ⟨c.val - 2 * m, by omega⟩
           else D ⟨k.val - 2 * m, by omega⟩ ⟨c.val - 2 * m, by omega⟩) = A k c := by
        intro k; dsimp only [C, D]
        by_cases hk : k.val < 2 * m <;> (simp only [hk, ↓reduceDIte]; congr 1 <;> (apply Fin.ext; dsimp; omega))
      rw [sumFin_congr (fun k => by rw [hcol k])]
      exact hconf r c
  have hMTAM : congruence (matMul ID U) A = castMat (by omega) (blockDiag B (scaleMat μ D)) := by
    funext i j
    change sumFin (fun k => matMul ID U k i * matMul A (matMul ID U) k j) = _
    rw [sumFin_congr (fun k => by rw [hM_entry k i, hAM k j])]
    unfold castMat blockDiag scaleMat
    by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
    · simp only [hi, hj, ↓reduceIte, ↓reduceDIte]
      rw [sumFin_single i _ (fun k hk => by by_cases hkm : k.val < 2 * m <;> simp [hkm, hk])]
      simp only [hi, ↓reduceDIte, ↓reduceIte, Int.one_mul]; rfl
    · simp only [hi, hj, ↓reduceIte, ↓reduceDIte]
      rw [sumFin_single j _ (fun k hk => by simp [hk])]
      simp [hj]
    · simp only [hi, hj, ↓reduceIte, ↓reduceDIte]
      have hcol : ∀ k : Fin (2 * (m + n)),
          (if hk : k.val < 2 * m then C ⟨k.val, hk⟩ ⟨i.val - 2 * m, by omega⟩
           else D ⟨k.val - 2 * m, by omega⟩ ⟨i.val - 2 * m, by omega⟩) * A k j =
          -(A i k * A k j) := by
        intro k; dsimp only [C, D]
        have hAk : (if hk : k.val < 2 * m then A ⟨k.val, by omega⟩ ⟨2 * m + (i.val - 2 * m), by omega⟩
                    else A ⟨2 * m + (k.val - 2 * m), by omega⟩ ⟨2 * m + (i.val - 2 * m), by omega⟩) = A k i := by
          by_cases hk : k.val < 2 * m <;> (simp only [hk, ↓reduceDIte]; congr 1 <;> (apply Fin.ext; dsimp; omega))
        rw [hAk, hA.2 k i, Int.neg_mul]
      rw [sumFin_congr hcol, sumFin_neg]
      have hne : i ≠ j := fin_ne_of_val (by omega)
      have h0 := hconf i j
      unfold matMul at h0
      rw [h0]; simp [hne]
    · simp only [hi, hj, ↓reduceIte, ↓reduceDIte]
      rw [sumFin_single j _ (fun k hk => by simp [hk])]
      simp only [hj, ↓reduceDIte, ↓reduceIte]
      rw [hD_skew.2, Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.mul_comm]
  rw [← hLHS, hMTAM, pfaffian_blockDiag, pfaffian_scaleMat]
  ac_rfl

-- ============================================================================
-- Section 5: Pure-Silicon Bitwise Primitives & Four Novel Infinite Pfaffian Laws
-- ============================================================================

-- 5.1 Bitwise Primitives & Arithmetic-to-Hardware Bridges

theorem pfaffian_skewOnes : ∀ m : Nat, pfaffian m (skewOnesMat (2 * m)) = 1
  | 0 => rfl
  | m + 1 => by
    let A00 : Mat (2 * 1) := skewOnesMat 2
    let A01 : Fin (2 * 1) → Fin (2 * m) → Int := fun _ _ => 1
    let A11 : Mat (2 * m) := skewOnesMat (2 * m)
    let X : Fin (2 * 1) → Fin (2 * m) → Int := fun i _ => if i.val = 0 then 1 else -1
    have hblock : skewOnesMat (2 * (1 + m)) =
        castMat (show 2 * 1 + 2 * m = 2 * (1 + m) by omega)
          (blockMat A00 A01 (fun i j => -A01 j i) A11) := by
      funext i j; unfold castMat blockMat; dsimp only [A00, A01, A11]; unfold skewOnesMat sgnInt
      by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
      · simp [hi, hj]
      · have hlt : i.val < j.val := by omega
        simp [hi, hj, hlt]
      · have hgt : j.val < i.val := by omega
        have hnl : ¬ (i.val < j.val) := by omega
        simp [hi, hj, hgt, hnl]
      · have hiff1 : i.val < j.val ↔ i.val - 2 < j.val - 2 := by omega
        have hiff2 : j.val < i.val ↔ j.val - 2 < i.val - 2 := by omega
        simp [hi, hj, hiff1, hiff2]
    have hcert : ∀ i j, matMul A00 X i j + 1 * A01 i j = 0 := by
      intro i j; unfold matMul; dsimp only [A00, A01, X]
      simp only [sumFin_succ, sumFin_zero, Int.add_zero, Int.one_mul]
      have hi2 : i.val = 0 ∨ i.val = 1 := by omega
      rcases hi2 with h0 | h1
      · have heq : i = ⟨0, by decide⟩ := Fin.ext h0; subst heq; decide
      · have heq : i = ⟨1, by decide⟩ := Fin.ext h1; subst heq; decide
    have hschur : (fun i j => 1 * 1 * A11 i j - 1 * matMul (matTrans A01) X i j) = A11 := by
      funext i j; unfold matMul matTrans; dsimp only [A01, X]
      simp only [sumFin_succ, sumFin_zero, Int.add_zero, Int.one_mul, Int.mul_one, Fin.succ, ↓reduceIte]
      omega
    have hstep := pfaffian_blockSchur_top A00 A01 A11 (isSkew_skewOnes 2) (isSkew_skewOnes (2 * m)) 1 X hcert
    rw [Int.one_pow, Int.one_mul, ← hblock, hschur] at hstep
    have hpf2 : pfaffian 1 A00 = 1 := by decide
    rw [hpf2, Int.one_mul, pfaffian_skewOnes m] at hstep
    have hcast : pfaffian (m + 1) (skewOnesMat (2 * (m + 1))) = pfaffian (1 + m) (skewOnesMat (2 * (1 + m))) := by
      rw [← pfaffian_castMat (show 1 + m = m + 1 by omega)]
      exact pfaffian_congr (fun i j => rfl)
    rw [hcast, hstep]

theorem pfaffian_carryPencil_step (k : Nat) (hk : 1 ≤ k) (a b : Int) :
    pfaffian (2 ^ k) (castMat (show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow2_succ]) (carryPencilMat (k + 1) a b)) =
    (b - a) ^ (2 ^ (k - 1)) *
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (carryPencilMat k (2 * a) (b - a))) := by
  let m : Nat := 2 ^ (k - 1)
  have h2m : 2 ^ k = 2 * m := by
    dsimp only [m]
    have : k = (k - 1) + 1 := by omega
    conv => lhs; rw [this]; rw [pow2_succ]
  have h2mm : 2 * m + 2 * m = 2 * (m + m) := by omega
  have h2k : 2 ^ k = m + m := by omega
  have hcast_eq : 2 ^ (k + 1) = 2 * (m + m) := by rw [pow2_succ]; omega
  let A : Mat (2 * (m + m)) := castMat hcast_eq (carryPencilMat (k + 1) a b)
  have hA_skew : IsSkew A := by
    constructor
    · intro i; exact (isSkew_carryPencil (k + 1) a b).1 _
    · intro i j; exact (isSkew_carryPencil (k + 1) a b).2 _ _
  -- Step 1: unimodular block-shear Q = blockUpperId (-I_{2m})
  let negI : Fin (2 * m) → Fin (2 * m) → Int := fun i j => if i = j then -1 else 0
  have hQ_pf : pfaffian (m + m) (congruence (castMat h2mm (blockUpperId negI)) A) = pfaffian (m + m) A :=
    pfaffian_blockUpperId h2mm negI hA_skew
  -- Compute B = congruence Q A explicitly as blockMat B00 B01 (-B01^T) B11!
  let Ck : Mat (2 * m) := castMat h2m (carryAsymMat k)
  let Sm : Mat (2 * m) := skewOnesMat (2 * m)
  let B00 : Mat (2 * m) := fun i j => a * Ck i j + (b - a) * Sm i j
  let B01 : Fin (2 * m) → Fin (2 * m) → Int := fun i j => (b - a) * (1 - Sm i j)
  let B11 : Mat (2 * m) := fun i j => 2 * (b - a) * Sm i j
  have hCk_skew : IsSkew Ck := ⟨fun i => (isSkew_carryAsym k).1 _, fun i j => (isSkew_carryAsym k).2 _ _⟩
  have hSm_skew : IsSkew Sm := isSkew_skewOnes (2 * m)
  have hB00_skew : IsSkew B00 := by
    constructor
    · intro i; dsimp only [B00]; rw [hCk_skew.1 i, hSm_skew.1 i]; simp
    · intro i j; dsimp only [B00]; rw [hCk_skew.2 i j, hSm_skew.2 i j]; simp only [Int.mul_neg]; omega
  have hB11_skew : IsSkew B11 := by
    constructor
    · intro i; dsimp only [B11]; rw [hSm_skew.1 i]; simp
    · intro i j; dsimp only [B11]; rw [hSm_skew.2 i j]; simp only [Int.mul_neg]
  have hA_quad : ∀ i j : Fin (2 * (m + m)), A i j =
      if hi : i.val < 2 * m then
        if hj : j.val < 2 * m then a * Ck ⟨i.val, hi⟩ ⟨j.val, hj⟩ + (b - a) * Sm ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else a * Ck ⟨i.val, hi⟩ ⟨j.val - 2 * m, by omega⟩ + (b - a)
      else
        if hj : j.val < 2 * m then a * Ck ⟨i.val - 2 * m, by omega⟩ ⟨j.val, hj⟩ - (b - a)
        else a * Ck ⟨i.val - 2 * m, by omega⟩ ⟨j.val - 2 * m, by omega⟩ + (b - a) * Sm ⟨i.val - 2 * m, by omega⟩ ⟨j.val - 2 * m, by omega⟩ := by
    intro i j
    dsimp only [A, Ck, Sm]; unfold castMat carryPencilMat
    rw [carryAsym_block k]
    unfold castMat blockMat skewOnesMat sgnInt
    have hlt_iff : ∀ u : Nat, u < 2 ^ k ↔ u < 2 * m := fun u => by omega
    by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
    · have hi' : i.val < 2 ^ k := by omega
      have hj' : j.val < 2 ^ k := by omega
      simp only [hi, hj, hi', hj', ↓reduceDIte]
      have h1 : carryAsymMat k ⟨i.val, hi'⟩ ⟨j.val, hj'⟩ = carryAsymMat k ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ := rfl
      rw [h1]
      rw [Int.mul_sub, Int.sub_mul]; omega
    · have hi' : i.val < 2 ^ k := by omega
      have hj' : ¬ (j.val < 2 ^ k) := by omega
      have hlt : i.val < j.val := by omega
      simp only [hi, hj, hi', hj', hlt, ↓reduceDIte, ↓reduceIte]
      have h1 : carryAsymMat k ⟨i.val, hi'⟩ ⟨j.val - 2 ^ k, by omega⟩ = carryAsymMat k ⟨i.val, by omega⟩ ⟨j.val - 2 * m, by omega⟩ := by
        congr 1; apply Fin.ext; dsimp; omega
      rw [h1, Int.mul_sub]; omega
    · have hi' : ¬ (i.val < 2 ^ k) := by omega
      have hj' : j.val < 2 ^ k := by omega
      have hgt : j.val < i.val := by omega
      have hnl : ¬ (i.val < j.val) := by omega
      simp only [hi, hj, hi', hj', hgt, hnl, ↓reduceDIte, ↓reduceIte]
      have h1 : carryAsymMat k ⟨i.val - 2 ^ k, by omega⟩ ⟨j.val, hj'⟩ = carryAsymMat k ⟨i.val - 2 * m, by omega⟩ ⟨j.val, by omega⟩ := by
        congr 1; apply Fin.ext; dsimp; omega
      rw [h1, Int.mul_add]; omega
    · have hi' : ¬ (i.val < 2 ^ k) := by omega
      have hj' : ¬ (j.val < 2 ^ k) := by omega
      simp only [hi, hj, hi', hj', ↓reduceDIte]
      have h1 : carryAsymMat k ⟨i.val - 2 ^ k, by omega⟩ ⟨j.val - 2 ^ k, by omega⟩ =
                carryAsymMat k ⟨i.val - 2 * m, by omega⟩ ⟨j.val - 2 * m, by omega⟩ := by
        congr 1 <;> (apply Fin.ext; dsimp; omega)
      have hiff1 : i.val < j.val ↔ i.val - 2 * m < j.val - 2 * m := by omega
      have hiff2 : j.val < i.val ↔ j.val - 2 * m < i.val - 2 * m := by omega
      have hiff3 : i.val - 2 ^ k < j.val - 2 ^ k ↔ i.val - 2 * m < j.val - 2 * m := by omega
      have hiff4 : j.val - 2 ^ k < i.val - 2 ^ k ↔ j.val - 2 * m < i.val - 2 * m := by omega
      rw [h1]; simp only [hiff1, hiff2, hiff3, hiff4, Int.mul_sub, Int.sub_mul]; omega
  have hQA : congruence (castMat h2mm (blockUpperId negI)) A =
             castMat h2mm (blockMat B00 B01 (fun i j => -B01 j i) B11) := by
    funext i j
    unfold congruence matMul matTrans
    have hQ : ∀ r c : Fin (2 * (m + m)), castMat h2mm (blockUpperId negI) r c =
        (if r = c then 1 else 0) + (if r.val + 2 * m = c.val then -1 else 0) := by
      intro r c; unfold castMat blockUpperId; dsimp only [negI]
      by_cases hr : r.val < 2 * m <;> by_cases hc : c.val < 2 * m
      · have hne : r.val + 2 * m ≠ c.val := by omega
        simp [hr, hc, hne, Fin.ext_iff]
      · have hiff : (⟨r.val, hr⟩ : Fin (2 * m)) = ⟨c.val - 2 * m, by omega⟩ ↔ r.val + 2 * m = c.val := by
          simp only [Fin.ext_iff]; omega
        simp [hr, hc, hiff, Fin.ext_iff]
      · have hne : r.val + 2 * m ≠ c.val := by omega
        simp [hr, hne, Fin.ext_iff]
      · have hne : r.val + 2 * m ≠ c.val := by omega
        simp [hr, hne, Fin.ext_iff]
    have hR : ∀ r : Fin (2 * (m + m)),
        sumFin (fun l => A r l * castMat h2mm (blockUpperId negI) l j) =
        A r j - if hj : j.val < 2 * m then 0 else A r ⟨j.val - 2 * m, by omega⟩ := by
      intro r
      have hsp : ∀ l, A r l * castMat h2mm (blockUpperId negI) l j =
          A r l * (if l = j then 1 else 0) + A r l * (if l.val + 2 * m = j.val then -1 else 0) := by
        intro l; rw [hQ l j, Int.mul_add]
      rw [sumFin_congr hsp, sumFin_add, sumFin_single j _ (fun l hl => by simp [hl])]
      simp only [↓reduceIte, Int.mul_one]
      by_cases hj : j.val < 2 * m
      · simp only [hj, ↓reduceDIte, Int.sub_zero]
        rw [sumFin_eq_zero (fun l => by
          have hne : l.val + 2 * m ≠ j.val := by omega
          simp [hne]), Int.add_zero]
      · simp only [hj, ↓reduceDIte]
        rw [sumFin_single ⟨j.val - 2 * m, by omega⟩ _ (fun l hl => by
          have hne : l.val + 2 * m ≠ j.val := by intro h; apply hl; apply Fin.ext; dsimp; omega
          simp [hne])]
        have heq : (⟨j.val - 2 * m, by omega⟩ : Fin (2 * (m + m))).val + 2 * m = j.val := by dsimp; omega
        simp only [heq, ↓reduceIte]; omega
    simp only [hR]
    have hL : ∀ f : Fin (2 * (m + m)) → Int,
        sumFin (fun r => castMat h2mm (blockUpperId negI) r i * f r) =
        f i - if hi : i.val < 2 * m then 0 else f ⟨i.val - 2 * m, by omega⟩ := by
      intro f
      have hsp : ∀ r, castMat h2mm (blockUpperId negI) r i * f r =
          (if r = i then 1 else 0) * f r + (if r.val + 2 * m = i.val then -1 else 0) * f r := by
        intro r; rw [hQ r i, Int.add_mul]
      rw [sumFin_congr hsp, sumFin_add, sumFin_single i _ (fun r hr => by simp [hr])]
      simp only [↓reduceIte, Int.one_mul]
      by_cases hi : i.val < 2 * m
      · simp only [hi, ↓reduceDIte, Int.sub_zero]
        rw [sumFin_eq_zero (fun r => by
          have hne : r.val + 2 * m ≠ i.val := by omega
          simp [hne]), Int.add_zero]
      · simp only [hi, ↓reduceDIte]
        rw [sumFin_single ⟨i.val - 2 * m, by omega⟩ _ (fun r hr => by
          have hne : r.val + 2 * m ≠ i.val := by intro h; apply hr; apply Fin.ext; dsimp; omega
          simp [hne])]
        have heq : (⟨i.val - 2 * m, by omega⟩ : Fin (2 * (m + m))).val + 2 * m = i.val := by dsimp; omega
        simp only [heq, ↓reduceIte]; omega
    rw [hL]
    unfold castMat blockMat; dsimp only [B00, B01, B11]
    by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
    · simp only [hi, hj, ↓reduceDIte, Int.sub_zero]
      rw [hA_quad i j]; simp [hi, hj]
    · simp only [hi, hj, ↓reduceDIte, Int.sub_zero]
      rw [hA_quad i j, hA_quad i ⟨j.val - 2 * m, by omega⟩]
      have hj' : (⟨j.val - 2 * m, by omega⟩ : Fin (2 * (m + m))).val < 2 * m := by dsimp; omega
      simp only [hi, hj, hj', ↓reduceDIte]
      simp only [Int.mul_sub, Int.sub_mul, Int.mul_one]; omega
    · simp only [hi, hj, ↓reduceDIte, Int.sub_zero]
      rw [hA_quad i j, hA_quad ⟨i.val - 2 * m, by omega⟩ j]
      have hi' : (⟨i.val - 2 * m, by omega⟩ : Fin (2 * (m + m))).val < 2 * m := by dsimp; omega
      simp only [hi, hj, hi', ↓reduceDIte]
      rw [hSm_skew.2 ⟨j.val, hj⟩ ⟨i.val - 2 * m, by omega⟩]
      simp only [Int.mul_sub, Int.sub_mul, Int.mul_one, Int.mul_neg]; omega
    · simp only [hi, hj, ↓reduceDIte]
      rw [hA_quad i j, hA_quad i ⟨j.val - 2 * m, by omega⟩,
          hA_quad ⟨i.val - 2 * m, by omega⟩ j, hA_quad ⟨i.val - 2 * m, by omega⟩ ⟨j.val - 2 * m, by omega⟩]
      have hi' : (⟨i.val - 2 * m, by omega⟩ : Fin (2 * (m + m))).val < 2 * m := by dsimp; omega
      have hj' : (⟨j.val - 2 * m, by omega⟩ : Fin (2 * (m + m))).val < 2 * m := by dsimp; omega
      simp only [hi, hj, hi', hj', ↓reduceDIte]
      have heq1 : (⟨(⟨i.val - 2 * m, by omega⟩ : Fin (2 * (m + m))).val, hi'⟩ : Fin (2 * m)) = ⟨i.val - 2 * m, by omega⟩ := rfl
      have heq2 : (⟨(⟨j.val - 2 * m, by omega⟩ : Fin (2 * (m + m))).val, hj'⟩ : Fin (2 * m)) = ⟨j.val - 2 * m, by omega⟩ := rfl
      rw [heq1, heq2]; simp only [Int.sub_mul, Int.mul_sub, Int.mul_assoc]; omega
  -- Step 2: Apply Mechanism 1B (pfaffian_blockSchur_bot) with d = 2 and Y k i = δ_{k,i} - altSign k!
  let Y : Fin (2 * m) → Fin (2 * m) → Int := fun k i => (if k = i then 1 else 0) - altSign k.val
  have hcert : ∀ i j : Fin (2 * m), 2 * B01 i j + matMul (matTrans Y) B11 i j = 0 := by
    intro i j; unfold matMul matTrans; dsimp only [B01, B11, Y]
    have hsp : ∀ k : Fin (2 * m), ((if k = i then 1 else 0) - altSign k.val) * (2 * (b - a) * Sm k j) =
        (if k = i then 1 else 0) * (2 * (b - a) * Sm k j) + -(2 * (b - a) * (altSign k.val * Sm k j)) := by
      intro k; rw [Int.sub_mul, Int.sub_eq_add_neg]; congr 1; congr 1; ac_rfl
    rw [sumFin_congr hsp, sumFin_add, sumFin_single i _ (fun k hk => by simp [hk])]
    rw [sumFin_neg, sumFin_mul_left, sumFin_altSign_skewOnes m j]
    simp only [↓reduceIte, Int.one_mul, Int.mul_one, Int.mul_sub, Int.sub_mul, Int.mul_assoc]; omega
  have hschur : (fun i j => 2 * 2 * B00 i j - 2 * matMul (matTrans Y) (matTrans B01) i j) =
                scaleMat 2 (castMat h2m (carryPencilMat k (2 * a) (b - a))) := by
    funext i j; unfold scaleMat matMul matTrans castMat carryPencilMat; dsimp only [B00, B01, Y, Ck, Sm]
    have hsp : ∀ k : Fin (2 * m), ((if k = i then 1 else 0) - altSign k.val) * ((b - a) * (1 - Sm j k)) =
        (if k = i then 1 else 0) * ((b - a) * (1 - Sm j k)) +
        (-(b - a) * altSign k.val + -(b - a) * (altSign k.val * Sm k j)) := by
      intro k
      rw [hSm_skew.2 j k, Int.sub_neg, Int.sub_mul, Int.mul_add, Int.mul_one]
      have h1 : altSign k.val * ((b - a) + (b - a) * Sm k j) =
                (b - a) * altSign k.val + (b - a) * (altSign k.val * Sm k j) := by
        rw [Int.mul_add, Int.mul_comm (altSign k.val) (b - a)]
        congr 1; ac_rfl
      rw [h1]; simp only [Int.neg_mul]; omega
    rw [sumFin_congr hsp, sumFin_add, sumFin_single i _ (fun k hk => by simp [hk])]
    rw [sumFin_add, sumFin_mul_left, sumFin_altSign_even m, sumFin_mul_left, sumFin_altSign_skewOnes m j]
    simp only [↓reduceIte, Int.one_mul, Int.mul_zero, Int.mul_one, Int.zero_add]
    rw [hSm_skew.2 j i, Int.sub_neg]
    have hs_eq : skewOnesMat (2 ^ k) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ = Sm i j := rfl
    rw [hs_eq]; unfold castMat; dsimp only [Sm]
    simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.neg_sub, Int.mul_assoc]; omega
  have hbot := pfaffian_blockSchur_bot B00 B01 B11 hB00_skew hB11_skew 2 Y hcert
  rw [← hQA, hQ_pf, hschur, pfaffian_scaleMat] at hbot
  have hB11_eq : B11 = scaleMat (2 * (b - a)) Sm := rfl
  rw [hB11_eq, pfaffian_scaleMat, pfaffian_skewOnes m, Int.mul_one] at hbot
  -- Cancel 2^(2m) = 2^m * 2^m ≠ 0!
  have h2pow : (2 : Int) ^ (2 * m) = (2 : Int) ^ m * (2 : Int) ^ m := by
    have : 2 * m = m + m := by omega
    rw [this, Int.pow_add]
  have hmul_pow : (2 * (b - a)) ^ m = (2 : Int) ^ m * (b - a) ^ m := by
    induction m with
    | zero => simp
    | succ t ih => simp only [Int.pow_succ]; rw [ih]; ac_rfl
  rw [h2pow, hmul_pow] at hbot
  have hne0 : (2 : Int) ^ m * (2 : Int) ^ m ≠ 0 :=
    Int.mul_ne_zero (int_pow_ne_zero (by decide) m) (int_pow_ne_zero (by decide) m)
  have hfinal : pfaffian (m + m) A = (b - a) ^ m * pfaffian m (castMat h2m (carryPencilMat k (2 * a) (b - a))) := by
    apply Int.eq_of_mul_eq_mul_left hne0
    rw [hbot]; ac_rfl
  have hA_cast : pfaffian (2 ^ k) (castMat (show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow2_succ]) (carryPencilMat (k + 1) a b)) =
                 pfaffian (m + m) A := by
    rw [← pfaffian_castMat h2k.symm]
    exact pfaffian_congr (fun i j => rfl)
  rw [hA_cast, hfinal]

/-- **Theorem A (Carry-Asymmetry Homogeneous Mersenne-Root Pfaffian Pencil):**
    For every `k ≥ 1` and all integers `a, b : Int`,
    `Pf(a C_k + b S_{2^k}) = (b - (2^k - 1) a) * ∏_{j=1}^{k-1} (b - (2^j - 1) a)^{2^{k-1-j}}`. -/
theorem pfaffian_carryPencil : ∀ (k : Nat) (hk : 1 ≤ k) (a b : Int),
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (carryPencilMat k a b)) =
    carryPencilClosed k a b
  | 0, hk, _, _ => by omega
  | 1, _, a, b => by
    unfold carryPencilClosed
    simp only [prodFin_zero, Int.mul_one]
    change sumFin (fun j : Fin 1 => altSign j.val * carryPencilMat 1 a b ⟨0, by decide⟩ j.succ * 1) = _
    simp only [sumFin_succ, sumFin_zero, Int.add_zero, altSign_zero, Int.one_mul, Int.mul_one]
    unfold carryPencilMat
    have hca : carryAsymMat 1 ⟨0, by decide⟩ (⟨0, by decide⟩ : Fin 1).succ = -1 := by decide
    have hso : skewOnesMat 2 ⟨0, by decide⟩ (⟨0, by decide⟩ : Fin 1).succ = 1 := by decide
    rw [hca, hso]; omega
  | k + 2, _, a, b => by
    have hstep := pfaffian_carryPencil_step (k + 1) (by omega) a b
    have hih := pfaffian_carryPencil (k + 1) (by omega) (2 * a) (b - a)
    have hcast : pfaffian (2 ^ (k + 2 - 1)) (castMat (show 2 ^ (k + 2) = 2 * 2 ^ (k + 2 - 1) by
        rw [show k + 2 - 1 = k + 1 by omega, pow2_succ]) (carryPencilMat (k + 2) a b)) =
        pfaffian (2 ^ (k + 1)) (castMat (show 2 ^ (k + 2) = 2 * 2 ^ (k + 1) by rw [pow2_succ]) (carryPencilMat (k + 2) a b)) :=
      pfaffian_congr (fun _ _ => rfl)
    rw [hcast, hstep, hih]
    unfold carryPencilClosed
    simp only [Nat.add_sub_cancel]
    rw [prodFin_succ]
    have hlead : (b - a) - ((2 : Int) ^ (k + 1) - 1) * (2 * a) = b - ((2 : Int) ^ (k + 2) - 1) * a := by
      have hpow : (2 : Int) ^ (k + 2) = (2 : Int) ^ (k + 1) * 2 := Int.pow_succ (2 : Int) (k + 1)
      have ha2 : (2 : Int) ^ (k + 1) * (2 * a) = (2 : Int) ^ (k + 1) * 2 * a := (Int.mul_assoc _ _ _).symm
      rw [hpow, Int.sub_mul, Int.sub_mul, Int.one_mul, ha2]; omega
    have h0 : (b - ((2 : Int) ^ ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)).val + 1) - 1) * a) ^
              (2 ^ (k - (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)).val)) = (b - a) ^ (2 ^ k) := by
      dsimp only; simp only [Nat.zero_add, Nat.sub_zero]
      have h1 : (2 : Int) ^ 1 - 1 = 1 := by decide
      rw [h1, Int.one_mul]
    have hprod : prodFin (fun j : Fin k => ((b - a) - ((2 : Int) ^ (j.val + 1) - 1) * (2 * a)) ^ (2 ^ (k + 1 - 2 - j.val))) =
                 prodFin (fun j : Fin k => (b - ((2 : Int) ^ (j.succ.val + 1) - 1) * a) ^ (2 ^ (k - j.succ.val))) := by
      apply prodFin_congr; intro j
      have hexp : k + 1 - 2 - j.val = k - j.succ.val := by simp [Fin.succ]; omega
      have hbase : (b - a) - ((2 : Int) ^ (j.val + 1) - 1) * (2 * a) = b - ((2 : Int) ^ (j.succ.val + 1) - 1) * a := by
        have hpow : (2 : Int) ^ (j.succ.val + 1) = (2 : Int) ^ (j.val + 1) * 2 := Int.pow_succ (2 : Int) (j.val + 1)
        have ha2 : (2 : Int) ^ (j.val + 1) * (2 * a) = (2 : Int) ^ (j.val + 1) * 2 * a := (Int.mul_assoc _ _ _).symm
        rw [hpow, Int.sub_mul, Int.sub_mul, Int.one_mul, ha2]; omega
      rw [hexp, hbase]
    rw [hlead, h0, Int.mul_left_comm]
    congr 1; congr 1

/-- **Corollary A1 (Pure Carry-Asymmetry Exact Mersenne Pfaffian):** -/
theorem pfaffian_carryAsym (k : Nat) (hk : 1 ≤ k) :
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (carryAsymMat k)) =
    carryPencilClosed k 1 0 := by
  have heq : carryAsymMat k = carryPencilMat k 1 0 := by
    funext i j; unfold carryPencilMat; simp
  rw [heq]; exact pfaffian_carryPencil k hk 1 0

/-- **Corollary A2 (Exact Dyadic Collapse at `a = 1, b = -1`):**
    `Pf(C_k - S_{2^k}) = (-1)^{2^{k-1}} * 2^{2^k - 1}` for all `k ≥ 1`. -/
theorem pfaffian_carry_dyadic : ∀ (k : Nat) (hk : 1 ≤ k),
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (carryPencilMat k 1 (-1))) =
    ((-1 : Int) ^ (2 ^ (k - 1))) * (2 : Int) ^ (2 ^ k - 1)
  | 0, hk => by omega
  | 1, _ => by
    rw [pfaffian_carryPencil 1 (by omega) 1 (-1)]
    unfold carryPencilClosed; decide
  | k + 2, _ => by
    rw [pfaffian_carryPencil (k + 2) (by omega) 1 (-1)]
    have hih := pfaffian_carry_dyadic (k + 1) (by omega)
    rw [pfaffian_carryPencil (k + 1) (by omega) 1 (-1)] at hih
    have hstep := pfaffian_carryPencil_step (k + 1) (by omega) 1 (-1)
    -- Note carryPencilMat (k+1) 2 (-2) = scaleMat 2 (carryPencilMat (k+1) 1 (-1))!
    have hsc : castMat (show 2 ^ (k + 1) = 2 * 2 ^ (k + 1 - 1) by
        rw [show k + 1 - 1 = k by omega, pow2_succ]) (carryPencilMat (k + 1) 2 (-2)) =
        scaleMat 2 (castMat (show 2 ^ (k + 1) = 2 * 2 ^ (k + 1 - 1) by
        rw [show k + 1 - 1 = k by omega, pow2_succ]) (carryPencilMat (k + 1) 1 (-1))) := by
      funext i j; unfold castMat scaleMat carryPencilMat
      simp only [Int.mul_add, Int.one_mul, Int.mul_neg, Int.neg_mul]
    have hstep2 : carryPencilClosed (k + 2) 1 (-1) =
        (-2 : Int) ^ (2 ^ k) * ((2 : Int) ^ (2 ^ k) * (((-1 : Int) ^ (2 ^ k)) * (2 : Int) ^ (2 ^ (k + 1) - 1))) := by
      have hcast : pfaffian (2 ^ (k + 1)) (castMat (show 2 ^ (k + 2) = 2 * 2 ^ (k + 1) by rw [pow2_succ]) (carryPencilMat (k + 2) 1 (-1))) =
                   carryPencilClosed (k + 2) 1 (-1) := by
        rw [← pfaffian_carryPencil (k + 2) (by omega) 1 (-1)]
        exact pfaffian_congr (fun _ _ => rfl)
      rw [hcast] at hstep
      rw [hstep, show (-1 : Int) - 1 = -2 by decide, show (2 : Int) * 1 = 2 by decide]
      rw [hsc, pfaffian_scaleMat, pfaffian_carryPencil (k + 1) (by omega) 1 (-1), hih]
      simp only [Nat.add_sub_cancel]
    rw [hstep2]
    have hneg2 : ∀ n : Nat, (-2 : Int) ^ n = (-1 : Int) ^ n * (2 : Int) ^ n := by
      intro n; induction n with
      | zero => rfl
      | succ n ih =>
        simp only [Int.pow_succ]; rw [ih]
        change (-1 : Int) ^ n * (2 : Int) ^ n * ((-1 : Int) * 2) = _
        ac_rfl
    rw [hneg2 (2 ^ k)]
    have h1 : (-1 : Int) ^ (2 ^ k) * (-1 : Int) ^ (2 ^ k) = (-1 : Int) ^ (2 ^ (k + 2 - 1)) := by
      rw [← Int.pow_add, show 2 ^ k + 2 ^ k = 2 ^ (k + 2 - 1) by rw [show k + 2 - 1 = k + 1 by omega, pow2_eq_add]]
    have h2 : (2 : Int) ^ (2 ^ k) * (2 : Int) ^ (2 ^ k) * (2 : Int) ^ (2 ^ (k + 1) - 1) = (2 : Int) ^ (2 ^ (k + 2) - 1) := by
      rw [← Int.pow_add, ← Int.pow_add]
      congr 1
      have hp1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := pow2_eq_add k
      have hp2 : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := pow2_eq_add (k + 1)
      have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
      omega
    calc (-1 : Int) ^ (2 ^ k) * (2 : Int) ^ (2 ^ k) * ((2 : Int) ^ (2 ^ k) * ((-1 : Int) ^ (2 ^ k) * (2 : Int) ^ (2 ^ (k + 1) - 1)))
        = ((-1 : Int) ^ (2 ^ k) * (-1 : Int) ^ (2 ^ k)) * ((2 : Int) ^ (2 ^ k) * (2 : Int) ^ (2 ^ k) * (2 : Int) ^ (2 ^ (k + 1) - 1)) := by ac_rfl
      _ = ((-1 : Int) ^ (2 ^ (k + 2 - 1))) * (2 : Int) ^ (2 ^ (k + 2) - 1) := by rw [h1, h2]

/-- **Corollary A3 (Exact Singularity Locus = Mersenne Numbers `{2^j - 1 | 1 ≤ j ≤ k}`):** -/
theorem pfaffian_carryPencil_eq_zero_iff (k : Nat) (hk : 1 ≤ k) (b : Int) :
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (carryPencilMat k 1 b)) = 0 ↔
    ∃ j : Nat, 1 ≤ j ∧ j ≤ k ∧ b = (2 : Int) ^ j - 1 := by
  rw [pfaffian_carryPencil k hk 1 b]
  unfold carryPencilClosed
  simp only [Int.mul_one, Int.mul_eq_zero]
  have hprod_zero : ∀ (m : Nat) (f : Fin m → Int), prodFin f = 0 ↔ ∃ j : Fin m, f j = 0 := by
    intro m; induction m with
    | zero => intro f; simp [prodFin]
    | succ m ih =>
      intro f; rw [prodFin_succ, Int.mul_eq_zero, ih]
      constructor
      · intro h; rcases h with h0 | ⟨j, hj⟩
        · exact ⟨⟨0, Nat.zero_lt_succ m⟩, h0⟩
        · exact ⟨j.succ, hj⟩
      · intro ⟨j, hj⟩
        cases j using Fin.cases with
        | zero => exact Or.inl hj
        | succ j' => exact Or.inr ⟨j', hj⟩
  rw [hprod_zero]
  constructor
  · intro h; rcases h with hlead | ⟨j, hj⟩
    · exact ⟨k, hk, Nat.le_refl k, by omega⟩
    · rw [int_pow_eq_zero_iff (Nat.two_pow_pos _)] at hj
      exact ⟨j.val + 1, by omega, by omega, by omega⟩
  · intro ⟨j, hj1, hjk, hbeq⟩
    by_cases hjeq : j = k
    · subst hjeq; left; omega
    · right
      refine ⟨⟨j - 1, by omega⟩, ?_⟩
      rw [int_pow_eq_zero_iff (Nat.two_pow_pos _)]
      have : j - 1 + 1 = j := by omega
      rw [this]; omega

-- ----------------------------------------------------------------------------
-- 5.3 Theorem B: Parametric Level-Weighted Gray-Walsh Signed Pfaffian Law
-- ----------------------------------------------------------------------------

/-- **Theorem B2 (Parametric Level-Weighted Gray-Walsh Exact Signed Pfaffian Law):**
    For all `k ≥ 1` and every weight sequence `b : Nat → Int` with `b 0 ≠ 0`:
    `Pf(G_1^{(b)}) = b 0`, `Pf(G_2^{(b)}) = -μ_2(b)`, and `Pf(G_k^{(b)}) = +μ_k(b)^{2^{k-2}}` for `k ≥ 3`. -/
theorem pfaffian_grayWalshWeighted (b : Nat → Int) (hb0 : b 0 ≠ 0) : ∀ (k : Nat) (hk : 1 ≤ k),
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (grayWalshWeightedMat k b)) =
    if k = 1 then b 0 else if k = 2 then -grayMu b 2 else (grayMu b k) ^ (2 ^ (k - 2))
  | 0, hk => by omega
  | 1, _ => by
    simp only [↓reduceIte]
    change sumFin (fun j : Fin 1 => altSign j.val * grayWalshWeightedMat 1 b ⟨0, by decide⟩ j.succ * 1) = b 0
    simp only [sumFin_succ, sumFin_zero, Int.add_zero, altSign_zero, Int.one_mul, Int.mul_one]
    unfold grayWalshWeightedMat
    have hne : (⟨0, by decide⟩ : Fin (2 ^ 1)) ≠ ⟨1, by decide⟩ := by decide
    have hm : msb (0 ^^^ 1) = 0 := by decide
    have hs : sgnInt 0 1 = 1 := by decide
    have hp : paritySign (gray 0 &&& gray 1) = 1 := by decide
    change (if (⟨0, by decide⟩ : Fin (2 ^ 1)) = ⟨1, by decide⟩ then 0 else b (msb (0 ^^^ 1)) * sgnInt 0 1 * paritySign (gray 0 &&& gray 1)) = b 0
    simp only [hne, ↓reduceIte, hm, hs, hp, Int.mul_one]
  | k + 2, _ => by
    have hk1 : 1 ≤ k + 1 := by omega
    have hih := pfaffian_grayWalshWeighted b hb0 (k + 1) hk1
    let m : Nat := 2 ^ k
    have h2m : 2 ^ (k + 1) = 2 * m := by dsimp [m]; rw [pow2_succ]
    have h2mm : 2 * m + 2 * m = 2 * (m + m) := by omega
    let μ : Int := grayMu b (k + 1)
    have hμ_pos : 0 < μ := grayMu_pos b hb0 (k + 1) hk1
    have hμ_ne0 : μ ≠ 0 := by omega
    let G : Mat (2 * m) := castMat h2m (grayWalshWeightedMat (k + 1) b)
    let H : Mat (2 * m) := castMat h2m (grayHadMat (k + 1))
    let D : Fin (2 * m) → Int := fun i => grayDiag (k + 1) ⟨i.val, by omega⟩
    let bk : Int := b (k + 1)
    let A01 : Fin (2 * m) → Fin (2 * m) → Int := fun i j => bk * (D i * H i j)
    let A11 : Mat (2 * m) := diagCong D G
    let X : Fin (2 * m) → Fin (2 * m) → Int := matMul G A01
    have hG_skew : IsSkew G := ⟨fun i => (isSkew_grayWalshWeighted (k + 1) b).1 _, fun i j => (isSkew_grayWalshWeighted (k + 1) b).2 _ _⟩
    have hA11_skew : IsSkew A11 := by
      constructor
      · intro i; dsimp only [A11]; unfold diagCong; rw [hG_skew.1 i]; simp
      · intro i j; dsimp only [A11]; unfold diagCong; rw [hG_skew.2 i j]; rw [Int.mul_neg, Int.neg_mul]; ac_rfl
    have hG_sq : ∀ i j : Fin (2 * m), matMul G G i j = if i = j then -μ else 0 := by
      intro i j; unfold matMul; dsimp only [G, castMat]
      have hcs : sumFin (fun t : Fin (2 * m) => grayWalshWeightedMat (k + 1) b ⟨i.val, by omega⟩ ⟨t.val, by omega⟩ * grayWalshWeightedMat (k + 1) b ⟨t.val, by omega⟩ ⟨j.val, by omega⟩) =
                 matMul (grayWalshWeightedMat (k + 1) b) (grayWalshWeightedMat (k + 1) b) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ :=
        sumFin_cast h2m.symm (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 1) b ⟨i.val, by omega⟩ t * grayWalshWeightedMat (k + 1) b t ⟨j.val, by omega⟩)
      rw [hcs, grayWalshWeighted_sq b (k + 1) hk1 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩]
      have hiff : (⟨i.val, by omega⟩ : Fin (2 ^ (k + 1))) = ⟨j.val, by omega⟩ ↔ i = j := by simp only [Fin.ext_iff]
      simp [hiff, μ]
    -- Certificate for Mechanism 1A: G * (G * A01) + μ * A01 = (-μ I) * A01 + μ * A01 = 0!
    have hcert : ∀ i j : Fin (2 * m), matMul G X i j + μ * A01 i j = 0 := by
      intro i j; dsimp only [X]
      have hassoc : matMul G (matMul G A01) i j = matMul (matMul G G) A01 i j := by
        rw [matMul_assoc]
      rw [hassoc]
      change sumFin (fun t => matMul G G i t * A01 t j) + μ * A01 i j = 0
      rw [sumFin_congr (fun t => by rw [hG_sq i t])]
      rw [sumFin_single i _ (fun t ht => by simp [Ne.symm ht])]
      simp only [↓reduceIte, Int.neg_mul]; omega
    -- Compute Schur block: μ^2 (D G D) - μ * A01^T * (G * A01) = μ * μ_{k+2} * (D G D)!
    have hschur : (fun i j => μ * μ * A11 i j - μ * matMul (matTrans A01) X i j) =
                  scaleMat (μ * grayMu b (k + 2)) A11 := by
      funext i j; unfold scaleMat
      have hGA01 : ∀ r c : Fin (2 * m), X r c = -matMul A01 A11 r c := by
        intro r c; dsimp only [X]; unfold matMul; rw [← sumFin_neg]
        have hanti := (grayWalshWeighted_anticomm b (k + 1) hk1).2 ⟨r.val, by omega⟩ ⟨c.val, by omega⟩
        have h1 : sumFin (fun t : Fin (2 * m) => G r t * A01 t c) =
                  bk * sumFin (fun t : Fin (2 ^ (k + 1)) => grayWalshWeightedMat (k + 1) b ⟨r.val, by omega⟩ t * grayDiag (k + 1) t * grayHadMat (k + 1) t ⟨c.val, by omega⟩) := by
          rw [← sumFin_mul_left, ← sumFin_cast h2m.symm]
          apply sumFin_congr; intro t; dsimp only [G, A01, D, H, castMat]; ac_rfl
        have h2 : sumFin (fun t : Fin (2 * m) => A01 r t * A11 t c) =
                  bk * sumFin (fun t : Fin (2 ^ (k + 1)) => grayDiag (k + 1) ⟨r.val, by omega⟩ * grayHadMat (k + 1) ⟨r.val, by omega⟩ t * (grayDiag (k + 1) t * grayWalshWeightedMat (k + 1) b t ⟨c.val, by omega⟩ * grayDiag (k + 1) ⟨c.val, by omega⟩)) := by
          rw [← sumFin_mul_left, ← sumFin_cast h2m.symm]
          apply sumFin_congr; intro t; dsimp only [A01, A11, G, D, H, castMat, diagCong]; ac_rfl
        rw [sumFin_neg, h1, h2]
        have : bk * (sumFin (fun t => grayWalshWeightedMat (k + 1) b ⟨r.val, by omega⟩ t * grayDiag (k + 1) t * grayHadMat (k + 1) t ⟨c.val, by omega⟩) +
                     sumFin (fun t => grayDiag (k + 1) ⟨r.val, by omega⟩ * grayHadMat (k + 1) ⟨r.val, by omega⟩ t * (grayDiag (k + 1) t * grayWalshWeightedMat (k + 1) b t ⟨c.val, by omega⟩ * grayDiag (k + 1) ⟨c.val, by omega⟩))) = 0 := by
          rw [hanti, Int.mul_zero]
        rw [Int.mul_add] at this; omega
      have hA01_sq : ∀ r c : Fin (2 * m), matMul (matTrans A01) A01 r c = if r = c then (2 : Int) ^ (k + 1) * (bk * bk) else 0 := by
        intro r c; unfold matMul matTrans; dsimp only [A01, D, H, castMat]
        have hsum : sumFin (fun t : Fin (2 * m) => bk * (grayDiag (k + 1) ⟨t.val, by omega⟩ * grayHadMat (k + 1) ⟨t.val, by omega⟩ ⟨r.val, by omega⟩) * (bk * (grayDiag (k + 1) ⟨t.val, by omega⟩ * grayHadMat (k + 1) ⟨t.val, by omega⟩ ⟨c.val, by omega⟩))) =
                    bk * bk * matMul (grayHadMat (k + 1)) (grayHadMat (k + 1)) ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ := by
          unfold matMul; rw [← sumFin_mul_left, ← sumFin_cast h2m.symm]
          apply sumFin_congr; intro t
          rw [grayHad_symm (k + 1) ⟨t.val, by omega⟩ ⟨r.val, by omega⟩]
          calc bk * (grayDiag (k + 1) ⟨t.val, by omega⟩ * grayHadMat (k + 1) ⟨r.val, by omega⟩ ⟨t.val, by omega⟩) *
               (bk * (grayDiag (k + 1) ⟨t.val, by omega⟩ * grayHadMat (k + 1) ⟨t.val, by omega⟩ ⟨c.val, by omega⟩))
              = (grayDiag (k + 1) ⟨t.val, by omega⟩ * grayDiag (k + 1) ⟨t.val, by omega⟩) *
                (bk * bk * (grayHadMat (k + 1) ⟨r.val, by omega⟩ ⟨t.val, by omega⟩ * grayHadMat (k + 1) ⟨t.val, by omega⟩ ⟨c.val, by omega⟩)) := by ac_rfl
            _ = bk * bk * (grayHadMat (k + 1) ⟨r.val, by omega⟩ ⟨t.val, by omega⟩ * grayHadMat (k + 1) ⟨t.val, by omega⟩ ⟨c.val, by omega⟩) := by
                rw [grayDiag_sq, Int.one_mul]
        rw [hsum, (grayHad_algebra (k + 1) hk1).1]
        have hiff : (⟨r.val, by omega⟩ : Fin (2 ^ (k + 1))) = ⟨c.val, by omega⟩ ↔ r = c := by simp only [Fin.ext_iff]
        by_cases hrc : r = c
        · simp only [hrc, ↓reduceIte]; rw [Int.mul_comm (bk * bk)]
        · simp [hrc, hiff]
      have hterm : matMul (matTrans A01) X i j = -((2 : Int) ^ (k + 1) * (bk * bk) * A11 i j) := by
        have h1 : matMul (matTrans A01) X i j = -matMul (matTrans A01) (matMul A01 A11) i j := by
          change sumFin (fun t => matTrans A01 i t * X t j) = -sumFin (fun t => matTrans A01 i t * matMul A01 A11 t j)
          rw [← sumFin_neg]; apply sumFin_congr; intro t
          rw [hGA01 t j, Int.mul_neg]
        rw [h1, ← matMul_assoc]
        change -sumFin (fun t => matMul (matTrans A01) A01 i t * A11 t j) = _
        rw [sumFin_congr (fun t => by rw [hA01_sq i t])]
        rw [sumFin_single i _ (fun t ht => by simp [Ne.symm ht])]
        simp
      rw [hterm, Int.mul_neg, Int.sub_neg]
      unfold grayMu
      rw [Int.mul_add, Int.add_mul, Int.mul_assoc]
      congr 1; ac_rfl
    have htop := pfaffian_blockSchur_top G A01 A11 hG_skew hA11_skew μ X hcert
    have hblock_eq : castMat (show 2 ^ (k + 2) = 2 * (m + m) by rw [pow2_succ]; omega) (grayWalshWeightedMat (k + 2) b) =
                     castMat h2mm (blockMat G A01 (fun i j => -A01 j i) A11) := by
      funext i j; rw [grayWalshWeighted_block (k + 1) hk1 b]; unfold castMat blockMat; dsimp only [G, A01, A11, D, H]
      unfold castMat
      have hp : 2 ^ (k + 1) = 2 * m := h2m
      by_cases hi : i.val < 2 * m <;> by_cases hj : j.val < 2 * m
      · have hi' : i.val < 2 ^ (k + 1) := by omega
        have hj' : j.val < 2 ^ (k + 1) := by omega
        simp [hi, hj, hi', hj']
      · have hi' : i.val < 2 ^ (k + 1) := by omega
        have hj' : ¬ (j.val < 2 ^ (k + 1)) := by omega
        simp only [hi, hj, hi', hj', ↓reduceDIte]; congr 2; congr 1; apply Fin.ext; dsimp; omega
      · have hi' : ¬ (i.val < 2 ^ (k + 1)) := by omega
        have hj' : j.val < 2 ^ (k + 1) := by omega
        simp only [hi, hj, hi', hj', ↓reduceDIte]; congr 3; congr 1; apply Fin.ext; dsimp; omega
      · have hi' : ¬ (i.val < 2 ^ (k + 1)) := by omega
        have hj' : ¬ (j.val < 2 ^ (k + 1)) := by omega
        simp only [hi, hj, hi', hj', ↓reduceDIte]; unfold diagCong; congr 1
        · congr 1
          · congr 1; apply Fin.ext; dsimp; omega
          · congr 1 <;> (apply Fin.ext; dsimp; omega)
        · congr 1; apply Fin.ext; dsimp; omega
    rw [← hblock_eq, hschur, pfaffian_scaleMat] at htop
    have hpfA11 : pfaffian m A11 = (-1 : Int) ^ (2 ^ k) * pfaffian m G := by
      dsimp only [A11]; rw [pfaffian_diagCong]
      have hprod : prodFin D = (-1 : Int) ^ (2 ^ k) := by
        dsimp only [D]; rw [prodFin_cast h2m.symm (grayDiag (k + 1)), prodFin_grayDiag (k + 1) hk1]; rfl
      rw [hprod]
    rw [hpfA11] at htop
    have hcast_lhs : pfaffian (2 ^ (k + 2 - 1)) (castMat (show 2 ^ (k + 2) = 2 * 2 ^ (k + 2 - 1) by
        rw [show k + 2 - 1 = k + 1 by omega, pow2_succ]) (grayWalshWeightedMat (k + 2) b)) =
        pfaffian (m + m) (castMat (show 2 ^ (k + 2) = 2 * (m + m) by rw [pow2_succ]; omega) (grayWalshWeightedMat (k + 2) b)) := by
      have hm2 : 2 ^ (k + 2 - 1) = m + m := by dsimp [m]; exact pow2_eq_add k
      rw [← pfaffian_castMat hm2]; exact pfaffian_congr (fun _ _ => rfl)
    rw [hcast_lhs]
    have hG_sq_pf : pfaffian m G * pfaffian m G = μ ^ m := by
      have hG_eq : pfaffian m G = pfaffian (2 ^ (k + 1 - 1)) (castMat (show 2 ^ (k + 1) = 2 * 2 ^ (k + 1 - 1) by
          rw [show k + 1 - 1 = k by omega, pow2_succ]) (grayWalshWeightedMat (k + 1) b)) :=
        pfaffian_congr (fun _ _ => rfl)
      rw [hG_eq, hih]
      cases k with
      | zero =>
        simp only [↓reduceIte]; dsimp only [m, μ]; simp [grayMu, Int.pow_succ, Int.pow_zero]
      | succ k' =>
        cases k' with
        | zero =>
          simp only [show (2 : Nat) ≠ 1 by decide, ↓reduceIte, Int.neg_mul, Int.mul_neg, Int.neg_neg]
          dsimp only [m, μ]; rw [show 2 ^ 1 = 2 by decide, Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
        | succ k'' =>
          have hne1 : k'' + 3 ≠ 1 := by omega
          have hne2 : k'' + 3 ≠ 2 := by omega
          simp only [hne1, hne2, ↓reduceIte]
          rw [← Int.pow_add]
          dsimp only [m, μ]
          congr 1; rw [show k'' + 3 - 2 = k'' + 1 by omega, pow2_eq_add (k'' + 1)]
    have hpow_split : (μ * grayMu b (k + 2)) ^ m = μ ^ m * (grayMu b (k + 2)) ^ m := by
      induction m with
      | zero => simp
      | succ t ih => simp only [Int.pow_succ]; rw [ih]; ac_rfl
    have h2m_pow : μ ^ (2 * m) = μ ^ m * μ ^ m := by
      rw [show 2 * m = m + m by omega, Int.pow_add]
    rw [hpow_split, h2m_pow] at htop
    have hne0 : μ ^ m * μ ^ m ≠ 0 := Int.mul_ne_zero (int_pow_ne_zero hμ_ne0 m) (int_pow_ne_zero hμ_ne0 m)
    apply Int.eq_of_mul_eq_mul_left hne0
    rw [htop]
    have hstep_alg : pfaffian m G * (μ ^ m * grayMu b (k + 2) ^ m * ((-1 : Int) ^ (2 ^ k) * pfaffian m G)) =
                     μ ^ m * μ ^ m * ((-1 : Int) ^ (2 ^ k) * grayMu b (k + 2) ^ m) := by
      calc pfaffian m G * (μ ^ m * grayMu b (k + 2) ^ m * ((-1 : Int) ^ (2 ^ k) * pfaffian m G))
          = (pfaffian m G * pfaffian m G) * μ ^ m * ((-1 : Int) ^ (2 ^ k) * grayMu b (k + 2) ^ m) := by ac_rfl
        _ = μ ^ m * μ ^ m * ((-1 : Int) ^ (2 ^ k) * grayMu b (k + 2) ^ m) := by rw [hG_sq_pf]
    rw [hstep_alg]
    cases k with
    | zero =>
      simp only [show (2 : Nat) ≠ 1 by decide, ↓reduceIte]
      dsimp only [m]; simp only [Nat.pow_zero, Int.pow_succ, Int.pow_zero, Int.one_mul, Int.neg_mul]
    | succ k' =>
      have hne1 : k' + 3 ≠ 1 := by omega
      have hne2 : k' + 3 ≠ 2 := by omega
      simp only [hne1, hne2, ↓reduceIte]
      rw [neg_one_pow_two_pow (k' + 1) (by omega), Int.one_mul]
      dsimp only [m]
      rw [show k' + 3 - 2 = k' + 1 by omega]

/-- **Corollary B3 (Unweighted Gray-Walsh Signed Mersenne-Power Pfaffian Law):** -/
theorem pfaffian_grayWalsh_pow2 (k : Nat) (hk : 1 ≤ k) :
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (grayWalshMat (2 ^ k))) =
    if k = 1 then 1 else if k = 2 then -3 else ((2 : Int) ^ k - 1) ^ (2 ^ (k - 2)) := by
  rw [grayWalshMat_eq_weighted k, pfaffian_grayWalshWeighted (fun _ => 1) (by decide) k hk]
  by_cases h1 : k = 1
  · subst h1; decide
  · by_cases h2 : k = 2
    · subst h2; decide
    · simp only [h1, h2, ↓reduceIte, grayMu_ones k hk]

-- ----------------------------------------------------------------------------
-- 5.4 Theorem C: All-Even Gray-Walsh Signed Binary-Reflection Law
-- ----------------------------------------------------------------------------

theorem pfaffian_grayWalsh_even_reflection_of_ne_zero (k r : Nat) (hk : 1 ≤ k) (hr : r ≤ 2 ^ (k - 1))
    (hne : pfaffian (2 ^ (k - 1) - r) (grayWalshMat (2 * (2 ^ (k - 1) - r))) ≠ 0) :
    pfaffian (2 ^ (k - 1) + r) (grayWalshMat (2 * (2 ^ (k - 1) + r))) =
    altSign r * ((2 : Int) ^ (k + 1) - 1) ^ r *
    pfaffian (2 ^ (k - 1) - r) (grayWalshMat (2 * (2 ^ (k - 1) - r))) := by
  let m : Nat := 2 ^ (k - 1) + r
  let n : Nat := 2 ^ (k - 1) - r
  have hmn : m + n = 2 ^ k := by
    dsimp [m, n]
    have : k = (k - 1) + 1 := by omega
    have h2 : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by conv => lhs; rw [this]; rw [pow2_eq_add]
    omega
  have h2mn : 2 * (m + n) = 2 ^ (k + 1) := by rw [hmn, pow2_succ]
  let A : Mat (2 * (m + n)) := castMat h2mn.symm (grayWalshMat (2 ^ (k + 1)))
  have hA_skew : IsSkew A := ⟨fun i => (isSkew_grayWalsh _).1 _, fun i j => (isSkew_grayWalsh _).2 _ _⟩
  let μ : Int := (2 : Int) ^ (k + 1) - 1
  have hconf : ∀ i j : Fin (2 * (m + n)), matMul A A i j = if i = j then -μ else 0 := by
    intro i j; unfold matMul; dsimp only [A, castMat]
    have hcs : sumFin (fun t : Fin (2 * (m + n)) => grayWalshMat (2 ^ (k + 1)) ⟨i.val, by omega⟩ ⟨t.val, by omega⟩ * grayWalshMat (2 ^ (k + 1)) ⟨t.val, by omega⟩ ⟨j.val, by omega⟩) =
               matMul (grayWalshMat (2 ^ (k + 1))) (grayWalshMat (2 ^ (k + 1))) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ :=
      sumFin_cast h2mn (fun t : Fin (2 ^ (k + 1)) => grayWalshMat (2 ^ (k + 1)) ⟨i.val, by omega⟩ t * grayWalshMat (2 ^ (k + 1)) t ⟨j.val, by omega⟩)
    rw [hcs]
    have hsq := grayWalshWeighted_sq (fun _ => 1) (k + 1) (by omega) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    rw [← grayWalshMat_eq_weighted (k + 1), grayMu_ones (k + 1) (by omega)] at hsq
    rw [hsq]
    have hiff : (⟨i.val, by omega⟩ : Fin (2 ^ (k + 1))) = ⟨j.val, by omega⟩ ↔ i = j := by simp only [Fin.ext_iff]
    simp [hiff, μ]
  -- Apply Mechanism 3: pfaffian_skewConference_compl!
  have hcompl := pfaffian_skewConference_compl A μ hA_skew hconf
  dsimp only at hcompl
  -- Identify leading block B = grayWalshMat (2 * m) and trailing block D = reversed grayWalshMat (2 * n)!
  have hB : (fun i j : Fin (2 * m) => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) = grayWalshMat (2 * m) := by
    funext i j; rfl
  have hD : (fun i j : Fin (2 * n) => A ⟨2 * m + i.val, by omega⟩ ⟨2 * m + j.val, by omega⟩) =
            (fun i j : Fin (2 * n) => grayWalshMat (2 * n) (revIdx i) (revIdx j)) := by
    funext i j; dsimp only [A]; unfold castMat grayWalshMat revIdx
    have hi_eq : 2 * m + i.val = 2 ^ (k + 1) - 1 - (2 * n - 1 - i.val) := by omega
    have hj_eq : 2 * m + j.val = 2 ^ (k + 1) - 1 - (2 * n - 1 - j.val) := by omega
    have hri : 2 * n - 1 - i.val < 2 ^ k := by omega
    have hrj : 2 * n - 1 - j.val < 2 ^ k := by omega
    have h := grayWalsh_compl_entry k (2 * n - 1 - i.val) (2 * n - 1 - j.val) hri hrj
    rw [← hi_eq, ← hj_eq] at h
    exact h
  rw [hB, hD, pfaffian_rev (isSkew_grayWalsh (2 * n))] at hcompl
  -- Evaluate pfaffian (m + n) A via Corollary B3!
  have hpfA : pfaffian (m + n) A = if k = 1 then -3 else μ ^ (2 ^ (k - 1)) := by
    have h1 := pfaffian_grayWalsh_pow2 (k + 1) (by omega)
    have hcast : pfaffian (m + n) A = pfaffian (2 ^ (k + 1 - 1)) (castMat (show 2 ^ (k + 1) = 2 * 2 ^ (k + 1 - 1) by
        rw [Nat.add_sub_cancel, pow2_succ]) (grayWalshMat (2 ^ (k + 1)))) := by
      have hmne : m + n = 2 ^ (k + 1 - 1) := by rw [Nat.add_sub_cancel]; exact hmn
      rw [← pfaffian_castMat hmne]; exact pfaffian_congr (fun _ _ => rfl)
    rw [hcast, h1]
    by_cases hk1 : k = 1
    · subst hk1; decide
    · have hne1 : k + 1 ≠ 1 := by omega
      have hne2 : k + 1 ≠ 2 := by omega
      simp only [hk1, hne1, hne2, ↓reduceIte, μ]
      congr 1
  rw [hpfA] at hcompl
  have hμ_ne0 : μ ≠ 0 := by
    dsimp only [μ]
    have hp : (2 : Int) ≤ (2 : Int) ^ (k + 1) := by
      have : ∀ t : Nat, (2 : Int) ≤ (2 : Int) ^ (t + 1) := by
        intro t; induction t with
        | zero => decide
        | succ s is => rw [Int.pow_succ]; omega
      exact this k
    omega
  have hD_ne0 : altSign n * pfaffian n (grayWalshMat (2 * n)) ≠ 0 := by
    apply Int.mul_ne_zero _ hne
    unfold altSign; split <;> decide
  have hfac_ne0 : μ ^ n * (altSign n * pfaffian n (grayWalshMat (2 * n))) ≠ 0 :=
    Int.mul_ne_zero (int_pow_ne_zero hμ_ne0 n) hD_ne0
  apply Int.eq_of_mul_eq_mul_left hfac_ne0
  rw [← hcompl]
  -- Case split k = 1 (r = 0 or r = 1) vs k ≥ 2!
  by_cases hk1 : k = 1
  · subst hk1
    simp only [↓reduceIte]
    have hr2 : r = 0 ∨ r = 1 := by simp at hr; omega
    rcases hr2 with rfl | rfl
    · dsimp only [m, n, μ]; decide
    · dsimp only [m, n, μ]; decide
  · simp only [hk1, ↓reduceIte]
    have h2pow : 2 ^ (k - 1) = n + r := by dsimp [n]; omega
    have hμ_split : μ ^ (2 ^ (k - 1)) = μ ^ n * μ ^ r := by rw [h2pow, Int.pow_add]
    have halt : altSign n = altSign r := by
      have h2even : ∃ t, 2 ^ (k - 1) = 2 * t := by
        refine ⟨2 ^ (k - 2), ?_⟩
        have : k - 1 = (k - 2) + 1 := by omega
        conv => lhs; rw [this]; rw [pow2_succ]
      rcases h2even with ⟨t, ht⟩
      unfold altSign; dsimp only [n]
      have hmod : (2 ^ (k - 1) - r) % 2 = r % 2 := by omega
      rw [hmod]
    rw [hμ_split, halt]
    dsimp only [μ]; ac_rfl

/-- **Theorem C1 (All-Even Nonvanishing of Gray-Walsh Pfaffians):** -/
theorem pfaffian_grayWalsh_even_ne_zero : ∀ m : Nat, pfaffian m (grayWalshMat (2 * m)) ≠ 0 := by
  intro m
  suffices ∀ B : Nat, ∀ t : Nat, t ≤ B → pfaffian t (grayWalshMat (2 * t)) ≠ 0 from this m m (Nat.le_refl m)
  intro B
  induction B with
  | zero =>
    intro t ht; have : t = 0 := by omega
    subst this; decide
  | succ B ih =>
    intro t ht
    by_cases hle : t ≤ B
    · exact ih t hle
    · have ht_eq : t = B + 1 := by omega
      by_cases ht1 : t = 1
      · subst ht1; decide
      · -- Since t ≥ 2, choose k = msb (t - 1) + 1 ≥ 1 so 2^(k-1) < t ≤ 2^k!
        let k : Nat := msb (t - 1) + 1
        have hmsb_bounds : ∀ x : Nat, 1 ≤ x → 2 ^ msb x ≤ x ∧ x < 2 ^ (msb x + 1) := by
          intro x hx
          suffices ∀ M : Nat, ∀ y : Nat, y ≤ M → 1 ≤ y → 2 ^ msb y ≤ y ∧ y < 2 ^ (msb y + 1) from this x x (Nat.le_refl x) hx
          intro M; induction M with
          | zero => intro y hy h1; omega
          | succ M ihM =>
            intro y hy h1
            cases y with
            | zero => omega
            | succ y' =>
              rw [msb_succ]
              by_cases hd : (y' + 1) / 2 = 0
              · simp only [hd, ↓reduceIte]; omega
              · simp only [hd, ↓reduceIte]
                have hrec := ihM ((y' + 1) / 2) (by omega) (by omega)
                have hp1 : 2 ^ (1 + msb ((y' + 1) / 2)) = 2 * 2 ^ msb ((y' + 1) / 2) := by
                  rw [Nat.add_comm, pow2_succ]
                have hp2 : 2 ^ (1 + msb ((y' + 1) / 2) + 1) = 2 * 2 ^ (msb ((y' + 1) / 2) + 1) := by
                  rw [show 1 + msb ((y' + 1) / 2) + 1 = (msb ((y' + 1) / 2) + 1) + 1 by omega, pow2_succ]
                omega
        have hb := hmsb_bounds (t - 1) (by omega)
        have hk1 : 1 ≤ k := by omega
        have h2km1 : 2 ^ (k - 1) < t := by dsimp [k]; omega
        have ht_le : t ≤ 2 ^ k := by dsimp [k]; omega
        let r : Nat := t - 2 ^ (k - 1)
        have hr_pos : 1 ≤ r := by omega
        have hr_le : r ≤ 2 ^ (k - 1) := by
          have : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
            have hk' : k = (k - 1) + 1 := by omega
            conv => lhs; rw [hk']; rw [pow2_eq_add]
          omega
        have href_lt : 2 ^ (k - 1) - r ≤ B := by omega
        have hne_ref := ih (2 ^ (k - 1) - r) href_lt
        have hrefl := pfaffian_grayWalsh_even_reflection_of_ne_zero k r hk1 hr_le hne_ref
        have ht_decomp : 2 ^ (k - 1) + r = t := by omega
        rw [ht_decomp] at hrefl
        rw [hrefl]
        apply Int.mul_ne_zero _ hne_ref
        apply Int.mul_ne_zero
        · unfold altSign; split <;> decide
        · apply int_pow_ne_zero
          have hp : (2 : Int) ≤ (2 : Int) ^ (k + 1) := by
            have : ∀ s : Nat, (2 : Int) ≤ (2 : Int) ^ (s + 1) := by
              intro s; induction s with
              | zero => decide
              | succ u iu => rw [Int.pow_succ]; omega
            exact this k
          omega

/-- **Theorem C2 (All-Even Gray-Walsh Signed Binary-Reflection Law):**
    For EVERY `k ≥ 1` and EVERY `0 ≤ r ≤ 2^{k-1}`,
    `Pf(G_{2^k + 2r}) = (-1)^r * (2^{k+1} - 1)^r * Pf(G_{2^k - 2r})`. -/
theorem pfaffian_grayWalsh_even_reflection (k r : Nat) (hk : 1 ≤ k) (hr : r ≤ 2 ^ (k - 1)) :
    pfaffian (2 ^ (k - 1) + r) (grayWalshMat (2 * (2 ^ (k - 1) + r))) =
    altSign r * ((2 : Int) ^ (k + 1) - 1) ^ r *
    pfaffian (2 ^ (k - 1) - r) (grayWalshMat (2 * (2 ^ (k - 1) - r))) :=
  pfaffian_grayWalsh_even_reflection_of_ne_zero k r hk hr (pfaffian_grayWalsh_even_ne_zero _)

-- ----------------------------------------------------------------------------
-- 5.5 Theorem D: Skew-Walsh Unimodularity & Phase-Transition Contrast
-- ----------------------------------------------------------------------------

theorem isSkew_skewWalsh (k : Nat) : IsSkew (skewWalshMat k) := by
  constructor
  · intro i; unfold skewWalshMat sgnInt; simp
  · intro i j; unfold skewWalshMat
    rw [Nat.and_comm i.val j.val]; unfold sgnInt
    by_cases h1 : i.val < j.val
    · have h2 : ¬ (j.val < i.val) := by omega
      simp [h1, h2]
    · by_cases h2 : j.val < i.val
      · simp [h1, h2]
      · simp [h1, h2]

theorem prodFin_paritySign_pow2 : ∀ k : Nat,
    prodFin (fun i : Fin (2 ^ k) => paritySign i.val) = if k = 1 then -1 else 1
  | 0 => by decide
  | 1 => by decide
  | k + 2 => by
    have hih := prodFin_paritySign_pow2 (k + 1)
    rw [← prodFin_cast (show 2 ^ (k + 1) + 2 ^ (k + 1) = 2 ^ (k + 2) by exact (pow2_eq_add (k + 1)).symm), prodFin_split]
    have hR : prodFin (fun j : Fin (2 ^ (k + 1)) => paritySign (2 ^ (k + 1) + j.val)) =
              (-1 : Int) ^ (2 ^ (k + 1)) * prodFin (fun j : Fin (2 ^ (k + 1)) => paritySign j.val) := by
      have h1 : prodFin (fun j : Fin (2 ^ (k + 1)) => paritySign (2 ^ (k + 1) + j.val)) =
                prodFin (fun j : Fin (2 ^ (k + 1)) => (-1 : Int) * paritySign j.val) :=
        prodFin_congr (fun j => by rw [paritySign_add_pow2 (k + 1) j.val j.isLt]; omega)
      have hmul : ∀ (n : Nat) (c : Int) (f : Fin n → Int), prodFin (fun j => c * f j) = c ^ n * prodFin f := by
        intro n c f; induction n with
        | zero => simp [prodFin]
        | succ t it => rw [prodFin_succ, prodFin_succ, Int.pow_succ, it]; ac_rfl
      rw [h1, hmul]
    change prodFin (fun i : Fin (2 ^ (k + 1)) => paritySign i.val) *
           prodFin (fun j : Fin (2 ^ (k + 1)) => paritySign (2 ^ (k + 1) + j.val)) = _
    rw [hR, neg_one_pow_two_pow (k + 1) (by omega), Int.one_mul, hih]
    have hne : k + 2 ≠ 1 := by omega
    simp only [hne, ↓reduceIte]
    split <;> decide

/-- **Theorem D (Skew-Walsh Exact Unimodularity Law):**
    Removing the 1-bit Gray shift from `grayWalshMat` causes an exact phase transition from
    exponential Mersenne powers `(2^k - 1)^{2^{k-2}}` to universal unimodularity `Pf(W_{2^k}) = +1`! -/
theorem pfaffian_skewWalsh (k : Nat) (hk : 1 ≤ k) :
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (skewWalshMat k)) = 1 := by
  cases k with
  | zero => omega
  | succ k' =>
    have h2 : 2 ^ (k' + 1) = 2 * 2 ^ k' := pow2_succ k'
    have hadd : 2 ^ k' + 2 ^ k' = 2 * 2 ^ k' := by omega
    let A : Mat (2 * 2 ^ k') := castMat h2 (skewWalshMat (k' + 1))
    have hA_skew : IsSkew A := ⟨fun i => (isSkew_skewWalsh _).1 _, fun i j => (isSkew_skewWalsh _).2 _ _⟩
    -- Apply unimodular block-shear U = blockUpperId (I_{2^{k'}}) to A!
    let U : Mat (2 * 2 ^ k') := castMat hadd (blockUpperId (matId (2 ^ k')))
    have hpf_eq : pfaffian (2 ^ k') (congruence U A) = pfaffian (2 ^ k') A :=
      pfaffian_blockUpperId hadd (matId (2 ^ k')) hA_skew
    -- Compute M = congruence U A explicitly!
    have hU : ∀ r c : Fin (2 * 2 ^ k'), U r c = (if r = c then 1 else 0) + (if r.val + 2 ^ k' = c.val then 1 else 0) := by
      intro r c; dsimp only [U]; unfold castMat blockUpperId matId
      by_cases hr : r.val < 2 ^ k' <;> by_cases hc : c.val < 2 ^ k'
      · have hne : r.val + 2 ^ k' ≠ c.val := by omega
        simp [hr, hc, hne, Fin.ext_iff]
      · have hiff : (⟨r.val, hr⟩ : Fin (2 ^ k')) = ⟨c.val - 2 ^ k', by omega⟩ ↔ r.val + 2 ^ k' = c.val := by
          simp only [Fin.ext_iff]; omega
        simp [hr, hc, hiff, Fin.ext_iff]
      · have hne : r.val + 2 ^ k' ≠ c.val := by omega
        simp [hr, hne, Fin.ext_iff]
      · have hne : r.val + 2 ^ k' ≠ c.val := by omega
        simp [hr, hne, Fin.ext_iff]
    have hM_entry : ∀ i j : Fin (2 * 2 ^ k'), congruence U A i j =
        A i j +
        (if hj : j.val < 2 ^ k' then 0 else A i ⟨j.val - 2 ^ k', by omega⟩) +
        (if hi : i.val < 2 ^ k' then 0 else
          A ⟨i.val - 2 ^ k', by omega⟩ j +
          if hj : j.val < 2 ^ k' then 0 else A ⟨i.val - 2 ^ k', by omega⟩ ⟨j.val - 2 ^ k', by omega⟩) := by
      intro i j; unfold congruence matMul matTrans
      have hR : ∀ r : Fin (2 * 2 ^ k'), sumFin (fun l => A r l * U l j) =
          A r j + if hj : j.val < 2 ^ k' then 0 else A r ⟨j.val - 2 ^ k', by omega⟩ := by
        intro r
        have hsp : ∀ l, A r l * U l j = A r l * (if l = j then 1 else 0) + A r l * (if l.val + 2 ^ k' = j.val then 1 else 0) := by
          intro l; rw [hU l j, Int.mul_add]
        rw [sumFin_congr hsp, sumFin_add, sumFin_single j _ (fun l hl => by simp [hl])]
        simp only [↓reduceIte, Int.mul_one]; congr 1
        by_cases hj : j.val < 2 ^ k'
        · simp only [hj, ↓reduceDIte]
          exact sumFin_eq_zero (fun l => by
            have hne : l.val + 2 ^ k' ≠ j.val := by omega
            simp [hne])
        · simp only [hj, ↓reduceDIte]
          rw [sumFin_single ⟨j.val - 2 ^ k', by omega⟩ _ (fun l hl => by
            have hne : l.val + 2 ^ k' ≠ j.val := by intro h; apply hl; apply Fin.ext; dsimp; omega
            simp [hne])]
          have heq : (⟨j.val - 2 ^ k', by omega⟩ : Fin (2 * 2 ^ k')).val + 2 ^ k' = j.val := by dsimp; omega
          simp [heq]
      simp only [hR]
      have hL : ∀ f : Fin (2 * 2 ^ k') → Int, sumFin (fun r => U r i * f r) =
          f i + if hi : i.val < 2 ^ k' then 0 else f ⟨i.val - 2 ^ k', by omega⟩ := by
        intro f
        have hsp : ∀ r, U r i * f r = (if r = i then 1 else 0) * f r + (if r.val + 2 ^ k' = i.val then 1 else 0) * f r := by
          intro r; rw [hU r i, Int.add_mul]
        rw [sumFin_congr hsp, sumFin_add, sumFin_single i _ (fun r hr => by simp [hr])]
        simp only [↓reduceIte, Int.one_mul]; congr 1
        by_cases hi : i.val < 2 ^ k'
        · simp only [hi, ↓reduceDIte]
          exact sumFin_eq_zero (fun r => by
            have hne : r.val + 2 ^ k' ≠ i.val := by omega
            simp [hne])
        · simp only [hi, ↓reduceDIte]
          rw [sumFin_single ⟨i.val - 2 ^ k', by omega⟩ _ (fun r hr => by
            have hne : r.val + 2 ^ k' ≠ i.val := by intro h; apply hr; apply Fin.ext; dsimp; omega
            simp [hne])]
          have heq : (⟨i.val - 2 ^ k', by omega⟩ : Fin (2 * 2 ^ k')).val + 2 ^ k' = i.val := by dsimp; omega
          simp [heq]
      rw [hL]
    -- Helper: evaluate A on the 4 quadrants directly!
    have hA_01 : ∀ u v : Fin (2 ^ k'), A ⟨u.val, by omega⟩ ⟨2 ^ k' + v.val, by omega⟩ = paritySign (u.val &&& v.val) := by
      intro u v; dsimp only [A]; unfold castMat skewWalshMat sgnInt
      have hlt : u.val < 2 ^ k' + v.val := by omega
      simp only [hlt, ↓reduceIte, Int.one_mul]
      rw [Nat.and_comm, and_add_pow2_left k' v.val u.val v.isLt u.isLt, Nat.and_comm]
    have hA_10 : ∀ u v : Fin (2 ^ k'), A ⟨2 ^ k' + u.val, by omega⟩ ⟨v.val, by omega⟩ = -paritySign (u.val &&& v.val) := by
      intro u v; rw [hA_skew.2, hA_01 v u, Nat.and_comm]
    have hA_11 : ∀ u v : Fin (2 ^ k'), A ⟨2 ^ k' + u.val, by omega⟩ ⟨2 ^ k' + v.val, by omega⟩ = -A ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ := by
      intro u v; dsimp only [A]; unfold castMat skewWalshMat sgnInt
      have h1 : 2 ^ k' + u.val < 2 ^ k' + v.val ↔ u.val < v.val := by omega
      have h2 : 2 ^ k' + v.val < 2 ^ k' + u.val ↔ v.val < u.val := by omega
      rw [and_add_pow2_both k' u.val v.val u.isLt v.isLt, paritySign_add_pow2 k' (u.val &&& v.val) (by
        apply lt_pow2_of_testBit; intro i hi; rw [Nat.testBit_and, testBit_lt_pow2 k' u.val u.isLt i hi]; rfl)]
      simp only [h1, h2, Int.mul_neg]
    -- Verify Mechanism 2 hypotheses on congruence U A!
    have hbot : ∀ i j : Fin (2 ^ k'), congruence U A ⟨2 ^ k' + i.val, by omega⟩ ⟨2 ^ k' + j.val, by omega⟩ = 0 := by
      intro i j; rw [hM_entry]
      have hni : ¬ (2 ^ k' + i.val < 2 ^ k') := by omega
      have hnj : ¬ (2 ^ k' + j.val < 2 ^ k') := by omega
      simp only [hni, hnj, ↓reduceDIte]
      have hi' : (⟨2 ^ k' + i.val - 2 ^ k', by omega⟩ : Fin (2 * 2 ^ k')) = ⟨i.val, by omega⟩ := Fin.ext (by dsimp; omega)
      have hj' : (⟨2 ^ k' + j.val - 2 ^ k', by omega⟩ : Fin (2 * 2 ^ k')) = ⟨j.val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hi', hj', hA_11 i j, hA_10 i j, hA_01 i j]; omega
    have htri : ∀ i j : Fin (2 ^ k'), j.val < i.val → congruence U A ⟨i.val, by omega⟩ ⟨2 ^ k' + j.val, by omega⟩ = 0 := by
      intro i j hji; rw [hM_entry]
      have hnj : ¬ (2 ^ k' + j.val < 2 ^ k') := by omega
      simp only [i.isLt, hnj, ↓reduceDIte, Int.add_zero]
      have hj' : (⟨2 ^ k' + j.val - 2 ^ k', by omega⟩ : Fin (2 * 2 ^ k')) = ⟨j.val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hj', hA_01 i j]
      dsimp only [A]; unfold castMat skewWalshMat sgnInt
      have hnl : ¬ (i.val < j.val) := by omega
      simp only [hnl, hji, ↓reduceIte]; omega
    have hdiag : ∀ i : Fin (2 ^ k'), congruence U A ⟨i.val, by omega⟩ ⟨2 ^ k' + i.val, by omega⟩ = paritySign i.val := by
      intro i; rw [hM_entry]
      have hni : ¬ (2 ^ k' + i.val < 2 ^ k') := by omega
      simp only [i.isLt, hni, ↓reduceDIte, Int.add_zero]
      have hi' : (⟨2 ^ k' + i.val - 2 ^ k', by omega⟩ : Fin (2 * 2 ^ k')) = ⟨i.val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hi', hA_01 i i, hA_skew.1, Int.add_zero, Nat.and_self]
    -- Invoke Mechanism 2: pfaffian_zeroCorner_upperTri!
    have hM_pf := pfaffian_zeroCorner_upperTri (2 ^ k') (congruence U A) (isSkew_congruence U A hA_skew) hbot htri
    rw [hpf_eq] at hM_pf
    have hcast : pfaffian (2 ^ (k' + 1 - 1)) (castMat (show 2 ^ (k' + 1) = 2 * 2 ^ (k' + 1 - 1) by
        rw [Nat.add_sub_cancel, pow2_succ]) (skewWalshMat (k' + 1))) = pfaffian (2 ^ k') A :=
      pfaffian_congr (fun _ _ => rfl)
    rw [hcast, hM_pf, prodFin_congr hdiag, prodFin_paritySign_pow2 k']
    cases k' with
    | zero => decide
    | succ k'' =>
      cases k'' with
      | zero => decide
      | succ k''' =>
        have hne : k''' + 2 ≠ 1 := by omega
        simp only [hne, ↓reduceIte, Int.mul_one]
        have heven : 2 ^ (k''' + 2) * (2 ^ (k''' + 2) - 1) / 2 = 2 * (2 ^ k''' * (2 ^ (k''' + 2) - 1)) := by
          have hp : 2 ^ (k''' + 2) = 4 * 2 ^ k''' := by
            rw [pow2_succ, pow2_succ]; omega
          rw [hp]
          have h1 : 4 * 2 ^ k''' * (4 * 2 ^ k''' - 1) = 2 * (2 * (2 ^ k''' * (4 * 2 ^ k''' - 1))) := by
            rw [← Nat.mul_assoc, ← Nat.mul_assoc]
          rw [h1, Nat.mul_div_cancel_left _ (by decide)]
        rw [heven, altSign_two_mul]

-- ============================================================================
-- Section 6: Kernel-Checked Non-Vacuity Witnesses, Sharpness Counterexamples,
--            and Complete `#print axioms` Audit
-- ============================================================================

-- 6.1 Direct Kernel-Evaluated Pfaffian Witnesses (rfl / decide)

theorem witness_carryAsym_k1 :
    pfaffian 1 (castMat (by decide) (carryAsymMat 1)) = -1 := by decide

theorem witness_carryAsym_k2 :
    pfaffian 2 (castMat (by decide) (carryAsymMat 2)) = 3 := by decide

theorem witness_carryPencil_singular_k2 :
    pfaffian 2 (castMat (by decide) (carryPencilMat 2 1 3)) = 0 := by decide

theorem witness_carryPencil_dyadic_k2 :
    pfaffian 2 (castMat (by decide) (carryPencilMat 2 1 (-1))) = 8 := by decide

theorem witness_grayWalsh_n4 :
    pfaffian 2 (grayWalshMat 4) = -3 := by decide

theorem witness_grayWalsh_n6 :
    pfaffian 3 (grayWalshMat 6) = -7 := by decide

theorem witness_grayWalsh_weighted_k2 :
    pfaffian 2 (castMat (by decide) (grayWalshWeightedMat 2 (fun j => if j = 0 then 2 else 3))) = -22 := by decide

theorem witness_skewWalsh_k2 :
    pfaffian 2 (castMat (by decide) (skewWalshMat 2)) = 1 := by decide

-- 6.2 Constructive Non-Vacuity Witnesses for All Reusable Mechanism Hypotheses

theorem nonvacuity_blockSchur_top :
    ∃ (A00 : Mat (2 * 1)) (A01 : Fin (2 * 1) → Fin (2 * 1) → Int) (A11 : Mat (2 * 1))
      (d : Int) (X : Fin (2 * 1) → Fin (2 * 1) → Int),
      IsSkew A00 ∧ IsSkew A11 ∧ d ≠ 0 ∧
      (∀ i j, matMul A00 X i j + d * A01 i j = 0) :=
  ⟨skewOnesMat 2, fun _ _ => 1, skewOnesMat 2, 1, fun i _ => if i.val = 0 then 1 else -1,
   isSkew_skewOnes 2, isSkew_skewOnes 2, by decide, by
    intro i j; unfold matMul; simp only [sumFin_succ, sumFin_zero, Int.add_zero, Int.one_mul]
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi with h0 | h1
    · have : i = ⟨0, by decide⟩ := Fin.ext h0; subst this; decide
    · have : i = ⟨1, by decide⟩ := Fin.ext h1; subst this; decide⟩

theorem nonvacuity_blockSchur_bot :
    ∃ (A00 : Mat (2 * 1)) (A01 : Fin (2 * 1) → Fin (2 * 1) → Int) (A11 : Mat (2 * 1))
      (d : Int) (Y : Fin (2 * 1) → Fin (2 * 1) → Int),
      IsSkew A00 ∧ IsSkew A11 ∧ d ≠ 0 ∧
      (∀ i j, d * A01 i j + matMul (matTrans Y) A11 i j = 0) :=
  ⟨skewOnesMat 2, fun i j => 1 - skewOnesMat 2 i j, scaleMat 2 (skewOnesMat 2), 2,
   fun k i => (if k = i then 1 else 0) - altSign k.val,
   isSkew_skewOnes 2,
   ⟨fun i => by unfold scaleMat; rw [(isSkew_skewOnes 2).1 i]; simp,
    fun i j => by unfold scaleMat; rw [(isSkew_skewOnes 2).2 i j, Int.mul_neg]⟩,
   by decide, by
    intro i j
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hi with h1 | h1 <;> rcases hj with h2 | h2
    · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars; decide
    · have : i = ⟨0, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars; decide
    · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨0, by decide⟩ := Fin.ext h2; subst_vars; decide
    · have : i = ⟨1, by decide⟩ := Fin.ext h1; have : j = ⟨1, by decide⟩ := Fin.ext h2; subst_vars; decide⟩

theorem nonvacuity_skewConference_compl :
    ∃ (A : Mat (2 * (1 + 1))) (μ : Int),
      IsSkew A ∧ μ ≠ 0 ∧ (∀ i j, matMul A A i j = if i = j then -μ else 0) :=
  ⟨grayWalshMat 4, 3, isSkew_grayWalsh 4, by decide, by
    intro i j
    have hsq := grayWalshWeighted_sq (fun _ => 1) 2 (by decide) i j
    rw [← grayWalshMat_eq_weighted 2, grayMu_ones 2 (by decide)] at hsq
    exact hsq⟩

-- 6.3 Kernel-Checked Sharpness Counterexamples (Falsified Variants)

/-- Counterexample 1: Removing bit-complement from `carryAsymMat` (`sgn(y-x) * carries(x, y)`)
    collapses `Pf` at `k = 2` to `0` (vs `Pf(C_2) = 3`). -/
theorem sharpness_raw_carry_no_complement :
    pfaffian 2 (fun i j : Fin 4 => sgnInt i.val j.val * carries i.val j.val) = 0 ∧
    pfaffian 2 (castMat (by decide) (carryAsymMat 2)) = 3 := by
  decide

/-- Counterexample 2a: Changing Gray shift `r = 1` to `r = 2` (`x ^^^ (x >>> 2)`) collapses
    `Pf` at `k = 2` to `1` (breaking Gray-Walsh `-3`). -/
theorem sharpness_shift2_breaks_grayWalsh :
    pfaffian 2 (fun i j : Fin 4 =>
      sgnInt i.val j.val * paritySign ((i.val ^^^ (i.val >>> 2)) &&& (j.val ^^^ (j.val >>> 2)))) = 1 ∧
    pfaffian 2 (grayWalshMat 4) = -3 := by
  decide

/-- Counterexample 2b: Replacing Gray code `x ^^^ (x >>> 1)` with inverse Gray (prefix-XOR)
    breaks the Mersenne-power law at `k = 3`: `Pf = 33 ≠ 49 = 7^2`. -/
theorem sharpness_invGray_breaks_grayWalsh :
    pfaffian 4 (fun i j : Fin 8 =>
      sgnInt i.val j.val * paritySign (invGray i.val &&& invGray j.val)) = 33 ∧
    pfaffian 4 (grayWalshMat 8) = 49 := by
  decide

/-- Counterexample 3: Shifting Skew-Walsh by `s = 2` breaks unimodularity at `k = 2`
    (`Pf = 3 ≠ 1`), whereas `s = 0` and `s = 1` both give `1`. -/
theorem sharpness_shifted_skewWalsh :
    pfaffian 2 (fun i j : Fin 4 =>
      sgnInt i.val j.val * paritySign ((i.val + 2) &&& (j.val + 2))) = 3 ∧
    pfaffian 2 (fun i j : Fin 4 =>
      sgnInt i.val j.val * paritySign ((i.val + 1) &&& (j.val + 1))) = 1 := by
  decide

end SiliconPfaffian
