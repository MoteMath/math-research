import ShellWalshNestedJoinSpectra.Defs

namespace ShellWalshEngine
/-- Multiplicativity of the exact integer determinant: `det (A * B) = det A * det B`. -/
theorem det_mul {n : Nat} (A B : Mat n) : det (matMul A B) = det A * det B := by
  change sumAllFun n n (fun f => leviCivita f * prodFin n (fun i => sumFin n (fun k => A i k * B k (f i)))) =
         det A * det B
  have h1 : ∀ f : Fin n -> Fin n,
      leviCivita f * prodFin n (fun i => sumFin n (fun k => A i k * B k (f i))) =
      sumAllFun n n (fun g => (prodFin n (fun i => A i (g i))) *
        (leviCivita f * prodFin n (fun i => B (g i) (f i)))) := by
    intro f
    rw [prodFin_sumFin, ← sumAllFun_mul_left]
    apply sumAllFun_congr
    intro g
    rw [prodFin_mul]
    rw [← Int.mul_assoc, Int.mul_comm (leviCivita f) (prodFin n (fun i => A i (g i))), Int.mul_assoc]
  rw [sumAllFun_congr h1]
  have sumAllFun_swap : ∀ (m1 m2 : Nat) (H : (Fin m1 -> Fin n) -> (Fin m2 -> Fin n) -> Int),
      sumAllFun m1 n (fun f => sumAllFun m2 n (fun g => H f g)) =
      sumAllFun m2 n (fun g => sumAllFun m1 n (fun f => H f g)) := by
    intro m1 m2 H
    induction m1 with
    | zero => rfl
    | succ m1 ih1 =>
      simp only [sumAllFun]
      rw [sumFin_congr (fun v => ih1 (fun f g => H (snoc f v) g))]
      have sumFin_sumAllFun : ∀ (m : Nat) (K : Fin n -> (Fin m -> Fin n) -> Int),
          sumFin n (fun v => sumAllFun m n (fun g => K v g)) =
          sumAllFun m n (fun g => sumFin n (fun v => K v g)) := by
        intro m K
        induction m with
        | zero => rfl
        | succ m ihm =>
          simp only [sumAllFun]
          rw [sumFin_swap_order]
          apply sumFin_congr
          intro w
          exact ihm (fun v g => K v (snoc g w))
      exact sumFin_sumAllFun m2 (fun v g => sumAllFun m1 n (fun f => H (snoc f v) g))
  rw [sumAllFun_swap]
  have h2 : ∀ g : Fin n -> Fin n,
      sumAllFun n n (fun f => prodFin n (fun i => A i (g i)) *
        (leviCivita f * prodFin n (fun i => B (g i) (f i)))) =
      (leviCivita g * prodFin n (fun i => A i (g i))) * det B := by
    intro g
    rw [sumAllFun_mul_left, sumAllFun_leviCivita_comp]
    rw [← Int.mul_assoc, Int.mul_comm (prodFin n (fun i => A i (g i))) (leviCivita g)]
  rw [sumAllFun_congr h2, sumAllFun_mul_right]
  rfl

theorem det_id_add_ones (m : Nat) : det (matAdd (matId m) (matOnes m)) = (m : Int) + 1 := by
  cases m with
  | zero => simp [det, sumAllFun, leviCivita, prodFin]
  | succ m' =>
    let A := matAdd (matId (m' + 1)) (matOnes (m' + 1))
    let P := matMul (matMul (elemRowSum (m' + 1)) A) (elemColDiff (m' + 1))
    have hdetP : det P = det A := by
      simp only [P, det_mul, det_elemRowSum, det_elemColDiff, Int.one_mul, Int.mul_one]
    rw [← hdetP]
    have hEA : ∀ i j : Fin (m' + 1),
        matMul (elemRowSum (m' + 1)) A i j =
        if i.val = 0 then (m' : Int) + 2 else A i j := by
      intro i j
      unfold matMul elemRowSum
      by_cases hi0 : i.val = 0
      · simp only [hi0, ↓reduceIte, Int.one_mul, A, matAdd, matId, matOnes]
        rw [sumFin_add, sumFin_const, sumFin_eq_single]
        omega
      · simp only [hi0, ↓reduceIte]
        rw [sumFin_congr (g := fun k => if k = i then A i j else 0)]
        · exact sumFin_eq_single i (A i j)
        · intro k
          by_cases hki : k = i
          · subst hki; simp
          · simp [hki, Ne.symm hki]
    have hP : ∀ i j : Fin (m' + 1),
        P i j =
        if i.val = 0 then (if j.val = 0 then (m' : Int) + 2 else 0)
        else if j.val = 0 then 1
        else if i = j then 1 else 0 := by
      intro i j
      dsimp only [P]
      rw [matMul_elemColDiff, hEA i j, hEA i ⟨0, Nat.zero_lt_succ m'⟩]
      by_cases hi0 : i.val = 0
      · simp only [hi0, ↓reduceIte]
        by_cases hj0 : j.val = 0
        · simp only [hj0, ↓reduceIte]
        · simp only [hj0, ↓reduceIte]; omega
      · simp only [hi0, ↓reduceIte]
        have hi_ne0 : i ≠ ⟨0, Nat.zero_lt_succ m'⟩ := fun h => hi0 (congrArg Fin.val h)
        by_cases hj0 : j.val = 0
        · simp only [hj0, ↓reduceIte, A, matAdd, matId, matOnes, hi_ne0]; omega
        · simp only [hj0, ↓reduceIte, A, matAdd, matId, matOnes, hi_ne0]
          by_cases hij : i = j
          · simp only [hij, ↓reduceIte]; omega
          · simp only [hij, ↓reduceIte]; omega
    rw [det_lowerTriangular]
    · rw [prodFin_succ_zero]
      have h0 : P ⟨0, Nat.zero_lt_succ m'⟩ ⟨0, Nat.zero_lt_succ m'⟩ = (m' : Int) + 2 := by
        rw [hP]; simp
      have hrest : prodFin m' (fun i => P i.succ i.succ) = 1 := by
        rw [prodFin_congr (g := fun _ => 1)]
        · exact prodFin_one m'
        · intro i; rw [hP]; simp
      rw [h0, hrest]; omega
    · intro i j hij
      rw [hP]
      have hj0 : j.val ≠ 0 := by omega
      have hne : i ≠ j := fun h => by have := congrArg Fin.val h; omega
      by_cases hi0 : i.val = 0
      · rw [ite_eq_left hi0, ite_eq_right hj0]
      · rw [ite_eq_right hi0, ite_eq_right hj0, ite_eq_right hne]

/-- **Kirchhoff Rank-1 Cofactor Identity**:
    For ANY `(m+1) x (m+1)` matrix `L` with zero row sums and zero column sums,
    `det (L + J) = (m + 1)^2 * det (L^{(0,0)})`. -/
theorem det_laplacian_add_ones {m : Nat} (L : Mat (m + 1))
    (hrow : ∀ i : Fin (m + 1), sumFin (m + 1) (fun j => L i j) = 0)
    (hcol : ∀ j : Fin (m + 1), sumFin (m + 1) (fun i => L i j) = 0) :
    det (matAdd L (matOnes (m + 1))) =
    ((m + 1 : Nat) : Int) * ((m + 1 : Nat) : Int) * det (minor00 L) := by
  let A := matAdd L (matOnes (m + 1))
  let P := matMul (matMul (elemRowSum (m + 1)) A) (elemColDiff (m + 1))
  have hdetP : det P = det A := by
    simp only [P, det_mul, det_elemRowSum, det_elemColDiff, Int.one_mul, Int.mul_one]
  rw [← hdetP]
  have hEA : ∀ i j : Fin (m + 1),
      matMul (elemRowSum (m + 1)) A i j =
      if i.val = 0 then ((m + 1 : Nat) : Int) else L i j + 1 := by
    intro i j
    unfold matMul elemRowSum
    by_cases hi0 : i.val = 0
    · simp only [hi0, ↓reduceIte, Int.one_mul, A, matAdd, matOnes]
      rw [sumFin_add, hcol j, sumFin_const]
      omega
    · simp only [hi0, ↓reduceIte]
      rw [sumFin_congr (g := fun k => if k = i then A i j else 0)]
      · rw [sumFin_eq_single]; rfl
      · intro k
        by_cases hki : k = i
        · subst hki; simp
        · simp [hki, Ne.symm hki]
  have hP0 : ∀ j : Fin (m + 1),
      P ⟨0, Nat.zero_lt_succ m⟩ j = if j.val = 0 then ((m + 1 : Nat) : Int) else 0 := by
    intro j
    dsimp only [P]
    rw [matMul_elemColDiff, hEA ⟨0, Nat.zero_lt_succ m⟩ j, hEA ⟨0, Nat.zero_lt_succ m⟩ ⟨0, Nat.zero_lt_succ m⟩]
    by_cases hj0 : j.val = 0
    · rw [ite_eq_left hj0, ite_eq_left hj0]; simp
    · rw [ite_eq_right hj0, ite_eq_right hj0]; simp
  have hminor : ∀ i j : Fin m,
      minor00 P i j = matMul (minor00 L) (matAdd (matId m) (matOnes m)) i j := by
    intro i j
    dsimp only [minor00, P]
    rw [matMul_elemColDiff, hEA i.succ j.succ, hEA i.succ ⟨0, Nat.zero_lt_succ m⟩]
    have hi0 : i.succ.val ≠ 0 := by simp
    have hj0 : j.succ.val ≠ 0 := by simp
    rw [ite_eq_right hj0, ite_eq_right hi0, ite_eq_right hi0]
    have hrhs : matMul (minor00 L) (matAdd (matId m) (matOnes m)) i j =
        L i.succ j.succ + sumFin m (fun k => L i.succ k.succ) := by
      unfold matMul minor00 matAdd matId matOnes
      rw [sumFin_congr (g := fun k => (if k = j then L i.succ j.succ else 0) + L i.succ k.succ)]
      · rw [sumFin_add, sumFin_eq_single]
      · intro k
        by_cases hkj : k = j
        · subst hkj; rw [ite_eq_left rfl, ite_eq_left rfl, Int.mul_add, Int.mul_one]
        · rw [ite_eq_right hkj, ite_eq_right hkj, Int.zero_add, Int.mul_one, Int.zero_add]
    rw [hrhs]
    have hrowi := hrow i.succ
    rw [sumFin_succ_zero] at hrowi
    omega
  rw [det_row0_single P (fun j hj => by rw [hP0 j, ite_eq_right hj])]
  rw [hP0 ⟨0, Nat.zero_lt_succ m⟩]
  rw [ite_eq_left rfl]
  rw [det_congr hminor, det_mul, det_id_add_ones]
  have hcast : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by omega
  rw [hcast]
  calc ((m : Int) + 1) * (det (minor00 L) * ((m : Int) + 1))
      = ((m : Int) + 1) * (((m : Int) + 1) * det (minor00 L)) := by rw [Int.mul_comm (det (minor00 L))]
    _ = ((m : Int) + 1) * ((m : Int) + 1) * det (minor00 L) := by rw [Int.mul_assoc]

/-! ### Master Orthogonal-Eigenbasis Spectral & Kirchhoff Lifting Theorems -/

/-- **Master Orthogonal-Eigenbasis Characteristic Polynomial Lifting Theorem**:
    Given ANY `n x n` matrix `L`, ANY orthogonal integer matrix `Q` with `Q^T Q = diag d`
    (`∀ i, d i ≠ 0`), and `L Q = Q diag lam`, the exact characteristic polynomial of `L`
    splits completely over `Int`: `∀ x : Int, det (x I - L) = ∏ i, (x - lam i)`. -/
theorem orthogonal_eigenbasis_charpoly {n : Nat} (L Q : Mat n) (d lam : Fin n -> Int)
    (horth : matMul (matTranspose Q) Q = matDiag d)
    (hd : ∀ i, d i ≠ 0)
    (hdiag : matMul L Q = matMul Q (matDiag lam)) :
    ∀ x : Int, det (matSub (matScale x (matId n)) L) = prodFin n (fun i => x - lam i) := by
  intro x
  have hdetQ_ne : det Q ≠ 0 := by
    have hprod : det (matTranspose Q) * det Q = prodFin n d := by
      rw [← det_mul, horth, det_diag]
    have hne : prodFin n d ≠ 0 := prodFin_ne_zero hd
    intro h0
    rw [h0, Int.mul_zero] at hprod
    exact hne hprod.symm
  have heq : matMul (matSub (matScale x (matId n)) L) Q = matMul Q (matDiag (fun i => x - lam i)) := by
    funext i j
    have h1 := congrFun (congrFun hdiag i) j
    rw [matMul_diag_right] at h1
    rw [matMul_diag_right]
    unfold matMul matSub matScale matId
    rw [sumFin_congr (g := fun k => (if k = i then x * Q i j else 0) - L i k * Q k j)]
    · rw [sumFin_sub, sumFin_eq_single]
      have hLq : sumFin n (fun k => L i k * Q k j) = Q i j * lam j := h1
      rw [hLq, Int.mul_sub, Int.mul_comm x (Q i j)]
    · intro k
      by_cases hki : k = i
      · subst hki; rw [ite_eq_left rfl, ite_eq_left rfl, Int.mul_one, Int.sub_mul]
      · rw [ite_eq_right (Ne.symm hki), ite_eq_right hki, Int.mul_zero, Int.zero_sub, Int.zero_sub, Int.neg_mul]
  have hdet := congrArg det heq
  rw [det_mul, det_mul, det_diag] at hdet
  rw [Int.mul_comm (det Q)] at hdet
  exact Int.eq_of_mul_eq_mul_right hdetQ_ne hdet

/-- **Master Orthogonal-Eigenbasis Kirchhoff Spanning-Tree Lifting Theorem**:
    For ANY `(m+1) x (m+1)` Laplacian `L` (zero row & column sums) diagonalized by an
    orthogonal integer matrix `Q` (`Q^T Q = diag d`, `d i ≠ 0`) whose column 0 is all 1s
    and `lam 0 = 0`, the exact Kirchhoff spanning-tree cofactor satisfies:
      `(m + 1) * det (L^{(0,0)}) = ∏_{j=1}^m lam j`. -/
theorem orthogonal_eigenbasis_kirchhoff {m : Nat} (L Q : Mat (m + 1)) (d lam : Fin (m + 1) -> Int)
    (hrow : ∀ i, sumFin (m + 1) (fun j => L i j) = 0)
    (hcol : ∀ j, sumFin (m + 1) (fun i => L i j) = 0)
    (horth : matMul (matTranspose Q) Q = matDiag d)
    (hd : ∀ i, d i ≠ 0)
    (hcol0 : ∀ i, Q i ⟨0, Nat.zero_lt_succ m⟩ = 1)
    (hlam0 : lam ⟨0, Nat.zero_lt_succ m⟩ = 0)
    (hdiag : matMul L Q = matMul Q (matDiag lam)) :
    ((m + 1 : Nat) : Int) * det (minor00 L) = prodFin m (fun j => lam j.succ) := by
  have hdetQ_ne : det Q ≠ 0 := by
    have hprod : det (matTranspose Q) * det Q = prodFin (m + 1) d := by
      rw [← det_mul, horth, det_diag]
    have hne : prodFin (m + 1) d ≠ 0 := prodFin_ne_zero hd
    intro h0
    rw [h0, Int.mul_zero] at hprod
    exact hne hprod.symm
  let lam' : Fin (m + 1) -> Int := fun j =>
    if j.val = 0 then ((m + 1 : Nat) : Int) else lam j
  have hJQ : matMul (matAdd L (matOnes (m + 1))) Q = matMul Q (matDiag lam') := by
    funext i j
    have h1 := congrFun (congrFun hdiag i) j
    rw [matMul_diag_right] at h1
    rw [matMul_diag_right]
    unfold matMul matAdd matOnes
    rw [sumFin_congr (g := fun k => L i k * Q k j + Q k j)]
    · rw [sumFin_add]
      have hLq : sumFin (m + 1) (fun k => L i k * Q k j) = Q i j * lam j := h1
      rw [hLq]
      by_cases hj0 : j.val = 0
      · have hj : j = ⟨0, Nat.zero_lt_succ m⟩ := Fin.ext hj0
        subst hj
        rw [hlam0, Int.mul_zero, Int.zero_add]
        rw [sumFin_congr (fun k => hcol0 k), sumFin_const, hcol0 i]
        dsimp only [lam']
        rw [ite_eq_left rfl, Int.mul_one, Int.one_mul]
      · have horth0j := congrFun (congrFun horth ⟨0, Nat.zero_lt_succ m⟩) j
        have hne0j : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) ≠ j := fun h => hj0 (congrArg Fin.val h).symm
        simp only [matMul, matTranspose, matDiag, hne0j, ↓reduceIte] at horth0j
        have hsum0 : sumFin (m + 1) (fun k => Q k j) = 0 := by
          rw [← horth0j]
          apply sumFin_congr
          intro k
          rw [hcol0 k, Int.one_mul]
        rw [hsum0, Int.add_zero]
        dsimp only [lam']
        rw [ite_eq_right hj0]
    · intro k; rw [Int.add_mul, Int.one_mul]
  have hdet := congrArg det hJQ
  rw [det_mul, det_mul, det_diag, Int.mul_comm (det Q)] at hdet
  have hdetLJ : det (matAdd L (matOnes (m + 1))) = prodFin (m + 1) lam' :=
    Int.eq_of_mul_eq_mul_right hdetQ_ne hdet
  rw [det_laplacian_add_ones L hrow hcol, prodFin_succ_zero] at hdetLJ
  have hlam'0 : lam' ⟨0, Nat.zero_lt_succ m⟩ = ((m + 1 : Nat) : Int) := by
    dsimp only [lam']; rw [ite_eq_left rfl]
  have hlam'succ : prodFin m (fun j => lam' j.succ) = prodFin m (fun j => lam j.succ) := by
    apply prodFin_congr; intro j
    dsimp only [lam']
    have hne : j.succ.val ≠ 0 := by simp
    rw [ite_eq_right hne]
  rw [hlam'0, hlam'succ] at hdetLJ
  have hm_ne : ((m + 1 : Nat) : Int) ≠ 0 := by omega
  rw [Int.mul_assoc] at hdetLJ
  exact Int.eq_of_mul_eq_mul_left hm_ne hdetLJ

/-! ============================================================================
    PART 2: The Reusable 2-Adic Shell-Walsh Nested-Join Diagonalization Engine
    ============================================================================ -/

/-- **REUSABLE ENGINE COROLLARY 1 (Exact Characteristic Polynomial of ALL 2-Adic Shell-Walsh Graphs)**:
    For ALL `k : Nat`, ALL `c : Nat -> Int`, ALL `phi : Nat -> Nat -> Int`, and ALL `x : Int`:
      `det (x * I - shellLaplacian k c phi) = ∏_{j=0}^{2^k - 1} (x - shellEig k c phi j)`. -/
theorem shellLaplacian_charpoly (k : Nat) (c : Nat -> Int) (phi : Nat -> Nat -> Int) :
    ∀ x : Int,
      det (matSub (matScale x (matId (2 ^ k))) (shellLaplacian k c phi)) =
      prodFin (2 ^ k) (fun j => x - shellEig k c phi j) :=
  orthogonal_eigenbasis_charpoly
    (shellLaplacian k c phi) (shellQ k) (shellNorm k) (shellEig k c phi)
    (shellQ_orth k) (shellNorm_ne_zero k) (shellLaplacian_diag k c phi)

/-- **REUSABLE ENGINE COROLLARY 2 (Exact Kirchhoff Spanning-Tree Cofactor of ALL 2-Adic Shell-Walsh Graphs)**:
    For ALL `k : Nat`, ALL `c : Nat -> Int`, ALL `phi : Nat -> Nat -> Int`
    (with `m = 2^k - 1` so `m + 1 = 2^k`):
      `2^k * det (minor00 (shellLaplacian k c phi)) = ∏_{j=1}^{2^k - 1} shellEig k c phi j`. -/
theorem shellLaplacian_kirchhoff (k : Nat) (c : Nat -> Int) (phi : Nat -> Nat -> Int) :
    ((2 ^ k : Nat) : Int) *
      det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (shellLaplacian k c phi))) =
    prodFin (2 ^ k - 1) (fun j => shellEig k c phi ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) := by
  have hcast : ∀ (n m : Nat) (hn : n = m + 1)
      (L Q : Mat n) (d lam : Fin n -> Int)
      (hrow : ∀ i, sumFin n (fun j => L i j) = 0)
      (hcol : ∀ j, sumFin n (fun i => L i j) = 0)
      (horth : matMul (matTranspose Q) Q = matDiag d)
      (hd : ∀ i, d i ≠ 0)
      (hcol0 : ∀ i, Q i ⟨0, by omega⟩ = 1)
      (hlam0 : lam ⟨0, by omega⟩ = 0)
      (hdiag : matMul L Q = matMul Q (matDiag lam)),
      (n : Int) * det (minor00 (cast (congrArg Mat hn) L)) =
      prodFin m (fun j => lam ⟨j.val + 1, by omega⟩) := by
    intro n m hn L Q d lam hrow hcol horth hd hcol0 hlam0 hdiag
    subst hn
    exact orthogonal_eigenbasis_kirchhoff L Q d lam hrow hcol horth hd hcol0 hlam0 hdiag
  exact hcast (2 ^ k) (2 ^ k - 1) (pow2_eq_pred_succ k)
    (shellLaplacian k c phi) (shellQ k) (shellNorm k) (shellEig k c phi)
    (fun i => graphLaplacian_row_sum _ i)
    (fun j => graphLaplacian_col_sum _ (fun a b => shellWeight_symm c phi a.val b.val) j)
    (shellQ_orth k) (shellNorm_ne_zero k)
    (shellQ_col0 k) (shellEig_zero k c phi) (shellLaplacian_diag k c phi)

/-- **UNIVERSAL 2-VARIABLE CARRY-XOR CHARACTERISTIC POLYNOMIAL THEOREM**:
    For EVERY `k : Nat`, EVERY arbitrary 2-variable weight function `h : Nat -> Nat -> Int`,
    and EVERY `x : Int`, the Laplacian of `w(i, j) = h (v2 (i + j)) (v2 (i ^^^ j))` splits
    completely into linear integer factors via the universal orthogonal basis `shellQ k`. -/
theorem carryXorLaplacian_charpoly (k : Nat) (h : Nat -> Nat -> Int) (x : Int) :
    det (matSub (matScale x (matId (2 ^ k))) (carryXorLaplacian k h)) =
    prodFin (2 ^ k) (fun j => x - shellEig k (carryXorC h) (carryXorPhi h) j) := by
  rw [carryXorLaplacian_eq_shellLaplacian]
  exact shellLaplacian_charpoly k (carryXorC h) (carryXorPhi h) x

/-- **UNIVERSAL 2-VARIABLE CARRY-XOR KIRCHHOFF SPANNING-TREE THEOREM**:
    For EVERY `k : Nat` and EVERY arbitrary 2-variable weight function `h : Nat -> Nat -> Int`:
      `2^k * det (minor00 (carryXorLaplacian k h)) = ∏_{j=1}^{2^k - 1} shellEig k (carryXorC h) (carryXorPhi h) j`. -/
theorem carryXorLaplacian_kirchhoff (k : Nat) (h : Nat -> Nat -> Int) :
    ((2 ^ k : Nat) : Int) *
      det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (carryXorLaplacian k h))) =
    prodFin (2 ^ k - 1)
      (fun j => shellEig k (carryXorC h) (carryXorPhi h)
        ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) := by
  rw [carryXorLaplacian_eq_shellLaplacian]
  exact shellLaplacian_kirchhoff k (carryXorC h) (carryXorPhi h)

/-! ============================================================================
    THEOREM B: 2-Adic Carry-Exact Graph `C_k` (`v2 (x + y) = v2 (x ^^^ y)`)
               Exact Factored Characteristic Polynomial & Spanning-Tree Formula ∀ k >= 1
    ============================================================================ -/

/-- **THEOREM B1 (Exact Factored Characteristic Polynomial of the 2-Adic Carry-Exact Graph `C_k`, ∀ k ≥ 0, ∀ x ∈ ℤ)**:
      `det (x I - L(C_k)) = x * (x - 2^k)^k * ∏_{r=1}^{k-1} (x - (2^k - 2^r))^(2^r - 1)`. -/
theorem carryExact_charpoly (k : Nat) (x : Int) :
    det (matSub (matScale x (matId (2 ^ k))) (carryExactLaplacian k)) =
    x * (x - ((2 ^ k : Nat) : Int)) ^ k *
    prodFin k (fun r =>
      if r.val = 0 then 1
      else (x - (((2 ^ k : Nat) : Int) - ((2 ^ r.val : Nat) : Int))) ^ (2 ^ r.val - 1)) := by
  unfold carryExactLaplacian
  rw [carryXorLaplacian_charpoly]
  -- Pull out `j = 0` (`shellEig 0 = 0`, factor `x`) and factor `-1` out of the remaining `2^k - 1` factors!
  have hcast : ∀ (n m : Nat) (hn : n = m + 1) (g : Fin n -> Int),
      prodFin n g = g ⟨0, by omega⟩ * prodFin m (fun j => g ⟨j.val + 1, by omega⟩) := by
    intro n m hn g; subst hn; rw [prodFin_succ_zero]; rfl
  rw [hcast (2 ^ k) (2 ^ k - 1) (pow2_eq_pred_succ k)]
  rw [shellEig_zero, Int.sub_zero]
  -- Write `x - lam = (-1) * ((-x) + lam)`!
  have hneg :
      prodFin (2 ^ k - 1) (fun j => x - shellEig k (carryXorC carryExactH) (carryXorPhi carryExactH)
        ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) =
      ((-1 : Int) ^ (2 ^ k - 1)) * carryExactShiftedProd k (-x) := by
    rw [← carryExact_shifted_product k (-x), ← int_pow_const_prod, ← prodFin_mul]
    apply prodFin_congr; intro j; omega
  rw [hneg]
  unfold carryExactShiftedProd
  have hsign_dist : ∀ (m : Nat),
      ((-1 : Int) ^ (2 ^ m - 1)) *
      ((-x + ((2 ^ m : Nat) : Int)) ^ m *
        prodFin m (fun r => if r.val = 0 then 1 else (-x + ((2 ^ m : Nat) : Int) - ((2 ^ r.val : Nat) : Int)) ^ (2 ^ r.val - 1))) =
      (x - ((2 ^ m : Nat) : Int)) ^ m *
        prodFin m (fun r => if r.val = 0 then 1 else (x - (((2 ^ m : Nat) : Int) - ((2 ^ r.val : Nat) : Int))) ^ (2 ^ r.val - 1)) := by
    intro m
    have hpow_neg : ∀ (e : Nat) (v : Int), ((-1 : Int) ^ e) * ((-v) ^ e) = v ^ e := by
      intro e v
      induction e with
      | zero => simp
      | succ e ihe =>
        rw [Int.pow_succ, Int.pow_succ, Int.pow_succ]
        calc ((-1 : Int) ^ e * -1) * ((-v) ^ e * -v)
            = (((-1 : Int) ^ e) * ((-v) ^ e)) * (-1 * -v) := by
                rw [Int.mul_assoc, Int.mul_assoc]; congr 1
                rw [← Int.mul_assoc (-1), Int.mul_comm (-1) ((-v) ^ e), Int.mul_assoc]
          _ = v ^ e * v := by rw [ihe]; simp
    have hpow_split : ((-1 : Int) ^ (2 ^ m - 1)) =
        ((-1 : Int) ^ m) * prodFin m (fun r => if r.val = 0 then 1 else (-1 : Int) ^ (2 ^ r.val - 1)) := by
      induction m with
      | zero => simp [prodFin]
      | succ m' ihm =>
        simp only [prodFin]
        have hrec : prodFin m' (fun r : Fin m' => if r.castSucc.val = 0 then (1 : Int) else (-1 : Int) ^ (2 ^ r.castSucc.val - 1)) =
                    prodFin m' (fun r : Fin m' => if r.val = 0 then (1 : Int) else (-1 : Int) ^ (2 ^ r.val - 1)) :=
          prodFin_congr (fun _ => rfl)
        rw [hrec]
        by_cases hm0 : m' = 0
        · subst hm0; simp [prodFin]
        · simp only [hm0, ↓reduceIte]
          have hexp : 2 ^ (m' + 1) - 1 = (2 ^ m' - 1) + 1 + (2 ^ m' - 1) := by
            have hp := Nat.two_pow_pos m'
            have hp2 : 2 ^ (m' + 1) = 2 ^ m' + 2 ^ m' := by rw [Nat.pow_succ]; omega
            omega
          rw [hexp, Int.pow_add, Int.pow_add, ihm, Int.pow_one, Int.pow_succ]
          have h4 : ∀ a b c d : Int, (a * b) * c * d = (a * c) * (b * d) := by
            intro a b c d
            calc (a * b) * c * d = a * (b * c) * d := by rw [Int.mul_assoc a b c]
              _ = a * (c * b) * d := by rw [Int.mul_comm b c]
              _ = (a * c) * (b * d) := by rw [← Int.mul_assoc a c b, Int.mul_assoc (a * c) b d]
          exact h4 _ _ _ _
    rw [hpow_split]
    have halg : ∀ a b c d : Int, (a * b) * (c * d) = (a * c) * (b * d) := by
      intro a b c d
      calc (a * b) * (c * d) = a * (b * c * d) := by rw [Int.mul_assoc, Int.mul_assoc]
        _ = a * (c * b * d) := by rw [Int.mul_comm b c]
        _ = (a * c) * (b * d) := by rw [Int.mul_assoc, Int.mul_assoc]
    rw [halg]
    congr 1
    · have h1 : -x + ((2 ^ m : Nat) : Int) = -(x - ((2 ^ m : Nat) : Int)) := by omega
      rw [h1, hpow_neg]
    · rw [← prodFin_mul]
      apply prodFin_congr
      intro r
      by_cases hr0 : r.val = 0
      · simp [hr0]
      · simp only [hr0, ↓reduceIte]
        have h1 : -x + ((2 ^ m : Nat) : Int) - ((2 ^ r.val : Nat) : Int) =
                  -(x - (((2 ^ m : Nat) : Int) - ((2 ^ r.val : Nat) : Int))) := by omega
        rw [h1, hpow_neg]
  rw [hsign_dist k, Int.mul_assoc]

/-- **THEOREM B2 (Exact Kirchhoff Spanning-Tree Count of the 2-Adic Carry-Exact Graph `C_k`, ∀ k ≥ 1)**:
      `det (L(C_k)^{(0,0)}) = (2^k)^(k - 1) * ∏_{r=1}^{k-1} (2^k - 2^r)^(2^r - 1)`. -/
theorem carryExact_spanning_trees (k : Nat) (hk : 1 ≤ k) :
    det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (carryExactLaplacian k))) =
    carryExactTau k := by
  have hkir := carryXorLaplacian_kirchhoff k carryExactH
  have hsp := carryExact_shifted_product k 0
  have hzero : prodFin (2 ^ k - 1)
      (fun j => shellEig k (carryXorC carryExactH) (carryXorPhi carryExactH)
        ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) =
      carryExactShiftedProd k 0 := by
    rw [← hsp]
    apply prodFin_congr; intro j; simp
  change ((2 ^ k : Nat) : Int) *
      det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (carryExactLaplacian k))) = _ at hkir
  rw [hzero] at hkir
  have hrel : carryExactShiftedProd k 0 = ((2 ^ k : Nat) : Int) * carryExactTau k := by
    unfold carryExactShiftedProd carryExactTau
    have hkm : k = (k - 1) + 1 := by omega
    have hpow : (((2 ^ k : Nat) : Int) ^ k) = ((2 ^ k : Nat) : Int) * (((2 ^ k : Nat) : Int) ^ (k - 1)) := by
      have h1 : ∀ (a : Int) (n : Nat), n = (n - 1) + 1 -> a ^ n = a * a ^ (n - 1) := by
        intro a n hn
        conv => lhs; rw [hn]
        rw [Int.pow_succ, Int.mul_comm]
      exact h1 _ k hkm
    simp only [Int.zero_add]
    rw [hpow, Int.mul_assoc]
  rw [hrel] at hkir
  have hne : ((2 ^ k : Nat) : Int) ≠ 0 := by have := Nat.two_pow_pos k; omega
  exact Int.eq_of_mul_eq_mul_left hne hkir

/-! ============================================================================
    THEOREM A: Dyadic 2-Adic Binary-Sum Graph `G_k^dyad` (`w(x, y) = 2^{v2 (x + y)}`)
               Exact Mirror-Band Spectrum, Spectral Gap of Width `2^k`, and
               Exact Kirchhoff Spanning-Tree Formula ∀ k >= 1
    ============================================================================ -/

/-- **THEOREM A1 (Exact Mirror-Band Characteristic Polynomial of the Dyadic Binary-Sum Graph `w(x,y) = 2^{v2(x+y)}`, ∀ k ≥ 1, ∀ x ∈ ℤ)**:
      `det (x I - L_k^dyad) = x * (x - 2^k) * ∏_{j=1}^{k-1} ((x - (j+2)*2^{k-1}) * (x - (2k+2-j)*2^{k-1}))^{2^{j-1}}`. -/
theorem dyadic_charpoly (k : Nat) (hk : 1 ≤ k) (x : Int) :
    det (matSub (matScale x (matId (2 ^ k))) (dyadicLaplacian k)) =
    x * (x - ((2 ^ k : Nat) : Int)) *
    prodFin k (fun j =>
      if j.val = 0 then 1
      else ((x - ((j.val + 2 : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int)) *
            (x - ((2 * k + 2 - j.val : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int))) ^ (2 ^ (j.val - 1))) := by
  unfold dyadicLaplacian
  rw [carryXorLaplacian_charpoly]
  have hcast : ∀ (n m : Nat) (hn : n = m + 1) (g : Fin n -> Int),
      prodFin n g = g ⟨0, by omega⟩ * prodFin m (fun j => g ⟨j.val + 1, by omega⟩) := by
    intro n m hn g; subst hn; rw [prodFin_succ_zero]; rfl
  rw [hcast (2 ^ k) (2 ^ k - 1) (pow2_eq_pred_succ k)]
  rw [shellEig_zero, Int.sub_zero]
  have hsub : prodFin (2 ^ k - 1)
      (fun j => x - shellEig k (carryXorC dyadicH) (carryXorPhi dyadicH)
        ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) =
      dyadicShiftedProd k x (-1) := by
    rw [← dyadic_shifted_product k hk x (-1)]
    apply prodFin_congr; intro j; simp [Int.neg_one_mul]; omega
  rw [hsub]
  unfold dyadicShiftedProd
  rw [Int.mul_assoc]
  congr 1
  congr 1
  · simp [Int.neg_one_mul]; omega
  · apply prodFin_congr
    intro j
    by_cases hj0 : j.val = 0
    · simp [hj0]
    · simp only [hj0, ↓reduceIte, Int.neg_one_mul]
      congr 1

/-- **THEOREM A2 (Exact Kirchhoff Spanning-Tree Weight Formula for `w(x,y) = 2^{v2(x+y)}`, ∀ k ≥ 1)**:
      `det (minor00 (dyadicLaplacian k)) = ∏_{j=1}^{k-1} ((j + 2) * (2k + 2 - j) * (2^{k-1})^2)^{2^{j-1}}`. -/
theorem dyadic_spanning_trees (k : Nat) (hk : 1 ≤ k) :
    det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (dyadicLaplacian k))) =
    dyadicTau k := by
  have hkir := carryXorLaplacian_kirchhoff k dyadicH
  have hsp := dyadic_shifted_product k hk 0 1
  have h01 : prodFin (2 ^ k - 1)
      (fun j => shellEig k (carryXorC dyadicH) (carryXorPhi dyadicH)
        ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) =
      dyadicShiftedProd k 0 1 := by
    rw [← hsp]
    apply prodFin_congr; intro j; simp
  change ((2 ^ k : Nat) : Int) *
      det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (dyadicLaplacian k))) = _ at hkir
  rw [h01] at hkir
  have hrel : dyadicShiftedProd k 0 1 = ((2 ^ k : Nat) : Int) * dyadicTau k := by
    unfold dyadicShiftedProd dyadicTau
    simp only [Int.zero_add, Int.one_mul]
  rw [hrel] at hkir
  have hne : ((2 ^ k : Nat) : Int) ≠ 0 := by have := Nat.two_pow_pos k; omega
  exact Int.eq_of_mul_eq_mul_left hne hkir

/-- **THEOREM A3 (Exact Spectral Gap of Width `2^k` in `G_k^dyad`, ∀ k ≥ 1)**:
    No eigenvalue of `dyadicLaplacian k` lies in the open band `((k+1)*2^{k-1}, (k+3)*2^{k-1})`,
    and in particular the midpoint `(k + 2) * 2^{k-1}` is NEVER an eigenvalue (`det ≠ 0`)! -/
theorem dyadic_spectral_gap (k : Nat) (hk : 1 ≤ k) (x : Int)
    (hlo : ((k + 1 : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int) < x)
    (hhi : x < ((k + 3 : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int)) :
    det (matSub (matScale x (matId (2 ^ k))) (dyadicLaplacian k)) ≠ 0 := by
  rw [dyadic_charpoly k hk x]
  have hp : 0 < ((2 ^ (k - 1) : Nat) : Int) := by have := Nat.two_pow_pos (k - 1); omega
  have h2k : ((2 ^ k : Nat) : Int) = 2 * ((2 ^ (k - 1) : Nat) : Int) := by
    have h1 : k = (k - 1) + 1 := by omega
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by conv => lhs; rw [h1]; rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have hx_pos : 0 < x := by
    have : 2 * ((2 ^ (k - 1) : Nat) : Int) ≤ ((k + 1 : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int) := by
      have hle : (2 : Int) ≤ ((k + 1 : Nat) : Int) := by omega
      exact Int.mul_le_mul_of_nonneg_right hle (by omega)
    omega
  have hx_ne_2k : x - ((2 ^ k : Nat) : Int) ≠ 0 := by
    rw [h2k]
    have : 2 * ((2 ^ (k - 1) : Nat) : Int) ≤ ((k + 1 : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int) := by
      have hle : (2 : Int) ≤ ((k + 1 : Nat) : Int) := by omega
      exact Int.mul_le_mul_of_nonneg_right hle (by omega)
    omega
  apply Int.mul_ne_zero (Int.mul_ne_zero (by omega) hx_ne_2k)
  apply prodFin_ne_zero
  intro j
  by_cases hj0 : j.val = 0
  · simp [hj0]
  · simp only [hj0, ↓reduceIte]
    have hjlt : j.val < k := j.isLt
    have hlow_ne : x - ((j.val + 2 : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int) ≠ 0 := by
      have hle : ((j.val + 2 : Nat) : Int) ≤ ((k + 1 : Nat) : Int) := by omega
      have hmul := Int.mul_le_mul_of_nonneg_right hle (by omega : 0 ≤ ((2 ^ (k - 1) : Nat) : Int))
      omega
    have hhigh_ne : x - ((2 * k + 2 - j.val : Nat) : Int) * ((2 ^ (k - 1) : Nat) : Int) ≠ 0 := by
      have hle : ((k + 3 : Nat) : Int) ≤ ((2 * k + 2 - j.val : Nat) : Int) := by omega
      have hmul := Int.mul_le_mul_of_nonneg_right hle (by omega : 0 ≤ ((2 ^ (k - 1) : Nat) : Int))
      omega
    have hpow_ne : ∀ (a : Int) (e : Nat), a ≠ 0 -> a ^ e ≠ 0 := by
      intro a e ha
      induction e with
      | zero => simp
      | succ e ihe => rw [Int.pow_succ]; exact Int.mul_ne_zero ihe ha
    exact hpow_ne _ _ (Int.mul_ne_zero hlow_ne hhigh_ne)

/-! ============================================================================
    THEOREM C: Even 2-Adic Binary-Sum Graph `E_k` (`v2 (x + y) % 2 = 0`)
               Non-Cograph (Induced P_4 ∀ k ≥ 4), Irregular (∀ k ≥ 2),
               Yet Universally Laplacian-Integral & Exact Kirchhoff Spectrum ∀ k ≥ 1
    ============================================================================ -/

/-- **THEOREM C1 (Exact Integer Characteristic Polynomial & Kirchhoff Spectrum of `E_k`, ∀ k ≥ 1)**:
    Even though `E_k` is irregular, non-Cayley, and contains induced `P_4` for all `k ≥ 4`,
    its entire Laplacian spectrum is integer and explicitly diagonalized by `shellQ k`. -/
theorem evenSum_charpoly (k : Nat) (x : Int) :
    det (matSub (matScale x (matId (2 ^ k))) (evenSumLaplacian k)) =
    prodFin (2 ^ k) (fun j => x - shellEig k (carryXorC evenSumH) (carryXorPhi evenSumH) j) :=
  carryXorLaplacian_charpoly k evenSumH x

theorem evenSum_kirchhoff (k : Nat) :
    ((2 ^ k : Nat) : Int) *
      det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ k)) (evenSumLaplacian k))) =
    prodFin (2 ^ k - 1)
      (fun j => shellEig k (carryXorC evenSumH) (carryXorPhi evenSumH)
        ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩) :=
  carryXorLaplacian_kirchhoff k evenSumH

theorem sharpness_c3_charpoly (x : Int) :
    det (matSub (matScale x (matId 4)) shifted3Laplacian) =
    x * (x - 2) * (x * x - 4 * x + 2) := by
  rw [shifted3Laplacian_eq]
  let A := matSub (matScale x (matId 4)) shifted3LaplacianExplicit
  have hdetU_ne : det shifted3U ≠ 0 := by
    have hprod : det (matTranspose shifted3U) * det shifted3U = prodFin 4 shifted3D := by
      rw [← det_mul, shifted3U_orth, det_diag]
    have hpd : prodFin 4 shifted3D = 64 := by decide
    rw [hpd] at hprod
    intro h0; rw [h0, Int.mul_zero] at hprod; omega
  have hAU : matMul A shifted3U = matMul shifted3U (shifted3Block x) := by
    rw [shifted3Block_eq_sub]
    funext i j
    have hLU := congrFun (congrFun shifted3LU_eq i) j
    unfold matMul at hLU
    unfold A matMul matSub matScale matId
    have hleft :
        sumFin 4 (fun k => (x * (if i = k then 1 else 0) - shifted3LaplacianExplicit i k) * shifted3U k j) =
        x * shifted3U i j - sumFin 4 (fun k => shifted3LaplacianExplicit i k * shifted3U k j) := by
      rw [sumFin_congr (g := fun k => (if k = i then x * shifted3U i j else 0) - shifted3LaplacianExplicit i k * shifted3U k j)]
      · rw [sumFin_sub, sumFin_eq_single]
      · intro k
        by_cases hki : k = i
        · subst hki; simp [Int.sub_mul]
        · have hik : i ≠ k := Ne.symm hki
          simp [hki, hik, Int.neg_mul]
    have hright :
        sumFin 4 (fun k => shifted3U i k * (x * (if k = j then 1 else 0) - shifted3LBlock k j)) =
        x * shifted3U i j - sumFin 4 (fun k => shifted3U i k * shifted3LBlock k j) := by
      rw [sumFin_congr (g := fun k => (if k = j then x * shifted3U i j else 0) - shifted3U i k * shifted3LBlock k j)]
      · rw [sumFin_sub, sumFin_eq_single]
      · intro k
        by_cases hkj : k = j
        · subst hkj; simp [Int.mul_comm]; grind
        · simp [hkj, Int.mul_neg]
    rw [hleft, hright, hLU]
  have hdetB : det (shifted3Block x) = x * (x - 2) * (x * x - 4 * x + 2) := by
    rw [det_row0_single (shifted3Block x) (by
      intro j hj
      rcases j with ⟨j, hjl⟩
      dsimp at hj
      have : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases this with rfl | rfl | rfl <;> rfl)]
    rw [det_row0_single (minor00 (shifted3Block x)) (by
      intro j hj
      rcases j with ⟨j, hjl⟩
      dsimp at hj
      have : j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl <;> rfl)]
    have h00 : shifted3Block x ⟨0, by decide⟩ ⟨0, by decide⟩ = x := rfl
    have h11 : minor00 (shifted3Block x) ⟨0, by decide⟩ ⟨0, by decide⟩ = x - 2 := rfl
    have h22 : det (minor00 (minor00 (shifted3Block x))) = x * x - 4 * x + 2 := by
      rw [det_two]
      change (x - 3) * (x - 1) - 1 * 1 = x * x - 4 * x + 2
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
    rw [h00, h11, h22, Int.mul_assoc]
  have hdet := congrArg det hAU
  rw [det_mul, det_mul, hdetB, Int.mul_comm (det shifted3U)] at hdet
  exact Int.eq_of_mul_eq_mul_right hdetU_ne hdet

theorem sharpness_noncommute_L0_L1 :
    matMul (evenSumLaplacian 2) evenSum1Laplacian2 ≠
    matMul evenSum1Laplacian2 (evenSumLaplacian 2) := by
  intro h
  have hentry := congrFun (congrFun h ⟨0, by decide⟩) ⟨1, by decide⟩
  revert hentry
  decide

/-! ============================================================================
    NON-VACUITY WITNESSES (Kernel-Checked Concrete Instantiations)
    ============================================================================ -/

/-- Non-vacuity witness 1: `dyadicTau` at `k = 1, 2, 3` matches exact Kirchhoff spanning-tree counts `1, 60, 49545216`. -/
theorem witness_dyadic_k1 : dyadicTau 1 = 1 := by decide
theorem witness_dyadic_k2 : dyadicTau 2 = 60 := by decide
theorem witness_dyadic_k3 : dyadicTau 3 = 49545216 := by decide

/-- Non-vacuity witness 2: direct `det (minor00 (dyadicLaplacian 2)) = 60` via our Levi-Civita determinant! -/
theorem witness_dyadic_det_k2 :
    det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ 2)) (dyadicLaplacian 2))) = 60 := by
  rw [dyadic_spanning_trees 2 (by decide)]
  decide

/-- Non-vacuity witness 3: `carryExactTau` at `k = 1, 2, 3` matches `1, 8, 24576`. -/
theorem witness_carryExact_k1 : carryExactTau 1 = 1 := by decide
theorem witness_carryExact_k2 : carryExactTau 2 = 8 := by decide
theorem witness_carryExact_k3 : carryExactTau 3 = 24576 := by decide

theorem witness_carryExact_det_k2 :
    det (minor00 (cast (congrArg Mat (pow2_eq_pred_succ 2)) (carryExactLaplacian 2))) = 8 := by
  rw [carryExact_spanning_trees 2 (by decide)]
  decide

/-- Non-vacuity witness 4: constructive `Nonempty` witness inhabiting all hypotheses of `orthogonal_eigenbasis_kirchhoff`. -/
theorem witness_nonvacuous_engine :
    Nonempty { p : (k : Nat) × (Fin (2 ^ k) -> Int) × (Fin (2 ^ k) -> Int) //
      p.1 = 2 ∧
      matMul (matTranspose (shellQ p.1)) (shellQ p.1) = matDiag p.2.1 ∧
      (∀ i, p.2.1 i ≠ 0) ∧
      matMul (dyadicLaplacian p.1) (shellQ p.1) = matMul (shellQ p.1) (matDiag p.2.2) } := by
  refine ⟨⟨⟨2, shellNorm 2, shellEig 2 (carryXorC dyadicH) (carryXorPhi dyadicH)⟩, rfl, ?_, ?_, ?_⟩⟩
  · exact shellQ_orth 2
  · exact shellNorm_ne_zero 2
  · rw [dyadicLaplacian, carryXorLaplacian_eq_shellLaplacian]
    exact shellLaplacian_diag 2 (carryXorC dyadicH) (carryXorPhi dyadicH)

end ShellWalshEngine
