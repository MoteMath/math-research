import CarryDeterminants.MixedRadix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Theorem 1: The Cantor Non-Vanishing & Tropical Uniqueness Theorem
# for Mixed-Radix and Base-`B` Carry Matrices

For any mixed-radix sequence `b : ℕ → ℕ` with `∀ r, 2 ≤ b r`, any depth `k`, any `1 ≤ n ≤ place b k`,
and any commutative ring `R`:
1. (**Vanishing direction**) If `n - 1` has *any* mixed-radix digit `d_r(n - 1) ∉ {0, b r - 1}`,
   then `det (carryMatrix b k n x) = 0` for *every* weight vector `x : ℕ → R`.
2. (**Unique Place-Value Pairing**) If every mixed-radix digit of `n - 1` lies in `{0, b r - 1}`,
   then there is a *unique* permutation `π* ∈ S_n` fixing `0` such that `i + π*(i)` is a place value
   `place b r` for every `1 ≤ i < n`.
3. (**Tropical Uniqueness & Exact Monic Leading Term**) Under the Cantor condition, the polynomial
   determinants `det (mixedCarryPolyMatrix b k n)` and (for uniform base `B`)
   `det (baseCarryPolyMatrix B k n)` are monic up to sign `Equiv.Perm.sign π* ∈ {+1, -1}`
   over every nontrivial commutative ring `R` (in particular over `ℤ` and `ZMod ℓ` for every prime `ℓ`).
4. (**Complete Iff Characterization**) Over any nontrivial commutative ring `R`,
   `det (baseCarryPolyMatrix B k n) ≠ 0` iff every base-`B` digit of `n - 1` lies in `{0, B - 1}`
   (and analogously for arbitrary mixed radix `b`).
-/

namespace NovelCarry

open Matrix Polynomial

lemma baseCarryPolyMatrix_eq_carryMatrix {R : Type*} [CommRing R] (B k n : ℕ) :
    baseCarryPolyMatrix (R := R) B k n =
      carryMatrix (fun _ => B) k n (fun _ => (Polynomial.X : Polynomial R)) := by
  ext i j
  simp [baseCarryPolyMatrix, carryMatrix, carryCount, Finset.prod_pow_eq_pow_sum]

/-! ### Part 1: Vanishing Direction via Multilinearity + Pigeonhole -/

/-- Replacing row `r` by `Row r - Row s` (with `r ≠ s`) preserves the determinant. -/
private lemma det_updateRow_sub_row {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) {r s : Fin n} (hrs : r ≠ s) :
    (M.updateRow r (M r - M s)).det = M.det := by
  have h : M r - M s = M r + (-1 : R) • M s := by
    ext j; simp [sub_eq_add_neg]
  rw [h, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul]
  have hzero : (M.updateRow r (M s)).det = 0 :=
    Matrix.det_zero_of_row_eq hrs (by simp [Matrix.updateRow_ne hrs.symm])
  rw [hzero, mul_zero, add_zero]

/-- Multilinearity of determinant in a single row over any finite linear combination. -/
private lemma det_updateRow_finset_sum {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} [DecidableEq ι]
    (A : Matrix (Fin n) (Fin n) R) (i : Fin n) (t : Finset ι) (w : ι → R) (u : ι → Fin n → R) :
    (A.updateRow i (∑ c ∈ t, w c • u c)).det =
      ∑ c ∈ t, w c * (A.updateRow i (u c)).det := by
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero i (by simp)
  | @insert c₀ t hc₀ ih =>
    rw [Finset.sum_insert hc₀, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
      ih, Finset.sum_insert hc₀]

/-- General multilinearity + pigeonhole rank barrier over ANY commutative ring `R`:
    if `m` distinct rows of `M` all lie in the span of `H < m` vectors `U 0, ..., U (H-1)`,
    then `M.det = 0`. -/
lemma det_eq_zero_of_rows_factor {R : Type*} [CommRing R] {n m H : ℕ}
    (hm : H < m) (M : Matrix (Fin n) (Fin n) R)
    (idx : Fin m ↪ Fin n) (W : Fin m → Fin H → R) (U : Fin H → Fin n → R)
    (hfac : ∀ a j, M (idx a) j = ∑ c : Fin H, W a c * U c j) :
    M.det = 0 := by
  suffices h : ∀ (s : Finset (Fin m)) (A : Matrix (Fin n) (Fin n) R),
      (∀ a ∈ s, ∀ j, A (idx a) j = ∑ c : Fin H, W a c * U c j) →
      A.det = ∑ f : {a // a ∈ s} → Fin H,
        (∏ a : {a // a ∈ s}, W a.1 (f a)) *
          (Matrix.of fun i j =>
            if hmem : ∃ a : {a // a ∈ s}, idx a.1 = i then
              U (f hmem.choose) j
            else A i j).det by
    rw [h Finset.univ M (fun a _ j => hfac a j)]
    apply Finset.sum_eq_zero
    intro f _
    have hcard : Fintype.card (Fin H) <
        Fintype.card {a : Fin m // a ∈ (Finset.univ : Finset (Fin m))} := by
      simp [hm]
    obtain ⟨a₁, a₂, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
    have hidx_ne : idx a₁.1 ≠ idx a₂.1 := fun h => hne (Subtype.ext (idx.injective h))
    have hdet0 : (Matrix.of fun i j =>
        if hmem : ∃ a : {a // a ∈ (Finset.univ : Finset (Fin m))}, idx a.1 = i then
          U (f hmem.choose) j
        else M i j).det = 0 := by
      apply Matrix.det_zero_of_row_eq hidx_ne
      ext j
      have hex1 : ∃ a : {a // a ∈ (Finset.univ : Finset (Fin m))}, idx a.1 = idx a₁.1 := ⟨a₁, rfl⟩
      have hex2 : ∃ a : {a // a ∈ (Finset.univ : Finset (Fin m))}, idx a.1 = idx a₂.1 := ⟨a₂, rfl⟩
      simp only [Matrix.of_apply, hex1, hex2, ↓reduceDIte]
      have hc1 : hex1.choose = a₁ := Subtype.ext (idx.injective hex1.choose_spec)
      have hc2 : hex2.choose = a₂ := Subtype.ext (idx.injective hex2.choose_spec)
      rw [hc1, hc2, hfeq]
    rw [hdet0, mul_zero]
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro A _
    have huniq : Unique ({a : Fin m // a ∈ (∅ : Finset (Fin m))} → Fin H) :=
      ⟨⟨fun a => (Finset.notMem_empty a.1 a.2).elim⟩,
       fun f => funext fun a => (Finset.notMem_empty a.1 a.2).elim⟩
    rw [Finset.sum_eq_single (default : {a // a ∈ (∅ : Finset (Fin m))} → Fin H)]
    · let f₀ : {a // a ∈ (∅ : Finset (Fin m))} → Fin H := default
      have hmat : (Matrix.of fun i j =>
          if hmem : ∃ a : {a // a ∈ (∅ : Finset (Fin m))}, idx a.1 = i then
            U (f₀ hmem.choose) j
          else A i j) = A := by
        ext i j; simp
      change A.det = (∏ a : {a // a ∈ (∅ : Finset (Fin m))}, W a.1 (f₀ a)) * _
      rw [hmat]
      simp [Finset.univ_eq_empty]
    · intro f _ hf; exact (hf (Subsingleton.elim f default)).elim
    · intro h; exact (h (Finset.mem_univ _)).elim
  | @insert a₀ s ha₀ ih =>
    intro A hA
    have hrow : A (idx a₀) = ∑ c : Fin H, W a₀ c • U c := by
      ext j
      simp [hA a₀ (Finset.mem_insert_self a₀ s) j]
    have hstep : A.det = ∑ c : Fin H, W a₀ c * (A.updateRow (idx a₀) (U c)).det := by
      conv_lhs => rw [← Matrix.updateRow_eq_self A (idx a₀), hrow]
      exact det_updateRow_finset_sum A (idx a₀) Finset.univ (W a₀) U
    rw [hstep]
    have hstep2 : ∀ c : Fin H,
        (A.updateRow (idx a₀) (U c)).det =
          ∑ f : {a // a ∈ s} → Fin H,
            (∏ a : {a // a ∈ s}, W a.1 (f a)) *
              (Matrix.of fun i j =>
                if hmem : ∃ a : {a // a ∈ s}, idx a.1 = i then U (f hmem.choose) j
                else (A.updateRow (idx a₀) (U c)) i j).det := by
      intro c
      apply ih
      intro a ha j
      have hne : idx a ≠ idx a₀ := fun h => ha₀ (idx.injective h ▸ ha)
      rw [Matrix.updateRow_ne hne]
      exact hA a (Finset.mem_insert_of_mem ha) j
    simp_rw [hstep2, Finset.mul_sum]
    let e : (Fin H × ({a // a ∈ s} → Fin H)) ≃ ({a // a ∈ insert a₀ s} → Fin H) :=
      { toFun := fun cf a =>
          if h : a.1 = a₀ then cf.1 else cf.2 ⟨a.1, (Finset.mem_insert.mp a.2).resolve_left h⟩
        invFun := fun g =>
          (g ⟨a₀, Finset.mem_insert_self a₀ s⟩,
           fun a => g ⟨a.1, Finset.mem_insert_of_mem a.2⟩)
        left_inv := by
          rintro ⟨c, f⟩
          ext
          · simp
          · rename_i a
            have hne : a.1 ≠ a₀ := fun h => ha₀ (h ▸ a.2)
            simp [hne]
        right_inv := by
          intro g
          ext a
          by_cases h : a.1 = a₀
          · have ha : a = ⟨a₀, Finset.mem_insert_self a₀ s⟩ := Subtype.ext h
            subst ha; simp
          · simp [h] }
    rw [← Fintype.sum_prod_type', ← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    rintro ⟨c, f⟩ _
    rw [← mul_assoc]
    congr 1
    · have hprod : ∏ a : {a // a ∈ insert a₀ s}, W a.1 (e (c, f) a) =
          W a₀ c * ∏ a : {a // a ∈ s}, W a.1 (f a) := by
        let e2 : Option {a // a ∈ s} ≃ {a // a ∈ insert a₀ s} :=
          { toFun := fun o => match o with
              | none => ⟨a₀, Finset.mem_insert_self a₀ s⟩
              | some a => ⟨a.1, Finset.mem_insert_of_mem a.2⟩
            invFun := fun a =>
              if h : a.1 = a₀ then none
              else some ⟨a.1, (Finset.mem_insert.mp a.2).resolve_left h⟩
            left_inv := by
              rintro (rfl | ⟨a, ha⟩)
              · simp
              · have hne : a ≠ a₀ := fun h => ha₀ (h ▸ ha)
                simp [hne]
            right_inv := by
              rintro ⟨a, ha⟩
              by_cases h : a = a₀
              · subst h; simp
              · simp [h] }
        rw [← Equiv.prod_comp e2, Fintype.prod_option]
        congr 1
        · simp [e, e2]
        · apply Finset.prod_congr rfl
          rintro ⟨a, ha⟩ _
          have hne : a ≠ a₀ := fun h => ha₀ (h ▸ ha)
          simp [e, e2, hne]
      exact hprod.symm
    · congr 1
      ext i j
      simp only [Matrix.of_apply]
      by_cases hs : ∃ a : {a // a ∈ s}, idx a.1 = i
      · have hins : ∃ a : {a // a ∈ insert a₀ s}, idx a.1 = i :=
          ⟨⟨hs.choose.1, Finset.mem_insert_of_mem hs.choose.2⟩, hs.choose_spec⟩
        simp only [hs, hins, ↓reduceDIte]
        have hch : hins.choose.1 = hs.choose.1 :=
          idx.injective (hins.choose_spec.trans hs.choose_spec.symm)
        have hne : hins.choose.1 ≠ a₀ := fun h => ha₀ (h ▸ hch ▸ hs.choose.2)
        have heval : e (c, f) hins.choose = f hs.choose := by
          simp only [e, Equiv.coe_fn_mk, hne, ↓reduceDIte]
          congr 1
          exact Subtype.ext hch
        rw [heval]
      · simp only [hs, ↓reduceDIte]
        by_cases hi0 : i = idx a₀
        · subst hi0
          have hins : ∃ a : {a // a ∈ insert a₀ s}, idx a.1 = idx a₀ :=
            ⟨⟨a₀, Finset.mem_insert_self a₀ s⟩, rfl⟩
          simp only [hins, ↓reduceDIte, Matrix.updateRow_self]
          have hch : hins.choose.1 = a₀ := idx.injective hins.choose_spec
          have heval : e (c, f) hins.choose = c := by
            simp only [e, Equiv.coe_fn_mk, hch, ↓reduceDIte]
          rw [heval]
        · have hno : ¬ ∃ a : {a // a ∈ insert a₀ s}, idx a.1 = i := by
            rintro ⟨⟨a, ha⟩, hai⟩
            rcases Finset.mem_insert.mp ha with rfl | has
            · exact hi0 hai.symm
            · exact hs ⟨⟨a, has⟩, hai⟩
          simp only [hno, ↓reduceDIte, Matrix.updateRow_ne hi0]

/-- Arithmetic helper: if `d ∣ A`, `d ∣ P`, and `e < d`, then `(A + e) / P = A / P`. -/
private lemma div_add_lt_of_dvd {d A P e : ℕ} (_hd : 0 < d) (hP : 0 < P)
    (hdA : d ∣ A) (hdP : d ∣ P) (he : e < d) : (A + e) / P = A / P := by
  have h1 : A = P * (A / P) + A % P := (Nat.div_add_mod A P).symm
  have hd_mod : d ∣ A % P := by
    obtain ⟨q1, hq1⟩ := hdA
    obtain ⟨q2, hq2⟩ := hdP
    have hsub : A % P = A - P * (A / P) := by omega
    rw [hsub, hq1, hq2, mul_assoc, ← Nat.mul_sub_left_distrib]
    exact dvd_mul_right d _
  have hmod_lt : A % P + e < P := by
    obtain ⟨qm, hqm⟩ := hd_mod
    obtain ⟨qp, hqp⟩ := hdP
    have hlt : A % P < P := Nat.mod_lt A hP
    have hqlt : qm < qp := by nlinarith
    have hqle : qm + 1 ≤ qp := hqlt
    nlinarith
  have hsum : A + e = (A % P + e) + P * (A / P) := by linarith
  rw [hsum, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hmod_lt, zero_add]

/-- Carry invariance Lemma 1: if `mdigit b j r ≠ b r - 1`, then adding `place b r` to
    `a * place b (r + 1)` does not change `carryBit b · j t` at ANY position `t`. -/
private lemma carryBit_add_place_eq_of_digit_ne (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r)
    (r a j t : ℕ) (hd : mdigit b j r ≠ b r - 1) :
    carryBit b (a * place b (r + 1) + place b r) j t =
      carryBit b (a * place b (r + 1)) j t := by
  have hb0 : ∀ s, 0 < b s := fun s => by have := hb s; omega
  have hPr : 0 < place b r := place_pos b hb0 r
  have hPr1 : 0 < place b (r + 1) := place_pos b hb0 (r + 1)
  have hdj_lt : mdigit b j r < b r := mdigit_lt b hb0 j r
  have hdj_le : mdigit b j r + 1 < b r := by omega
  have hsmall : place b r + j % place b (r + 1) < place b (r + 1) := by
    have hmod : j % place b (r + 1) = j % place b r + mdigit b j r * place b r := by
      rw [place_succ, Nat.mod_mul, mdigit, mul_comm (place b r)]
    have hjr : j % place b r < place b r := Nat.mod_lt j hPr
    rw [hmod, place_succ]
    have : (mdigit b j r + 1) * place b r + place b r ≤ b r * place b r := by
      have hle : mdigit b j r + 2 ≤ b r := hdj_le
      nlinarith
    nlinarith
  by_cases ht : t < r
  · have hdvd : place b (t + 1) ∣ place b r := place_dvd_of_le b (by omega)
    have hdvd1 : place b (t + 1) ∣ place b (r + 1) := place_dvd_of_le b (by omega)
    have hm1 : (a * place b (r + 1) + place b r) % place b (t + 1) = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_add (dvd_mul_of_dvd_right hdvd1 a) hdvd)
    have hm2 : (a * place b (r + 1)) % place b (t + 1) = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdvd1 a)
    simp [carryBit, carryIn, hm1, hm2]
  · have hdvd : place b (r + 1) ∣ place b (t + 1) := place_dvd_of_le b (by omega)
    obtain ⟨M, hM⟩ := hdvd
    have hPt1 : 0 < place b (t + 1) := place_pos b hb0 (t + 1)
    have hMpos : 0 < M := by nlinarith
    have h1 : (a * place b (r + 1) + place b r) % place b (t + 1) =
        (a % M) * place b (r + 1) + place b r := by
      rw [hM]
      have hdiv : a = M * (a / M) + a % M := (Nat.div_add_mod a M).symm
      have hlt : (a % M) * place b (r + 1) + place b r < place b (r + 1) * M := by
        have ham : a % M + 1 ≤ M := Nat.mod_lt a hMpos
        have hbr : place b r < place b (r + 1) := by
          rw [place_succ]; have := hb r; nlinarith
        nlinarith
      have heq : a * place b (r + 1) + place b r =
          (a % M * place b (r + 1) + place b r) + (place b (r + 1) * M) * (a / M) := by
        calc a * place b (r + 1) + place b r
            = (M * (a / M) + a % M) * place b (r + 1) + place b r := by rw [← hdiv]
          _ = (a % M * place b (r + 1) + place b r) + (place b (r + 1) * M) * (a / M) := by ring
      rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have h2 : (a * place b (r + 1)) % place b (t + 1) = (a % M) * place b (r + 1) := by
      rw [hM, mul_comm a (place b (r + 1)), Nat.mul_mod_mul_left, mul_comm]
    have h3 : j % place b (t + 1) = ((j / place b (r + 1)) % M) * place b (r + 1) +
        j % place b (r + 1) := by
      rw [hM, Nat.mod_mul, mul_comm (place b (r + 1))]
      ring
    unfold carryBit carryIn
    rw [h1, h2, h3]
    have hL : (a % M * place b (r + 1) + place b r) +
        ((j / place b (r + 1)) % M * place b (r + 1) + j % place b (r + 1)) =
        (a % M + (j / place b (r + 1)) % M) * place b (r + 1) +
          (place b r + j % place b (r + 1)) := by ring
    have hR : a % M * place b (r + 1) +
        ((j / place b (r + 1)) % M * place b (r + 1) + j % place b (r + 1)) =
        (a % M + (j / place b (r + 1)) % M) * place b (r + 1) +
          j % place b (r + 1) := by ring
    rw [hL, hR]
    have hdivL := div_add_lt_of_dvd
      (A := (a % M + (j / place b (r + 1)) % M) * place b (r + 1))
      hPr1 hPt1 (dvd_mul_left _ _) ⟨M, hM⟩ hsmall
    have hdivR := div_add_lt_of_dvd
      (A := (a % M + (j / place b (r + 1)) % M) * place b (r + 1))
      hPr1 hPt1 (dvd_mul_left _ _) ⟨M, hM⟩ (Nat.mod_lt j hPr1)
    rw [hdivL, hdivR]

/-- Carry invariance Lemma 2: if `place b r ∣ i`, then `carryBit b i j t` depends on `j`
    only through `(j / place b r) * place b r` (all digits below `r` drop out). -/
private lemma carryBit_eq_of_dvd_left (b : ℕ → ℕ) (hb : ∀ r, 0 < b r)
    (r i j t : ℕ) (hdi : place b r ∣ i) :
    carryBit b i j t = carryBit b i ((j / place b r) * place b r) t := by
  have hPr : 0 < place b r := place_pos b hb r
  have hPt1 : 0 < place b (t + 1) := place_pos b hb (t + 1)
  by_cases ht : t < r
  · have hdvd : place b (t + 1) ∣ place b r := place_dvd_of_le b (by omega)
    have hmi : i % place b (t + 1) = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans hdvd hdi)
    unfold carryBit carryIn
    rw [hmi, zero_add, zero_add,
      Nat.div_eq_of_lt (Nat.mod_lt _ hPt1), Nat.div_eq_of_lt (Nat.mod_lt _ hPt1)]
  · have hdvd : place b r ∣ place b (t + 1) := place_dvd_of_le b (by omega)
    obtain ⟨Q, hQ⟩ := hdvd
    have hj_split : j % place b (t + 1) =
        ((j / place b r) * place b r) % place b (t + 1) + j % place b r := by
      have h1 : j % place b (t + 1) = j % place b r + ((j / place b r) % Q) * place b r := by
        rw [hQ, Nat.mod_mul, mul_comm (place b r)]
      have h2 : ((j / place b r) * place b r) % place b (t + 1) =
          ((j / place b r) % Q) * place b r := by
        rw [hQ, mul_comm (j / place b r) (place b r), Nat.mul_mod_mul_left, mul_comm]
      linarith
    have hdi_mod : place b r ∣ i % place b (t + 1) := by
      obtain ⟨qi, hqi⟩ := hdi
      have hdm : i = place b (t + 1) * (i / place b (t + 1)) + i % place b (t + 1) :=
        (Nat.div_add_mod i (place b (t + 1))).symm
      have hsub : i % place b (t + 1) = i - place b (t + 1) * (i / place b (t + 1)) := by omega
      rw [hsub, hqi, hQ, mul_assoc, ← Nat.mul_sub_left_distrib]
      exact dvd_mul_right _ _
    have hdj_mod : place b r ∣ ((j / place b r) * place b r) % place b (t + 1) := by
      rw [hQ, mul_comm (j / place b r) (place b r), Nat.mul_mod_mul_left]
      exact dvd_mul_right _ _
    unfold carryBit carryIn
    rw [hj_split, ← add_assoc]
    exact div_add_lt_of_dvd hPr hPt1 (dvd_add hdi_mod hdj_mod) ⟨Q, hQ⟩ (Nat.mod_lt j hPr)

/-- **Vanishing Half of Theorem 1**: Over *any* commutative ring `R` and *any* weight function
    `x : ℕ → R`, if `n - 1` has at least one mixed-radix digit `d_r(n - 1) ∉ {0, b r - 1}`,
    then `det (carryMatrix b k n x) = 0`. -/
theorem carryMatrix_det_eq_zero_of_non_extremal {R : Type*} [CommRing R]
    (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) (k n : ℕ) (hn1 : 1 ≤ n) (x : ℕ → R)
    {r : ℕ} (_hr : r < k) (hd0 : mdigit b (n - 1) r ≠ 0) (hd1 : mdigit b (n - 1) r ≠ b r - 1) :
    (carryMatrix b k n x).det = 0 := by
  have hb0 : ∀ s, 0 < b s := fun s => by have := hb s; omega
  have hPr : 0 < place b r := place_pos b hb0 r
  have hPr1 : 0 < place b (r + 1) := place_pos b hb0 (r + 1)
  have hdj_lt : mdigit b (n - 1) r < b r := mdigit_lt b hb0 (n - 1) r
  set H := (n - 1) / place b (r + 1)
  have hn_decomp : n - 1 = H * place b (r + 1) + mdigit b (n - 1) r * place b r +
      (n - 1) % place b r := by
    have h1 : n - 1 = place b (r + 1) * H + (n - 1) % place b (r + 1) :=
      (Nat.div_add_mod (n - 1) (place b (r + 1))).symm
    have h2 : (n - 1) % place b (r + 1) =
        (n - 1) % place b r + mdigit b (n - 1) r * place b r := by
      rw [place_succ, Nat.mod_mul, mdigit, mul_comm (place b r)]
    have h3 : place b (r + 1) * H = H * place b (r + 1) := mul_comm _ _
    omega
  have hi1_lt : ∀ a : Fin (H + 1), a.1 * place b (r + 1) + place b r < n := by
    intro a
    have ha : a.1 ≤ H := Nat.lt_succ_iff.mp a.2
    have h1 : a.1 * place b (r + 1) ≤ H * place b (r + 1) := Nat.mul_le_mul_right _ ha
    have h2 : place b r ≤ mdigit b (n - 1) r * place b r := by
      have : 1 ≤ mdigit b (n - 1) r := by omega
      nlinarith
    omega
  have hi0_lt : ∀ a : Fin (H + 1), a.1 * place b (r + 1) < n := by
    intro a; have := hi1_lt a; omega
  let i0 : Fin (H + 1) → Fin n := fun a => ⟨a.1 * place b (r + 1), hi0_lt a⟩
  let i1 : Fin (H + 1) → Fin n := fun a => ⟨a.1 * place b (r + 1) + place b r, hi1_lt a⟩
  have hi1_inj : Function.Injective i1 := by
    intro a₁ a₂ h
    have hval : a₁.1 * place b (r + 1) + place b r = a₂.1 * place b (r + 1) + place b r :=
      congrArg Fin.val h
    have : a₁.1 * place b (r + 1) = a₂.1 * place b (r + 1) := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hPr1 this)
  have hi_disj : ∀ a₁ a₂ : Fin (H + 1), i1 a₁ ≠ i0 a₂ := by
    intro a₁ a₂ h
    have hval : a₁.1 * place b (r + 1) + place b r = a₂.1 * place b (r + 1) :=
      congrArg Fin.val h
    have hmod := congrArg (fun m => (m / place b r) % b r) hval
    have hL : ((a₁.1 * place b (r + 1) + place b r) / place b r) % b r = 1 := by
      rw [place_succ, show a₁.1 * (place b r * b r) + place b r =
          place b r * (a₁.1 * b r + 1) by ring,
          Nat.mul_div_right _ hPr, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (hb r)]
    have hR : ((a₂.1 * place b (r + 1)) / place b r) % b r = 0 := by
      rw [place_succ, show a₂.1 * (place b r * b r) = place b r * (a₂.1 * b r) by ring,
          Nat.mul_div_right _ hPr, Nat.mul_mod_left]
    rw [hL, hR] at hmod
    omega
  set M := carryMatrix b k n x
  let M' : Matrix (Fin n) (Fin n) R :=
    Matrix.of fun i j =>
      if h : ∃ a : Fin (H + 1), i1 a = i then
        M (i1 h.choose) j - M (i0 h.choose) j
      else M i j
  have hdet_eq : M'.det = M.det := by
    suffices hstep : ∀ s : Finset (Fin (H + 1)),
        (Matrix.of fun i j =>
          if h : ∃ a ∈ s, i1 a = i then
            M (i1 h.choose) j - M (i0 h.choose) j
          else M i j).det = M.det by
      have hM' : M' = Matrix.of fun i j =>
          if h : ∃ a ∈ (Finset.univ : Finset (Fin (H + 1))), i1 a = i then
            M (i1 h.choose) j - M (i0 h.choose) j
          else M i j := by
        ext i j
        simp only [M', Matrix.of_apply]
        by_cases hex : ∃ a : Fin (H + 1), i1 a = i
        · have hex' : ∃ a ∈ (Finset.univ : Finset (Fin (H + 1))), i1 a = i :=
            ⟨hex.choose, Finset.mem_univ _, hex.choose_spec⟩
          simp only [hex, hex', ↓reduceDIte]
          have hch : hex'.choose = hex.choose :=
            hi1_inj (hex'.choose_spec.2.trans hex.choose_spec.symm)
          rw [hch]
        · have hex' : ¬ ∃ a ∈ (Finset.univ : Finset (Fin (H + 1))), i1 a = i := by
            rintro ⟨a, _, ha⟩; exact hex ⟨a, ha⟩
          simp only [hex, hex', ↓reduceDIte]
      rw [hM', hstep Finset.univ]
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (Matrix.of fun i j =>
          if h : ∃ a ∈ (∅ : Finset (Fin (H + 1))), i1 a = i then
            M (i1 h.choose) j - M (i0 h.choose) j
          else M i j) = M := by
        ext i j; simp
      rw [this]
    | @insert a₀ s ha₀ ih =>
      set A : Matrix (Fin n) (Fin n) R :=
        Matrix.of fun i j =>
          if h : ∃ a ∈ s, i1 a = i then
            M (i1 h.choose) j - M (i0 h.choose) j
          else M i j
      have hupd : (Matrix.of fun i j =>
          if h : ∃ a ∈ insert a₀ s, i1 a = i then
            M (i1 h.choose) j - M (i0 h.choose) j
          else M i j) = A.updateRow (i1 a₀) (A (i1 a₀) - A (i0 a₀)) := by
        ext i j
        have hAi1 : A (i1 a₀) j = M (i1 a₀) j := by
          have hno : ¬ ∃ a ∈ s, i1 a = i1 a₀ := by
            rintro ⟨a, has, ha⟩; exact ha₀ (hi1_inj ha ▸ has)
          simp [A, hno]
        have hAi0 : A (i0 a₀) j = M (i0 a₀) j := by
          have hno : ¬ ∃ a ∈ s, i1 a = i0 a₀ := by
            rintro ⟨a, _, ha⟩; exact hi_disj a a₀ ha
          simp [A, hno]
        by_cases hi : i = i1 a₀
        · subst hi
          have hex : ∃ a ∈ insert a₀ s, i1 a = i1 a₀ := ⟨a₀, Finset.mem_insert_self _ _, rfl⟩
          simp only [Matrix.of_apply, hex, ↓reduceDIte, Matrix.updateRow_self, Pi.sub_apply,
            hAi1, hAi0]
          have hch : hex.choose = a₀ := hi1_inj hex.choose_spec.2
          rw [hch]
        · rw [Matrix.updateRow_ne hi]
          simp only [Matrix.of_apply, A]
          by_cases hs : ∃ a ∈ s, i1 a = i
          · have hex : ∃ a ∈ insert a₀ s, i1 a = i :=
              ⟨hs.choose, Finset.mem_insert_of_mem hs.choose_spec.1, hs.choose_spec.2⟩
            simp only [hex, hs, ↓reduceDIte]
            have hch : hex.choose = hs.choose :=
              hi1_inj (hex.choose_spec.2.trans hs.choose_spec.2.symm)
            rw [hch]
          · have hno : ¬ ∃ a ∈ insert a₀ s, i1 a = i := by
              rintro ⟨a, ha, hai⟩
              rcases Finset.mem_insert.mp ha with rfl | has
              · exact hi hai.symm
              · exact hs ⟨a, has, hai⟩
            simp only [hno, hs, ↓reduceDIte]
      rw [hupd, det_updateRow_sub_row A (hi_disj a₀ a₀), ih]
  rw [← hdet_eq]
  let idx : Fin (H + 1) ↪ Fin n := ⟨i1, hi1_inj⟩
  let W : Fin (H + 1) → Fin H → R := fun a c =>
    (∏ t ∈ Finset.range k, x t ^ carryBit b (a.1 * place b (r + 1) + place b r)
      (c.1 * place b (r + 1) + (b r - 1) * place b r) t) -
    (∏ t ∈ Finset.range k, x t ^ carryBit b (a.1 * place b (r + 1))
      (c.1 * place b (r + 1) + (b r - 1) * place b r) t)
  let U : Fin H → Fin n → R := fun c j =>
    if mdigit b j.1 r = b r - 1 ∧ j.1 / place b (r + 1) = c.1 then 1 else 0
  apply det_eq_zero_of_rows_factor (Nat.lt_succ_self H) M' idx W U
  intro a j
  have hex : ∃ a' : Fin (H + 1), i1 a' = i1 a := ⟨a, rfl⟩
  have hch : hex.choose = a := hi1_inj hex.choose_spec
  simp only [M', idx, Function.Embedding.coeFn_mk, Matrix.of_apply, hex, ↓reduceDIte, hch]
  by_cases hdj : mdigit b j.1 r = b r - 1
  · have hj_div_lt : j.1 / place b (r + 1) < H := by
      by_contra hge
      push Not at hge
      have hj_decomp : j.1 = (j.1 / place b (r + 1)) * place b (r + 1) +
          mdigit b j.1 r * place b r + j.1 % place b r := by
        have h1 := (Nat.div_add_mod j.1 (place b (r + 1))).symm
        have h2 : j.1 % place b (r + 1) = j.1 % place b r + mdigit b j.1 r * place b r := by
          rw [place_succ, Nat.mod_mul, mdigit, mul_comm (place b r)]
        have h3 : place b (r + 1) * (j.1 / place b (r + 1)) =
            (j.1 / place b (r + 1)) * place b (r + 1) := mul_comm _ _
        omega
      have h1 : H * place b (r + 1) ≤ (j.1 / place b (r + 1)) * place b (r + 1) :=
        Nat.mul_le_mul_right _ hge
      have h2 : mdigit b (n - 1) r * place b r + place b r ≤ (b r - 1) * place b r := by
        have hle : mdigit b (n - 1) r + 1 ≤ b r - 1 := by omega
        calc mdigit b (n - 1) r * place b r + place b r
            = (mdigit b (n - 1) r + 1) * place b r := by ring
          _ ≤ (b r - 1) * place b r := Nat.mul_le_mul_right _ hle
      have h3 : (n - 1) % place b r < place b r := Nat.mod_lt _ hPr
      rw [hdj] at hj_decomp
      omega
    let c₀ : Fin H := ⟨j.1 / place b (r + 1), hj_div_lt⟩
    rw [Finset.sum_eq_single c₀]
    · simp only [U, c₀, hdj, and_self, ↓reduceIte, mul_one]
      have hj_trunc : (j.1 / place b r) * place b r =
          (j.1 / place b (r + 1)) * place b (r + 1) + (b r - 1) * place b r := by
        have h1 : j.1 / place b r = b r * (j.1 / place b (r + 1)) + mdigit b j.1 r := by
          unfold mdigit
          rw [place_succ, ← Nat.div_div_eq_div_mul]
          exact (Nat.div_add_mod (j.1 / place b r) (b r)).symm
        rw [h1, hdj, place_succ]
        ring
      have hdvd1 : place b r ∣ a.1 * place b (r + 1) + place b r := by
        rw [place_succ]; exact dvd_add ⟨a.1 * b r, by ring⟩ (dvd_refl _)
      have hdvd0 : place b r ∣ a.1 * place b (r + 1) := by
        rw [place_succ]; exact ⟨a.1 * b r, by ring⟩
      simp only [M, carryMatrix, i1, i0, W, Matrix.of_apply]
      congr 1
      · apply Finset.prod_congr rfl
        intro t _
        rw [carryBit_eq_of_dvd_left b hb0 r _ j.1 t hdvd1, hj_trunc]
      · apply Finset.prod_congr rfl
        intro t _
        rw [carryBit_eq_of_dvd_left b hb0 r _ j.1 t hdvd0, hj_trunc]
    · intro c _ hc
      have hne : j.1 / place b (r + 1) ≠ c.1 := fun h => hc (Fin.ext h.symm)
      simp [U, hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · have hU0 : ∀ c : Fin H, U c j = 0 := fun c => by simp [U, hdj]
    simp only [hU0, mul_zero, Finset.sum_const_zero]
    simp only [M, carryMatrix, i1, i0, Matrix.of_apply]
    rw [sub_eq_zero]
    apply Finset.prod_congr rfl
    intro t _
    rw [carryBit_add_place_eq_of_digit_ne b hb r a.1 j.1 t hdj]

/-! ### Part 2: Unique Place-Value Pairing & Tropical Uniqueness -/

/-- The mixed-radix digit sum `mdigitSum b k m` equals `0` (for `m < place b k`) iff `m = 0`. -/
lemma mdigitSum_eq_zero_iff (b : ℕ → ℕ) {k m : ℕ} (hm : m < place b k) :
    mdigitSum b k m = 0 ↔ m = 0 := by
  constructor
  · intro h
    rw [eq_sum_mdigit b hm]
    apply Finset.sum_eq_zero
    intro r hr
    have h0 : mdigit b m r = 0 := (Finset.sum_eq_zero_iff.mp h) r hr
    simp [h0]
  · rintro rfl
    unfold mdigitSum
    simp [mdigit_zero]

/-- Digit of a place value `place b r`: equals `1` at `r` and `0` everywhere else (when `b ≥ 2`). -/
lemma mdigit_place (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) (r t : ℕ) :
    mdigit b (place b r) t = if t = r then 1 else 0 := by
  have hb0 : ∀ s, 0 < b s := fun s => by have := hb s; omega
  by_cases htr : t = r
  · subst htr
    simp [mdigit, Nat.div_self (place_pos b hb0 t), Nat.mod_eq_of_lt (hb t)]
  · simp only [htr, ↓reduceIte]
    by_cases hlt : t < r
    · have hdvd : place b (t + 1) ∣ place b r := place_dvd_of_le b (by omega)
      obtain ⟨q, hq⟩ := hdvd
      unfold mdigit
      rw [hq, place_succ, mul_assoc, Nat.mul_div_right _ (place_pos b hb0 t), Nat.mul_mod_right]
    · have hplt : place b r < place b t := by
        calc place b r < place b r * b r := by
              have h1 := place_pos b hb0 r; have h2 := hb r; nlinarith
          _ = place b (r + 1) := rfl
          _ ≤ place b t := place_mono b (fun s => by have := hb s; omega) (by omega)
      exact mdigit_of_lt_place b hplt

/-- For `m < place b (k + 1)`, `mdigitSum b (k + 1) m = 1` iff `m = place b r` for some `r ≤ k`. -/
lemma mdigitSum_eq_one_iff (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) {k m : ℕ}
    (hm : m < place b (k + 1)) :
    mdigitSum b (k + 1) m = 1 ↔ ∃ r ≤ k, m = place b r := by
  constructor
  · intro h
    have hex : ∃ r ∈ Finset.range (k + 1), mdigit b m r ≠ 0 := by
      by_contra hall
      push Not at hall
      have : mdigitSum b (k + 1) m = 0 := Finset.sum_eq_zero hall
      omega
    obtain ⟨r, hr, hrne⟩ := hex
    have hsum_split : mdigit b m r + ∑ t ∈ (Finset.range (k + 1)).erase r, mdigit b m t = 1 := by
      rw [Finset.add_sum_erase _ _ hr]
      exact h
    have hdr : mdigit b m r = 1 := by omega
    have hrest : ∑ t ∈ (Finset.range (k + 1)).erase r, mdigit b m t = 0 := by omega
    refine ⟨r, Nat.lt_succ_iff.mp (Finset.mem_range.mp hr), ?_⟩
    rw [eq_sum_mdigit b hm, Finset.sum_eq_single r]
    · rw [hdr, one_mul]
    · intro t ht htr
      have h0 : mdigit b m t = 0 :=
        (Finset.sum_eq_zero_iff.mp hrest) t (Finset.mem_erase.mpr ⟨htr, ht⟩)
      simp [h0]
    · intro hnot; exact (hnot hr).elim
  · rintro ⟨r, hrk, rfl⟩
    unfold mdigitSum
    rw [Finset.sum_eq_single r]
    · simp [mdigit_place b hb r r]
    · intro t _ htr
      simp [mdigit_place b hb r t, htr]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim

/-- Sum of `(b r - 1) * place b r` for `r < t` equals `place b t - 1`. -/
lemma sum_max_digits (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (t : ℕ) :
    ∑ r ∈ Finset.range t, (b r - 1) * place b r = place b t - 1 := by
  induction t with
  | zero => simp [place]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, place_succ]
    have hPt : 1 ≤ place b t := place_pos b (fun r => hb r) t
    have hbt : 1 ≤ b t := hb t
    have hmul : (b t - 1) * place b t + place b t = place b t * b t := by
      have := Nat.sub_add_cancel hbt
      calc (b t - 1) * place b t + place b t = (b t - 1 + 1) * place b t := by ring
        _ = b t * place b t := by rw [this]
        _ = place b t * b t := mul_comm _ _
    omega

/-- Uniqueness of mixed-radix digit representation. -/
lemma mdigit_of_sum (b : ℕ → ℕ) (hb : ∀ r, 0 < b r) (t : ℕ) (d : ℕ → ℕ)
    (hd : ∀ r < t, d r < b r) :
    ∀ r < t, mdigit b (∑ j ∈ Finset.range t, d j * place b j) r = d r := by
  induction t with
  | zero => intro r hr; omega
  | succ t ih =>
    intro r hr
    have hlt : ∑ j ∈ Finset.range t, d j * place b j < place b t := by
      have hle : ∑ j ∈ Finset.range t, d j * place b j ≤
          ∑ j ∈ Finset.range t, (b j - 1) * place b j := by
        apply Finset.sum_le_sum
        intro j hj
        have hdj := hd j (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))
        exact Nat.mul_le_mul_right _ (by omega)
      have hmax := sum_max_digits b (fun j => hb j) t
      have hPt := place_pos b hb t
      omega
    rw [Finset.sum_range_succ]
    by_cases hrt : r = t
    · subst hrt
      unfold mdigit
      rw [Nat.add_mul_div_right _ _ (place_pos b hb r), Nat.div_eq_of_lt hlt, zero_add]
      exact Nat.mod_eq_of_lt (hd r (Nat.lt_succ_self r))
    · have hrt' : r < t := by omega
      have hdvd : place b (r + 1) ∣ place b t := place_dvd_of_le b (by omega)
      obtain ⟨Q, hQ⟩ := hdvd
      unfold mdigit
      rw [hQ, place_succ, show d t * (place b r * b r * Q) =
          place b r * (b r * (d t * Q)) by ring,
          Nat.add_mul_div_left _ _ (place_pos b hb r), Nat.add_mul_mod_self_left]
      exact ih (fun j hj => hd j (Nat.lt_succ_of_lt hj)) r hrt'

/-- Digitwise complementation: if `m < place b t` has all digits in `{0, b r - 1}`,
    then so does `(place b t - 1) - m`. -/
private lemma cantor_complement (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) {t m : ℕ}
    (hm : m < place b t) (hC : ∀ r < t, mdigit b m r = 0 ∨ mdigit b m r = b r - 1) :
    ∀ r < t, mdigit b (place b t - 1 - m) r = 0 ∨ mdigit b (place b t - 1 - m) r = b r - 1 := by
  have hb0 : ∀ s, 0 < b s := fun s => by have := hb s; omega
  let d : ℕ → ℕ := fun r => b r - 1 - mdigit b m r
  have hsum : ∑ r ∈ Finset.range t, d r * place b r = place b t - 1 - m := by
    have hadd : ∑ r ∈ Finset.range t, d r * place b r +
        ∑ r ∈ Finset.range t, mdigit b m r * place b r =
        ∑ r ∈ Finset.range t, (b r - 1) * place b r := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      have hle : mdigit b m r ≤ b r - 1 := by
        have := mdigit_lt b hb0 m r; omega
      have : d r + mdigit b m r = b r - 1 := Nat.sub_add_cancel hle
      calc d r * place b r + mdigit b m r * place b r
          = (d r + mdigit b m r) * place b r := by ring
        _ = (b r - 1) * place b r := by rw [this]
    rw [← eq_sum_mdigit b hm, sum_max_digits b (fun s => by have := hb s; omega) t] at hadd
    omega
  intro r hr
  rw [← hsum, mdigit_of_sum b hb0 t d (fun j _ => by have := hb j; dsimp [d]; omega) r hr]
  rcases hC r hr with h0 | h1
  · right; simp [d, h0]
  · left; simp [d, h1]

/-- **Unique Place-Value Pairing Theorem**: For any mixed radix `b` (`∀ r, 2 ≤ b r`) and any
    Cantor index `1 ≤ n ≤ place b k`, there exists a UNIQUE permutation `π* ∈ S_n` fixing `0`
    such that `i + π*(i)` is a place value `place b r` (`r ≤ k`) for all `1 ≤ i < n`. -/
theorem existsUnique_placeValue_perm (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) :
    ∀ n : ℕ, ∀ k : ℕ, (hn1 : 1 ≤ n) → n ≤ place b k →
      (∀ r < k, mdigit b (n - 1) r = 0 ∨ mdigit b (n - 1) r = b r - 1) →
      ∃! π : Equiv.Perm (Fin n),
        π ⟨0, hn1⟩ = ⟨0, hn1⟩ ∧
        ∀ i : Fin n, i.1 ≠ 0 → ∃ r ≤ k, i.1 + (π i).1 = place b r := by
  have hb0 : ∀ s, 0 < b s := fun s => by have := hb s; omega
  have hb1 : ∀ s, 1 ≤ b s := fun s => by have := hb s; omega
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hn1 hnk hC
    by_cases hn_eq1 : n = 1
    · subst hn_eq1
      refine ⟨Equiv.refl _, ⟨rfl, fun i hi => by omega⟩, fun σ _ => ?_⟩
      ext i; omega
    · have hn2 : 2 ≤ n := by omega
      have hnm1_pos : 0 < n - 1 := by omega
      have hnm1_lt : n - 1 < place b k := by omega
      let S := (Finset.range k).filter (fun r => mdigit b (n - 1) r ≠ 0)
      have hS_ne : S.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hzero : mdigitSum b k (n - 1) = 0 := by
          apply Finset.sum_eq_zero
          intro r hr
          by_contra hne0
          have hmem : r ∈ S := Finset.mem_filter.mpr ⟨hr, hne0⟩
          rw [hne] at hmem; exact Finset.notMem_empty r hmem
        have := (mdigitSum_eq_zero_iff b hnm1_lt).mp hzero
        omega
      let t := S.max' hS_ne
      have ht_mem : t ∈ S := Finset.max'_mem S hS_ne
      have ht_lt_k : t < k := Finset.mem_range.mp (Finset.mem_filter.mp ht_mem).1
      have hdt_ne : mdigit b (n - 1) t ≠ 0 := (Finset.mem_filter.mp ht_mem).2
      have hdt_eq : mdigit b (n - 1) t = b t - 1 := (hC t ht_lt_k).resolve_left hdt_ne
      have hnm1_lt_t1 : n - 1 < place b (t + 1) := by
        have hsum_eq : n - 1 = ∑ r ∈ Finset.range (t + 1), mdigit b (n - 1) r * place b r := by
          calc n - 1 = ∑ r ∈ Finset.range k, mdigit b (n - 1) r * place b r :=
                eq_sum_mdigit b hnm1_lt
            _ = ∑ r ∈ Finset.range (t + 1), mdigit b (n - 1) r * place b r := by
                symm
                apply Finset.sum_subset (Finset.range_mono (by omega : t + 1 ≤ k))
                intro r hr hrnot
                have hgt : t < r := by
                  have := Finset.mem_range.mp hr
                  have : ¬ r < t + 1 := fun h => hrnot (Finset.mem_range.mpr h)
                  omega
                have h0 : mdigit b (n - 1) r = 0 := by
                  by_contra hne0
                  have hle := Finset.le_max' S r (Finset.mem_filter.mpr ⟨hr, hne0⟩)
                  omega
                simp [h0]
        have hle : ∑ r ∈ Finset.range (t + 1), mdigit b (n - 1) r * place b r ≤
            ∑ r ∈ Finset.range (t + 1), (b r - 1) * place b r := by
          apply Finset.sum_le_sum
          intro r _
          have := mdigit_lt b hb0 (n - 1) r
          exact Nat.mul_le_mul_right _ (by omega)
        have hmax := sum_max_digits b hb1 (t + 1)
        have hPpos := place_pos b hb0 (t + 1)
        omega
      set m := (n - 1) % place b t
      have hm_lt : m < place b t := Nat.mod_lt _ (place_pos b hb0 t)
      have hn_decomp : n - 1 = (b t - 1) * place b t + m := by
        have h1 : (n - 1) % place b (t + 1) = m + place b t * mdigit b (n - 1) t := by
          rw [place_succ, Nat.mod_mul]; rfl
        have h2 : n - 1 = (n - 1) % place b (t + 1) := (Nat.mod_eq_of_lt hnm1_lt_t1).symm
        rw [h2, h1, hdt_eq]; ring
      set n' := place b t - m
      have hn'_pos : 1 ≤ n' := by omega
      have hn'_le_Pt : n' ≤ place b t := Nat.sub_le _ _
      have hPt_lt_n : place b t < n := by
        have hbt : 1 ≤ b t - 1 := by have := hb t; omega
        have : place b t ≤ (b t - 1) * place b t := by
          simpa using Nat.mul_le_mul_right (place b t) hbt
        omega
      have hn'_lt_n : n' < n := by omega
      have hsum_nn' : n' + (n - 1) = place b (t + 1) := by
        rw [place_succ]
        have hbt : 1 ≤ b t := hb1 t
        have hmul : place b t + (b t - 1) * place b t = place b t * b t := by
          have := Nat.sub_add_cancel hbt
          calc place b t + (b t - 1) * place b t = (b t - 1 + 1) * place b t := by ring
            _ = b t * place b t := by rw [this]
            _ = place b t * b t := mul_comm _ _
        omega
      have hC_m : ∀ r < t, mdigit b m r = 0 ∨ mdigit b m r = b r - 1 := by
        intro r hr
        have hdm : mdigit b m r = mdigit b (n - 1) r := by
          have hdvd : place b (r + 1) ∣ place b t := place_dvd_of_le b (by omega)
          obtain ⟨Q, hQ⟩ := hdvd
          set qn := (n - 1) / place b t
          have h1 : n - 1 = place b t * qn + m := (Nat.div_add_mod (n - 1) (place b t)).symm
          have h2 : n - 1 = m + place b r * (b r * (Q * qn)) := by
            rw [h1, hQ, place_succ]; ring
          unfold mdigit
          conv_rhs => rw [h2, Nat.add_mul_div_left _ _ (place_pos b hb0 r),
            Nat.add_mul_mod_self_left]
        rw [hdm]
        exact hC r (by omega)
      have hC_n' : ∀ r < t, mdigit b (n' - 1) r = 0 ∨ mdigit b (n' - 1) r = b r - 1 := by
        have : n' - 1 = place b t - 1 - m := by omega
        rw [this]
        exact cantor_complement b hb hm_lt hC_m
      obtain ⟨π', ⟨hπ'0, hπ'pv⟩, hπ'uniq⟩ := ih n' hn'_lt_n t hn'_pos hn'_le_Pt hC_n'
      have hrev_bound : ∀ i : ℕ, n' ≤ i → i < n →
          n' ≤ place b (t + 1) - i ∧ place b (t + 1) - i < n := by
        intro i hi1 hi2; omega
      let f : Fin n → Fin n := fun i =>
        if h : i.1 < n' then ⟨(π' ⟨i.1, h⟩).1, lt_trans (π' ⟨i.1, h⟩).2 hn'_lt_n⟩
        else ⟨place b (t + 1) - i.1, (hrev_bound i.1 (by omega) i.2).2⟩
      let g : Fin n → Fin n := fun i =>
        if h : i.1 < n' then ⟨(π'.symm ⟨i.1, h⟩).1, lt_trans (π'.symm ⟨i.1, h⟩).2 hn'_lt_n⟩
        else ⟨place b (t + 1) - i.1, (hrev_bound i.1 (by omega) i.2).2⟩
      have hfg : Function.LeftInverse g f := by
        intro i
        dsimp only [f, g]
        by_cases h : i.1 < n'
        · simp only [h, ↓reduceDIte, (π' ⟨i.1, h⟩).2]
          ext; simp
        · have hbnd := hrev_bound i.1 (by omega) i.2
          have hnot : ¬ place b (t + 1) - i.1 < n' := by omega
          simp only [h, hnot, ↓reduceDIte]
          ext; dsimp; omega
      have hgf : Function.RightInverse g f := by
        intro i
        dsimp only [f, g]
        by_cases h : i.1 < n'
        · simp only [h, ↓reduceDIte, (π'.symm ⟨i.1, h⟩).2]
          ext; simp
        · have hbnd := hrev_bound i.1 (by omega) i.2
          have hnot : ¬ place b (t + 1) - i.1 < n' := by omega
          simp only [h, hnot, ↓reduceDIte]
          ext; dsimp; omega
      let π : Equiv.Perm (Fin n) := ⟨f, g, hfg, hgf⟩
      refine ⟨π, ⟨?_, ?_⟩, ?_⟩
      · ext
        have hn'_gt0 : 0 < n' := hn'_pos
        simp only [π, Equiv.coe_fn_mk, f, hn'_gt0, ↓reduceDIte]
        exact congrArg Fin.val hπ'0
      · intro i hi
        simp only [π, Equiv.coe_fn_mk, f]
        by_cases h : i.1 < n'
        · simp only [h, ↓reduceDIte]
          obtain ⟨r, hrt, hr⟩ := hπ'pv ⟨i.1, h⟩ hi
          exact ⟨r, by omega, hr⟩
        · simp only [h, ↓reduceDIte]
          refine ⟨t + 1, by omega, ?_⟩
          omega
      · intro σ ⟨hσ0, hσpv⟩
        have hforce_r : ∀ x y r : ℕ, x < n → y < n → place b t ≤ x → 1 ≤ y →
            x + y = place b r → r = t + 1 := by
          intro x y r hx hy hxt hy1 hxy
          have hgt : place b t < place b r := by omega
          have hrt : t < r := by
            by_contra hle; push Not at hle
            have := place_mono b hb1 hle; omega
          have hlt2 : place b r < place b (t + 2) := by
            have h1 : x + y < 2 * place b (t + 1) := by omega
            have h2 : 2 * place b (t + 1) ≤ place b (t + 2) := by
              have hps : place b (t + 2) = place b (t + 1) * b (t + 1) := place_succ b (t + 1)
              have hm := Nat.mul_le_mul_left (place b (t + 1)) (hb (t + 1))
              linarith
            omega
          have hle1 : r ≤ t + 1 := by
            by_contra hge; push Not at hge
            have hge2 : t + 2 ≤ r := by omega
            have := place_mono b hb1 hge2
            omega
          omega
        have hσ_hi : ∀ i : Fin n, place b t ≤ i.1 → (σ i).1 = place b (t + 1) - i.1 := by
          intro i hi
          have hi_ne : i.1 ≠ 0 := by have := place_pos b hb0 t; omega
          have hσi_ne : (σ i).1 ≠ 0 := by
            intro h0
            have hEq : σ i = σ ⟨0, hn1⟩ := by
              rw [hσ0]; exact Fin.ext h0
            exact hi_ne (congrArg Fin.val (σ.injective hEq))
          obtain ⟨r, _, hr⟩ := hσpv i hi_ne
          have hr_eq := hforce_r i.1 (σ i).1 r i.2 (σ i).2 hi (by omega) hr
          subst hr_eq
          omega
        have hσ_img_hi : ∀ i : Fin n, place b t ≤ (σ i).1 → (σ i).1 = place b (t + 1) - i.1 := by
          intro i hσi
          have hi_ne : i.1 ≠ 0 := by
            intro h0
            have : i = ⟨0, hn1⟩ := Fin.ext h0
            rw [this, hσ0] at hσi
            have := place_pos b hb0 t; omega
          obtain ⟨r, _, hr⟩ := hσpv i hi_ne
          have hr_eq := hforce_r (σ i).1 i.1 r (σ i).2 i.2 hσi (by omega) (by omega)
          subst hr_eq
          omega
        have hσ_top : ∀ i : Fin n, n' ≤ i.1 → (σ i).1 = place b (t + 1) - i.1 := by
          intro i hi
          by_cases hbig : place b t ≤ i.1
          · exact hσ_hi i hbig
          · have hj_lt : place b (t + 1) - i.1 < n := (hrev_bound i.1 hi i.2).2
            have hj_ge : place b t ≤ place b (t + 1) - i.1 := by
              have hP2 : 2 * place b t ≤ place b (t + 1) := by
                rw [place_succ]
                have := Nat.mul_le_mul_left (place b t) (hb t)
                linarith
              omega
            let j : Fin n := ⟨place b (t + 1) - i.1, hj_lt⟩
            let i₀ : Fin n := σ.symm j
            have hσi₀ : (σ i₀).1 = place b (t + 1) - i₀.1 := by
              apply hσ_img_hi i₀
              simp only [i₀, Equiv.apply_symm_apply, j]
              exact hj_ge
            have hi₀_eq : i₀ = i := by
              ext
              have h1 : (σ i₀).1 = j.1 := by simp [i₀]
              rw [h1] at hσi₀
              dsimp [j] at hσi₀
              omega
            have : σ i = j := by rw [← hi₀_eq]; simp [i₀]
            rw [this]
        have hσ_lo : ∀ i : Fin n, i.1 < n' → (σ i).1 < n' := by
          intro i hi
          by_contra hge; push Not at hge
          have hj_bnd := hrev_bound (σ i).1 hge (σ i).2
          let j : Fin n := ⟨place b (t + 1) - (σ i).1, hj_bnd.2⟩
          have hσj : σ j = σ i := by
            ext
            rw [hσ_top j hj_bnd.1]
            dsimp [j]; omega
          have hji : j = i := σ.injective hσj
          have : n' ≤ i.1 := by rw [← hji]; exact hj_bnd.1
          omega
        have hσsymm_lo : ∀ i : Fin n, i.1 < n' → (σ.symm i).1 < n' := by
          intro i hi
          by_contra hge; push Not at hge
          have h1 := hσ_top (σ.symm i) hge
          rw [Equiv.apply_symm_apply] at h1
          have h2 := (hrev_bound (σ.symm i).1 hge (σ.symm i).2).1
          omega
        let σ' : Equiv.Perm (Fin n') :=
          { toFun := fun i => ⟨(σ ⟨i.1, lt_trans i.2 hn'_lt_n⟩).1,
              hσ_lo ⟨i.1, lt_trans i.2 hn'_lt_n⟩ i.2⟩
            invFun := fun i => ⟨(σ.symm ⟨i.1, lt_trans i.2 hn'_lt_n⟩).1,
              hσsymm_lo ⟨i.1, lt_trans i.2 hn'_lt_n⟩ i.2⟩
            left_inv := fun i => by ext; simp
            right_inv := fun i => by ext; simp }
        have hσ'_eq : σ' = π' := by
          apply hπ'uniq σ'
          refine ⟨?_, ?_⟩
          · ext
            change (σ ⟨0, hn1⟩).1 = 0
            exact congrArg Fin.val hσ0
          · intro i hi
            obtain ⟨r, _, hr⟩ := hσpv ⟨i.1, lt_trans i.2 hn'_lt_n⟩ hi
            have hP2 : 2 * place b t ≤ place b (t + 1) := by
              rw [place_succ]
              have := Nat.mul_le_mul_left (place b t) (hb t)
              linarith
            have hlt_Pt : i.1 + (σ' i).1 < place b (t + 1) := by
              have h1 : i.1 < n' := i.2
              have h2 : (σ' i).1 < n' := (σ' i).2
              omega
            have hrt : r ≤ t := by
              by_contra hgt; push Not at hgt
              have hge1 : t + 1 ≤ r := by omega
              have hle := place_mono b hb1 hge1
              dsimp only [σ', Equiv.coe_fn_mk] at hlt_Pt
              dsimp only at hr
              omega
            exact ⟨r, hrt, hr⟩
        ext i
        simp only [π, Equiv.coe_fn_mk, f]
        by_cases h : i.1 < n'
        · simp only [h, ↓reduceDIte, ← hσ'_eq]
          rfl
        · simp only [h, ↓reduceDIte]
          exact hσ_top i (by omega)

/-- The canonical unique place-value permutation `π*` for any Cantor index `n`. -/
noncomputable def cantorPerm (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r)
    (k n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ place b k)
    (hC : ∀ r < k, mdigit b (n - 1) r = 0 ∨ mdigit b (n - 1) r = b r - 1) :
    Equiv.Perm (Fin n) :=
  (existsUnique_placeValue_perm b hb n k hn1 hnk hC).choose

/-- Total weighted carry degree of a permutation `σ ∈ S_n` in mixed radix `b`. -/
def permWeightedCarry (b : ℕ → ℕ) (k n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, ∑ r ∈ Finset.range k, (b r - 1) * carryBit b i.1 (σ i).1 r

/-- Exact identity relating `permWeightedCarry` to the sum of `mdigitSum (i + σ i)`. -/
lemma two_mul_digitSum_eq (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r)
    (k n : ℕ) (hnk : n ≤ place b k) (σ : Equiv.Perm (Fin n)) :
    2 * (∑ i : Fin n, mdigitSum b k i.1) =
      (∑ i : Fin n, mdigitSum b (k + 1) (i.1 + (σ i).1)) + permWeightedCarry b k n σ := by
  have hb0 : ∀ s, 0 < b s := fun s => by have := hb s; omega
  have hreidx : ∑ i : Fin n, mdigitSum b k (σ i).1 = ∑ i : Fin n, mdigitSum b k i.1 :=
    Equiv.sum_comp σ (fun i : Fin n => mdigitSum b k i.1)
  have hpoint : ∀ i : Fin n,
      mdigitSum b k i.1 + mdigitSum b k (σ i).1 =
        mdigitSum b (k + 1) (i.1 + (σ i).1) +
          ∑ r ∈ Finset.range k, (b r - 1) * carryBit b i.1 (σ i).1 r := by
    intro i
    have h1 := digit_sum_add_carry_eq b hb0 k i.1 (σ i).1
      (lt_of_lt_of_le i.2 hnk) (lt_of_lt_of_le (σ i).2 hnk)
    have hdk : mdigit b (i.1 + (σ i).1) k = (i.1 + (σ i).1) / place b k := by
      unfold mdigit
      apply Nat.mod_eq_of_lt
      have hlt : i.1 + (σ i).1 < place b k * b k := by
        have hsum2 : i.1 + (σ i).1 < 2 * place b k := by omega
        have hmul := Nat.mul_le_mul_left (place b k) (hb k)
        linarith
      exact Nat.div_lt_of_lt_mul hlt
    have hsum : mdigitSum b (k + 1) (i.1 + (σ i).1) =
        mdigitSum b k (i.1 + (σ i).1) + (i.1 + (σ i).1) / place b k := by
      unfold mdigitSum; rw [Finset.sum_range_succ, hdk]
    omega
  have htot : ∑ i : Fin n, (mdigitSum b k i.1 + mdigitSum b k (σ i).1) =
      ∑ i : Fin n, (mdigitSum b (k + 1) (i.1 + (σ i).1) +
        ∑ r ∈ Finset.range k, (b r - 1) * carryBit b i.1 (σ i).1 r) :=
    Finset.sum_congr rfl (fun i _ => hpoint i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hreidx] at htot
  unfold permWeightedCarry
  omega

/-- Strict tropical maximality of `cantorPerm`: every `σ ≠ π*` has strictly smaller
    weighted carry total than `π*`. -/
lemma permWeightedCarry_lt_cantorPerm (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r)
    (k n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ place b k)
    (hC : ∀ r < k, mdigit b (n - 1) r = 0 ∨ mdigit b (n - 1) r = b r - 1)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ cantorPerm b hb k n hn1 hnk hC) :
    permWeightedCarry b k n σ < permWeightedCarry b k n (cantorPerm b hb k n hn1 hnk hC) := by
  have hspec := (existsUnique_placeValue_perm b hb n k hn1 hnk hC).choose_spec
  set π := cantorPerm b hb k n hn1 hnk hC
  have hπ0 : π ⟨0, hn1⟩ = ⟨0, hn1⟩ := hspec.1.1
  have hπpv : ∀ i : Fin n, i.1 ≠ 0 → ∃ r ≤ k, i.1 + (π i).1 = place b r := hspec.1.2
  have hP2k : 2 * place b k ≤ place b (k + 1) := by
    rw [place_succ]
    have := Nat.mul_le_mul_left (place b k) (hb k)
    linarith
  have hπ_sum : ∑ i : Fin n, mdigitSum b (k + 1) (i.1 + (π i).1) = n - 1 := by
    have hlt_ij : ∀ i : Fin n, i.1 + (π i).1 < place b (k + 1) := by
      intro i; omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn1⟩ : Fin n))]
    have h0 : mdigitSum b (k + 1) (0 + (π ⟨0, hn1⟩).1) = 0 := by
      rw [hπ0]; simp [mdigitSum, mdigit_zero]
    rw [h0, zero_add]
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn1⟩,
        mdigitSum b (k + 1) (i.1 + (π i).1) = 1 := by
      intro i hi
      have hne : i.1 ≠ 0 := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
      exact (mdigitSum_eq_one_iff b hb (hlt_ij i)).mpr (hπpv i hne)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_fin, smul_eq_mul, mul_one]
  have hσ_gt : n - 1 < ∑ i : Fin n, mdigitSum b (k + 1) (i.1 + (σ i).1) := by
    have hlt_ij : ∀ i : Fin n, i.1 + (σ i).1 < place b (k + 1) := by
      intro i; omega
    have hge1 : ∀ i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn1⟩,
        1 ≤ mdigitSum b (k + 1) (i.1 + (σ i).1) := by
      intro i hi
      have hne : i.1 ≠ 0 := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
      by_contra hlt; push Not at hlt
      have h0 : mdigitSum b (k + 1) (i.1 + (σ i).1) = 0 := by omega
      have := (mdigitSum_eq_zero_iff b (hlt_ij i)).mp h0
      omega
    have hge : n - 1 ≤ ∑ i : Fin n, mdigitSum b (k + 1) (i.1 + (σ i).1) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn1⟩ : Fin n))]
      have hsum_ge : n - 1 ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn1⟩,
          mdigitSum b (k + 1) (i.1 + (σ i).1) := by
        calc n - 1 = ∑ _i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn1⟩, 1 := by
              rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                Finset.card_fin, smul_eq_mul, mul_one]
          _ ≤ _ := Finset.sum_le_sum hge1
      omega
    by_contra hle; push Not at hle
    have heq : ∑ i : Fin n, mdigitSum b (k + 1) (i.1 + (σ i).1) = n - 1 := by omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn1⟩ : Fin n))] at heq
    have hsum_ge : n - 1 ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn1⟩,
        mdigitSum b (k + 1) (i.1 + (σ i).1) := by
      calc n - 1 = ∑ _i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn1⟩, 1 := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_fin, smul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum hge1
    have h0_eq : mdigitSum b (k + 1) (0 + (σ ⟨0, hn1⟩).1) = 0 := by
      change mdigitSum b (k + 1) (0 + (σ ⟨0, hn1⟩).1) + _ = n - 1 at heq
      omega
    have hσ0 : σ ⟨0, hn1⟩ = ⟨0, hn1⟩ := by
      have := (mdigitSum_eq_zero_iff b (hlt_ij ⟨0, hn1⟩)).mp h0_eq
      ext; omega
    have hrest_eq : ∑ i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn1⟩,
        mdigitSum b (k + 1) (i.1 + (σ i).1) = n - 1 := by omega
    have hσpv : ∀ i : Fin n, i.1 ≠ 0 → ∃ r ≤ k, i.1 + (σ i).1 = place b r := by
      intro i hi
      have hmem : i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn1⟩ :=
        Finset.mem_erase.mpr ⟨fun h => hi (congrArg Fin.val h), Finset.mem_univ _⟩
      have h1 : mdigitSum b (k + 1) (i.1 + (σ i).1) = 1 := by
        by_contra hne1
        have hgt1 : 2 ≤ mdigitSum b (k + 1) (i.1 + (σ i).1) := by
          have := hge1 i hmem; omega
        have hsplit := Finset.add_sum_erase _
          (fun j : Fin n => mdigitSum b (k + 1) (j.1 + (σ j).1)) hmem
        have hrem : (n - 1) - 1 ≤
            ∑ j ∈ ((Finset.univ : Finset (Fin n)).erase ⟨0, hn1⟩).erase i,
              mdigitSum b (k + 1) (j.1 + (σ j).1) := by
          calc (n - 1) - 1 =
                ∑ _j ∈ ((Finset.univ : Finset (Fin n)).erase ⟨0, hn1⟩).erase i, 1 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem hmem,
                  Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin, smul_eq_mul, mul_one]
            _ ≤ _ := Finset.sum_le_sum (fun j hj => hge1 j (Finset.mem_of_mem_erase hj))
        omega
      exact (mdigitSum_eq_one_iff b hb (hlt_ij i)).mp h1
    exact hσ (hspec.2 σ ⟨hσ0, hσpv⟩)
  have h1 := two_mul_digitSum_eq b hb k n hnk π
  have h2 := two_mul_digitSum_eq b hb k n hnk σ
  omega

/-- General tropical-uniqueness helper: if a determinant of monomials `X^{w(i,j)}` has a
    *unique* permutation `π*` maximizing `∑_i w(i, σ i)` with maximum `D`, then
    `coeff (det) D = sign π*` and `∀ d > D, coeff (det) d = 0`. -/
lemma det_monomial_coeff_of_unique_max {R : Type*} [CommRing R] {n : ℕ}
    (w : Fin n → Fin n → ℕ) (π : Equiv.Perm (Fin n))
    (hmax : ∀ σ : Equiv.Perm (Fin n), σ ≠ π → ∑ i, w i (σ i) < ∑ i, w i (π i)) :
    let M : Matrix (Fin n) (Fin n) (Polynomial R) :=
      Matrix.of fun i j => (Polynomial.X : Polynomial R) ^ w i j
    let D := ∑ i, w i (π i)
    M.det.coeff D = (Equiv.Perm.sign π : ℤ) ∧ ∀ d > D, M.det.coeff d = 0 := by
  intro M D
  have hdet : M.det = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : R) • (Polynomial.X : Polynomial R) ^ (∑ i, w i (σ i)) := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [M, Matrix.transpose_apply, Matrix.of_apply, Finset.prod_pow_eq_pow_sum]
    have hsmul : ∀ (u : ℤˣ) (p : Polynomial R), u • p = ((u : ℤ) : R) • p := by
      intro u p
      rcases Int.units_eq_one_or u with rfl | rfl <;> simp
    exact hsmul (Equiv.Perm.sign σ) _
  constructor
  · rw [hdet, Polynomial.finsetSum_coeff, Finset.sum_eq_single π]
    · simp [D]
    · intro σ _ hσ
      have hlt := hmax σ hσ
      simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul]
      rw [ite_eq_right_iff.mpr (fun h => by omega), mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro d hd
    rw [hdet, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro σ _
    have hle : ∑ i, w i (σ i) ≤ D := by
      by_cases hσ : σ = π
      · subst hσ; exact le_refl _
      · exact le_of_lt (hmax σ hσ)
    simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul]
    rw [ite_eq_right_iff.mpr (fun h => by omega), mul_zero]

/-- **Tropical Uniqueness & Exact Leading Term for Mixed-Radix Carry Matrices**:
    When every digit of `n - 1` lies in `{0, b r - 1}`, the polynomial determinant
    `det (mixedCarryPolyMatrix b k n)` over ANY nontrivial commutative ring `R` has
    exact degree `D = permWeightedCarry b k n π*` and leading coefficient
    `Equiv.Perm.sign π* ∈ {+1, -1}` (hence is nonzero in `R[X]`). -/
theorem mixedCarryPolyMatrix_det_leading {R : Type*} [CommRing R] [Nontrivial R]
    (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) (k n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ place b k)
    (hC : ∀ r < k, mdigit b (n - 1) r = 0 ∨ mdigit b (n - 1) r = b r - 1) :
    let π := cantorPerm b hb k n hn1 hnk hC
    let D := permWeightedCarry b k n π
    (mixedCarryPolyMatrix (R := R) b k n).det.natDegree = D ∧
    (mixedCarryPolyMatrix (R := R) b k n).det.leadingCoeff = ((Equiv.Perm.sign π : ℤ) : R) ∧
    (mixedCarryPolyMatrix (R := R) b k n).det ≠ 0 := by
  intro π D
  have hM : mixedCarryPolyMatrix (R := R) b k n =
      Matrix.of fun i j => (Polynomial.X : Polynomial R) ^
        (∑ r ∈ Finset.range k, (b r - 1) * carryBit b i.1 j.1 r) := by
    ext i j
    simp [mixedCarryPolyMatrix, carryMatrix, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  obtain ⟨hcoeff, hhi⟩ := det_monomial_coeff_of_unique_max (R := R)
    (fun i j => ∑ r ∈ Finset.range k, (b r - 1) * carryBit b i.1 j.1 r) π
    (fun σ hσ => permWeightedCarry_lt_cantorPerm b hb k n hn1 hnk hC σ hσ)
  rw [← hM] at hcoeff hhi
  change (mixedCarryPolyMatrix (R := R) b k n).det.coeff D = _ at hcoeff
  change ∀ d > D, (mixedCarryPolyMatrix (R := R) b k n).det.coeff d = 0 at hhi
  have hsign_ne : ((Equiv.Perm.sign π : ℤ) : R) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have hdeg : (mixedCarryPolyMatrix (R := R) b k n).det.natDegree = D := by
    apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      exact hhi
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [hcoeff]
      exact hsign_ne
  refine ⟨hdeg, ?_, ?_⟩
  · rw [Polynomial.leadingCoeff, hdeg, hcoeff]
  · intro h0
    have : ((Equiv.Perm.sign π : ℤ) : R) = 0 := by
      rw [← hcoeff, h0, Polynomial.coeff_zero]
    exact hsign_ne this

/-- **Theorem 1A (Mixed-Radix Cantor Non-Vanishing Characterization)**:
    Over any nontrivial commutative ring `R` and any mixed radix `b` (`∀ r, 2 ≤ b r`),
    `det (mixedCarryPolyMatrix b k n) ≠ 0` if and only if every mixed-radix digit of `n - 1`
    belongs to `{0, b r - 1}`. -/
theorem mixedCarryPolyMatrix_det_ne_zero_iff {R : Type*} [CommRing R] [Nontrivial R]
    (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) (k n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ place b k) :
    (mixedCarryPolyMatrix (R := R) b k n).det ≠ 0 ↔
      ∀ r < k, mdigit b (n - 1) r = 0 ∨ mdigit b (n - 1) r = b r - 1 := by
  constructor
  · intro hne r hr
    by_contra hnot
    push Not at hnot
    exact hne (carryMatrix_det_eq_zero_of_non_extremal b hb k n hn1 _ hr hnot.1 hnot.2)
  · intro hC
    exact (mixedCarryPolyMatrix_det_leading (R := R) b hb k n hn1 hnk hC).2.2

/-- **Theorem 1B (Uniform Base-`B` Cantor Non-Vanishing & Monic Leading Term Theorem)**:
    For every base `B ≥ 2`, every depth `k`, every `1 ≤ n ≤ B^k`, and every nontrivial
    commutative ring `R`, the polynomial carry determinant
    `det (X^{c_B(i, j)})_{0 ≤ i, j < n}` is nonzero in `R[X]` **if and only if**
    every base-`B` digit of `n - 1` lies in `{0, B - 1}` (the generalized Cantor set;
    for `B = 2` this holds for all `n ≥ 1`, and for `B = 3` precisely when `n - 1` is in
    the discrete ternary Cantor set). Moreover, when nonzero, it is monic up to sign
    `Equiv.Perm.sign π* ∈ {+1, -1}`. -/
theorem baseCarryPolyMatrix_det_leading {R : Type*} [CommRing R] [Nontrivial R]
    (B k n : ℕ) (hB : 2 ≤ B) (hn1 : 1 ≤ n) (hnk : n ≤ B ^ k)
    (hC : ∀ r < k, mdigit (fun _ => B) (n - 1) r = 0 ∨ mdigit (fun _ => B) (n - 1) r = B - 1) :
    let hb : ∀ _r : ℕ, 2 ≤ B := fun _ => hB
    let π := cantorPerm (fun _ => B) hb k n hn1 (by rwa [place_const]) hC
    let D := ∑ i : Fin n, carryCount (fun _ => B) k i.1 (π i).1
    (baseCarryPolyMatrix (R := R) B k n).det.natDegree = D ∧
    (baseCarryPolyMatrix (R := R) B k n).det.leadingCoeff = ((Equiv.Perm.sign π : ℤ) : R) ∧
    (baseCarryPolyMatrix (R := R) B k n).det ≠ 0 := by
  intro hb π D
  have hmax : ∀ σ : Equiv.Perm (Fin n), σ ≠ π →
      ∑ i : Fin n, carryCount (fun _ => B) k i.1 (σ i).1 < D := by
    intro σ hσ
    have hlt := permWeightedCarry_lt_cantorPerm (fun _ => B) hb k n hn1 (by rwa [place_const]) hC σ hσ
    have hmul : ∀ τ : Equiv.Perm (Fin n),
        permWeightedCarry (fun _ => B) k n τ =
          (B - 1) * ∑ i : Fin n, carryCount (fun _ => B) k i.1 (τ i).1 := by
      intro τ
      unfold permWeightedCarry carryCount
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    rw [hmul σ, hmul π] at hlt
    exact lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
  obtain ⟨hcoeff, hhi⟩ := det_monomial_coeff_of_unique_max (R := R)
    (fun i j => carryCount (fun _ => B) k i.1 j.1) π hmax
  change (baseCarryPolyMatrix (R := R) B k n).det.coeff D = _ at hcoeff
  change ∀ d > D, (baseCarryPolyMatrix (R := R) B k n).det.coeff d = 0 at hhi
  have hsign_ne : ((Equiv.Perm.sign π : ℤ) : R) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have hdeg : (baseCarryPolyMatrix (R := R) B k n).det.natDegree = D := by
    apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      exact hhi
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [hcoeff]
      exact hsign_ne
  refine ⟨hdeg, ?_, ?_⟩
  · rw [Polynomial.leadingCoeff, hdeg, hcoeff]
  · intro h0
    have : ((Equiv.Perm.sign π : ℤ) : R) = 0 := by
      rw [← hcoeff, h0, Polynomial.coeff_zero]
    exact hsign_ne this

theorem baseCarryPolyMatrix_det_ne_zero_iff {R : Type*} [CommRing R] [Nontrivial R]
    (B k n : ℕ) (hB : 2 ≤ B) (hn1 : 1 ≤ n) (hnk : n ≤ B ^ k) :
    (baseCarryPolyMatrix (R := R) B k n).det ≠ 0 ↔
      ∀ r < k, mdigit (fun _ => B) (n - 1) r = 0 ∨ mdigit (fun _ => B) (n - 1) r = B - 1 := by
  constructor
  · intro hne r hr
    by_contra hnot
    push Not at hnot
    rw [baseCarryPolyMatrix_eq_carryMatrix] at hne
    exact hne (carryMatrix_det_eq_zero_of_non_extremal (fun _ => B) (fun _ => hB) k n hn1 _ hr
      hnot.1 hnot.2)
  · intro hC
    exact (baseCarryPolyMatrix_det_leading (R := R) B k n hB hn1 hnk hC).2.2

/-- Immediate corollary for base 2: `det (X^{c_2(i,j)})_{0 ≤ i, j < n}` is NEVER zero in `R[X]`
    for ANY `n ≥ 1` and ANY nontrivial commutative ring `R` (including `ZMod ℓ` for every prime `ℓ`). -/
theorem binaryCarryPolyMatrix_det_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    (k n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ 2 ^ k) :
    (baseCarryPolyMatrix (R := R) 2 k n).det ≠ 0 := by
  rw [baseCarryPolyMatrix_det_ne_zero_iff (R := R) 2 k n (le_refl 2) hn1 hnk]
  intro r _
  have hlt : mdigit (fun _ => 2) (n - 1) r < 2 :=
    mdigit_lt (fun _ => 2) (fun _ => by omega) (n - 1) r
  omega

end NovelCarry
