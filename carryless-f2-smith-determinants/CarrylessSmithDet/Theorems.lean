import CarrylessSmithDet.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Tactic

namespace CarrylessSmithDet

open Matrix Polynomial BigOperators

/-! ## Section 1: Exact Isomorphism Between `(ℕ, ^^^, clmul)` and `(ZMod 2)[X]` -/

private theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem zmod2_isUnit_eq_one {u : Polynomial (ZMod 2)} (hu : IsUnit u) : u = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.isUnit_iff.mp hu
  rcases zmod2_eq_zero_or_one c with rfl | rfl
  · exact absurd hc.1 (by simp)
  · simpa using hc.2.symm

private theorem zmod2_associated_iff_eq {P Q : Polynomial (ZMod 2)} :
    Associated P Q ↔ P = Q := by
  constructor
  · rintro ⟨u, rfl⟩
    have hu : (u : Polynomial (ZMod 2)) = 1 := zmod2_isUnit_eq_one u.isUnit
    simp [hu]
  · rintro rfl; exact Associated.refl P

private theorem natToPoly_zero : natToPoly 0 = 0 := by
  unfold natToPoly; simp

private theorem natToPoly_eq_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    natToPoly n = Polynomial.C ((n % 2 : ℕ) : ZMod 2) + Polynomial.X * natToPoly (n / 2) := by
  conv => lhs; unfold natToPoly
  simp [hn]

private theorem natToPoly_one : natToPoly 1 = 1 := by
  rw [natToPoly_eq_of_ne_zero (by omega)]
  simp [natToPoly_zero]

private theorem natToPoly_coeff (n k : ℕ) :
    (natToPoly n).coeff k = if n.testBit k then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn; simp [natToPoly_zero]
  · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
    rw [natToPoly_eq_of_ne_zero hn]
    cases k with
    | zero =>
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero,
        add_zero, Nat.testBit_zero]
      have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h2 with h2 | h2 <;> simp [h2]
    | succ k =>
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_succ, zero_add,
        Polynomial.coeff_X_mul, Nat.testBit_succ]
      exact natToPoly_coeff (n / 2) k
termination_by n

private theorem natToPoly_xor (a b : ℕ) :
    natToPoly (a ^^^ b) = natToPoly a + natToPoly b := by
  ext k
  rw [Polynomial.coeff_add, natToPoly_coeff, natToPoly_coeff, natToPoly_coeff, Nat.testBit_xor]
  cases a.testBit k <;> cases b.testBit k <;> decide

private theorem natToPoly_shiftLeft_one (n : ℕ) :
    natToPoly (n <<< 1) = Polynomial.X * natToPoly n := by
  ext k
  rw [natToPoly_coeff, Nat.testBit_shiftLeft]
  cases k with
  | zero => simp
  | succ k =>
    simp only [Polynomial.coeff_X_mul, show 1 ≤ k + 1 by omega, decide_true, Bool.true_and,
      Nat.add_sub_cancel, natToPoly_coeff]

private theorem clmul_zero (b : ℕ) : clmul 0 b = 0 := by
  unfold clmul; simp

private theorem clmul_eq_of_ne_zero {a : ℕ} (ha : a ≠ 0) (b : ℕ) :
    clmul a b = (if a % 2 = 1 then b else 0) ^^^ (clmul (a / 2) b <<< 1) := by
  conv => lhs; unfold clmul
  simp [ha]

theorem natToPoly_clmul (a b : ℕ) :
    natToPoly (clmul a b) = natToPoly a * natToPoly b := by
  by_cases ha : a = 0
  · subst ha; simp [clmul_zero, natToPoly_zero]
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    rw [clmul_eq_of_ne_zero ha, natToPoly_xor, natToPoly_shiftLeft_one,
      natToPoly_clmul (a / 2) b, natToPoly_eq_of_ne_zero ha]
    have h2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases h2 with h2 | h2
    · simp [h2, natToPoly_zero, mul_assoc]
    · simp [h2, add_mul, mul_assoc]
termination_by a

private theorem testBit_sum_pow_two (S : Finset ℕ) (k : ℕ) :
    (∑ i ∈ S, 2 ^ i).testBit k = decide (k ∈ S) := by
  induction S using Finset.induction_on generalizing k with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hdisj : (2 ^ a &&& ∑ i ∈ s, 2 ^ i) = 0 := by
      apply Nat.eq_of_testBit_eq; intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit, ih j]
      by_cases hja : a = j
      · subst hja; simp [ha]
      · simp [hja]
    have hadd_xor : 2 ^ a + ∑ i ∈ s, 2 ^ i = 2 ^ a ^^^ ∑ i ∈ s, 2 ^ i := by
      have h1 : ∀ u v : ℕ, u + v = (u ^^^ v) + 2 * (u &&& v) := by
        intro u v
        have : u + v = (u ^^^ v) + 2 * (u &&& v) := by
          -- standard binary addition identity
          induction u using Nat.strongRecOn generalizing v with
          | ind u ihu =>
            by_cases hu0 : u = 0
            · subst hu0; simp
            · have hlt : u / 2 < u := Nat.div_lt_self (Nat.pos_of_ne_zero hu0) (by omega)
              have ih' := ihu (u / 2) hlt (v / 2)
              have hxd : (u ^^^ v) / 2 = u / 2 ^^^ v / 2 := by
                apply Nat.eq_of_testBit_eq; intro j
                rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]
              have had : (u &&& v) / 2 = u / 2 &&& v / 2 := by
                apply Nat.eq_of_testBit_eq; intro j
                rw [← Nat.testBit_succ, Nat.testBit_and, Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ]
              have hbit : u % 2 + v % 2 = (u ^^^ v) % 2 + 2 * ((u &&& v) % 2) := by
                have htb1 : (u ^^^ v).testBit 0 = (u.testBit 0 ^^ v.testBit 0) := Nat.testBit_xor u v 0
                have htb2 : (u &&& v).testBit 0 = (u.testBit 0 && v.testBit 0) := Nat.testBit_and u v 0
                simp only [Nat.testBit_zero] at htb1 htb2
                have hu2 : u % 2 = 0 ∨ u % 2 = 1 := by omega
                have hv2 : v % 2 = 0 ∨ v % 2 = 1 := by omega
                rcases hu2 with hu2 | hu2 <;> rcases hv2 with hv2 | hv2 <;>
                  (rw [hu2, hv2] at htb1 htb2;
                   by_cases hx : (u ^^^ v) % 2 = 1 <;> by_cases hn : (u &&& v) % 2 = 1 <;>
                    (simp [hx, hn] at htb1 htb2; try omega))
              have hdu := Nat.div_add_mod u 2
              have hdv := Nat.div_add_mod v 2
              have hdx := Nat.div_add_mod (u ^^^ v) 2
              have hdn := Nat.div_add_mod (u &&& v) 2
              rw [hxd] at hdx; rw [had] at hdn
              omega
        exact this
      have h := h1 (2 ^ a) (∑ i ∈ s, 2 ^ i)
      rw [hdisj] at h; omega
    rw [hadd_xor, Nat.testBit_xor, Nat.testBit_two_pow, ih k]
    by_cases hka : k = a
    · subst hka; simp [ha]
    · simp [hka, show a ≠ k by omega]

private theorem polyToNat_testBit (P : Polynomial (ZMod 2)) (k : ℕ) :
    (polyToNat P).testBit k = decide (P.coeff k ≠ 0) := by
  unfold polyToNat
  rw [testBit_sum_pow_two]
  simp [Polynomial.mem_support_iff]

theorem polyToNat_natToPoly (n : ℕ) :
    polyToNat (natToPoly n) = n := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [polyToNat_testBit, natToPoly_coeff]
  cases n.testBit k <;> simp

theorem natToPoly_polyToNat (P : Polynomial (ZMod 2)) :
    natToPoly (polyToNat P) = P := by
  ext k
  rw [natToPoly_coeff, polyToNat_testBit]
  rcases zmod2_eq_zero_or_one (P.coeff k) with h0 | h1
  · simp [h0]
  · simp [h1]

private theorem natToPoly_eq_zero_iff (n : ℕ) : natToPoly n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg polyToNat h
    rw [polyToNat_natToPoly] at this
    simpa [polyToNat] using this
  · rintro rfl; exact natToPoly_zero

private theorem natToPoly_natDegree (m : ℕ) (hm : 1 ≤ m) :
    (natToPoly m).natDegree = Nat.log 2 m := by
  have hm0 : m ≠ 0 := by omega
  have hle : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm0
  have hlt : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by omega) m
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [natToPoly_coeff]
    have hmk : m < 2 ^ k := lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))
    simp [Nat.testBit_lt_two_pow hmk]
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [natToPoly_coeff]
    have hbit : m.testBit (Nat.log 2 m) = true := by
      have hpos : 0 < 2 ^ Nat.log 2 m := Nat.two_pow_pos _
      have hdiv_ge : 1 ≤ m / 2 ^ Nat.log 2 m := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
      have hdiv_lt : m / 2 ^ Nat.log 2 m < 2 := Nat.div_lt_of_lt_mul (by rw [pow_succ] at hlt; exact hlt)
      have hdiv1 : m / 2 ^ Nat.log 2 m = 1 := by omega
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv1]; simp
    simp [hbit]

private theorem le_of_natToPoly_dvd {d m : ℕ} (hm : 1 ≤ m) (hdvd : natToPoly d ∣ natToPoly m) :
    1 ≤ d ∧ d ≤ m := by
  rcases hdvd with ⟨Q, hQ⟩
  have hm0 : natToPoly m ≠ 0 := fun h => by have := (natToPoly_eq_zero_iff m).mp h; omega
  have hd0 : natToPoly d ≠ 0 := by intro h; rw [h, zero_mul] at hQ; exact hm0 hQ
  have hQ0 : Q ≠ 0 := by intro h; rw [h, mul_zero] at hQ; exact hm0 hQ
  have hd1 : 1 ≤ d := by
    have : d ≠ 0 := fun h => hd0 ((natToPoly_eq_zero_iff d).mpr h)
    omega
  refine ⟨hd1, ?_⟩
  by_cases hdegQ : Q.natDegree = 0
  · have hQc : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdegQ
    have hQ1 : Q = 1 := by
      rcases zmod2_eq_zero_or_one (Q.coeff 0) with h0 | h1
      · rw [h0, map_zero] at hQc; exact absurd hQc hQ0
      · rw [h1, map_one] at hQc; exact hQc
    rw [hQ1, mul_one] at hQ
    have := congrArg polyToNat hQ
    rw [polyToNat_natToPoly, polyToNat_natToPoly] at this
    omega
  · have hdeg := congrArg Polynomial.natDegree hQ
    rw [Polynomial.natDegree_mul hd0 hQ0, natToPoly_natDegree m hm, natToPoly_natDegree d hd1] at hdeg
    have hd_lt : d < 2 ^ (Nat.log 2 d + 1) := Nat.lt_pow_succ_log_self (by omega) d
    have hpow : 2 ^ (Nat.log 2 d + 1) ≤ 2 ^ Nat.log 2 m :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hm_ge : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
    omega

private theorem mem_clDivisors_iff {d m : ℕ} (hm : 1 ≤ m) :
    d ∈ clDivisors m ↔ natToPoly d ∣ natToPoly m := by
  unfold clDivisors
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro hdvd
    have ⟨h1, h2⟩ := le_of_natToPoly_dvd hm hdvd
    exact ⟨⟨h1, h2⟩, hdvd⟩

private theorem clgcd_pos_right {a b : ℕ} (hb : 1 ≤ b) : 1 ≤ clgcd a b := by
  unfold clgcd
  have hb0 : natToPoly b ≠ 0 := fun h => by have := (natToPoly_eq_zero_iff b).mp h; omega
  have hg0 : EuclideanDomain.gcd (natToPoly a) (natToPoly b) ≠ 0 := by
    intro h
    have := EuclideanDomain.gcd_dvd_right (natToPoly a) (natToPoly b)
    rw [h] at this
    exact hb0 (zero_dvd_iff.mp this)
  by_contra hlt
  have hz : polyToNat (EuclideanDomain.gcd (natToPoly a) (natToPoly b)) = 0 := by omega
  have := congrArg natToPoly hz
  rw [natToPoly_polyToNat, natToPoly_zero] at this
  exact hg0 this

private theorem natToPoly_dvd_clgcd_iff (d a b : ℕ) :
    natToPoly d ∣ natToPoly (clgcd a b) ↔ natToPoly d ∣ natToPoly a ∧ natToPoly d ∣ natToPoly b := by
  unfold clgcd
  rw [natToPoly_polyToNat]
  exact ⟨fun h => ⟨h.trans (EuclideanDomain.gcd_dvd_left _ _),
      h.trans (EuclideanDomain.gcd_dvd_right _ _)⟩,
    fun ⟨h1, h2⟩ => EuclideanDomain.dvd_gcd h1 h2⟩

/-! ## Section 2: Universal Carry-Less Smith `LDL^T` Factorization -/

theorem det_clgcdMat_of_divisorSum {R : Type*} [CommRing R] (f g : ℕ → R)
    (hfg : ∀ m, 1 ≤ m → f m = ∑ d ∈ clDivisors m, g d) (n : ℕ) :
    (clgcdMat f n).det = ∏ k ∈ Finset.range n, g (k + 1) := by
  classical
  let Z : Matrix (Fin n) (Fin n) R :=
    Matrix.of fun i j => if natToPoly (j.val + 1) ∣ natToPoly (i.val + 1) then 1 else 0
  have htri : Z.BlockTriangular (fun i : Fin n => OrderDual.toDual i) := by
    intro i j hij
    have hlt : i.val < j.val := hij
    simp only [Z, Matrix.of_apply]
    have hndvd : ¬ (natToPoly (j.val + 1) ∣ natToPoly (i.val + 1)) := by
      intro hdvd
      have ⟨_, hle⟩ := le_of_natToPoly_dvd (by omega) hdvd
      omega
    simp [hndvd]
  have hdetZ : Z.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular Z htri]
    apply Finset.prod_eq_one
    intro i _
    simp [Z]
  have hfac : clgcdMat f n = Z * Matrix.diagonal (fun k : Fin n => g (k.val + 1)) * Zᵀ := by
    ext i j
    simp only [clgcdMat, Z, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
      Matrix.of_apply, mul_ite, mul_zero, ite_mul, zero_mul, one_mul, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hg_pos : 1 ≤ clgcd (i.val + 1) (j.val + 1) := clgcd_pos_right (by omega)
    rw [hfg _ hg_pos]
    have hle_n : ∀ d ∈ clDivisors (clgcd (i.val + 1) (j.val + 1)), d ≤ n := by
      intro d hd
      rw [mem_clDivisors_iff hg_pos, natToPoly_dvd_clgcd_iff] at hd
      have ⟨_, hle⟩ := le_of_natToPoly_dvd (by omega) hd.1
      omega
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      if natToPoly (k + 1) ∣ natToPoly (j.val + 1) then
        if natToPoly (k + 1) ∣ natToPoly (i.val + 1) then g (k + 1) else 0
      else 0) n]
    have hshift :
        ∑ k ∈ Finset.range n,
          (if natToPoly (k + 1) ∣ natToPoly (j.val + 1) then
            if natToPoly (k + 1) ∣ natToPoly (i.val + 1) then g (k + 1) else 0
          else 0) =
        ∑ d ∈ Finset.Icc 1 n,
          (if d ∈ clDivisors (clgcd (i.val + 1) (j.val + 1)) then g d else 0) := by
      refine Finset.sum_nbij (fun k => k + 1) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
      · intro a _ b _ h; dsimp only at h; omega
      · intro d hd
        simp only [Finset.mem_coe, Finset.mem_Icc] at hd
        exact ⟨d - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
      · intro k _
        simp only [mem_clDivisors_iff hg_pos, natToPoly_dvd_clgcd_iff]
        by_cases hi : natToPoly (k + 1) ∣ natToPoly (i.val + 1) <;>
          by_cases hj : natToPoly (k + 1) ∣ natToPoly (j.val + 1) <;>
          simp [hi, hj]
    rw [hshift, ← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hd
      have hle := hle_n d hd
      have h1 : 1 ≤ d := (le_of_natToPoly_dvd hg_pos ((mem_clDivisors_iff hg_pos).mp hd)).1
      exact ⟨⟨h1, hle⟩, hd⟩
    · exact fun h => h.2
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetZ, Matrix.det_diagonal,
    one_mul, mul_one, Fin.prod_univ_eq_prod_range (fun k => g (k + 1)) n]

private theorem sum_clMobiusInv {R : Type*} [CommRing R] (f : ℕ → R) (m : ℕ) (hm : 1 ≤ m) :
    ∑ d ∈ clDivisors m, clMobiusInv f d = f m := by
  classical
  have hm_mem : m ∈ clDivisors m := (mem_clDivisors_iff hm).mpr (dvd_refl _)
  rw [← Finset.add_sum_erase _ _ hm_mem]
  have hm0 : m ≠ 0 := by omega
  conv => lhs; arg 1; unfold clMobiusInv
  simp only [hm0, ↓reduceIte]
  have hcongr : ∑ d ∈ (clDivisors m).erase m, (if d < m then clMobiusInv f d else 0) =
      ∑ d ∈ (clDivisors m).erase m, clMobiusInv f d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hne : d ≠ m := (Finset.mem_erase.mp hd).1
    have hmem : d ∈ clDivisors m := (Finset.mem_erase.mp hd).2
    have hle : d ≤ m := (le_of_natToPoly_dvd hm ((mem_clDivisors_iff hm).mp hmem)).2
    simp [show d < m by omega]
  rw [hcongr]
  ring

theorem det_clgcdMat {R : Type*} [CommRing R] (f : ℕ → R) (n : ℕ) :
    (clgcdMat f n).det = ∏ k ∈ Finset.range n, clMobiusInv f (k + 1) :=
  det_clgcdMat_of_divisorSum f (clMobiusInv f) (fun m hm => (sum_clMobiusInv f m hm).symm) n

/-! ## Section 3: Carry-Less Euler Totient Divisor-Sum Law & `q = 2` Strict Positivity -/

private theorem clgcd_clmul_left (d a b : ℕ) :
    clgcd (clmul d a) (clmul d b) = clmul d (clgcd a b) := by
  unfold clgcd
  rw [natToPoly_clmul, natToPoly_clmul]
  have hassoc : Associated (EuclideanDomain.gcd (natToPoly d * natToPoly a) (natToPoly d * natToPoly b))
      (natToPoly d * EuclideanDomain.gcd (natToPoly a) (natToPoly b)) := by
    refine associated_of_dvd_dvd ?_ ?_
    · by_cases hd : natToPoly d = 0
      · simp [hd]
      · have hd1 : natToPoly d ∣ EuclideanDomain.gcd (natToPoly d * natToPoly a) (natToPoly d * natToPoly b) :=
          EuclideanDomain.dvd_gcd (dvd_mul_right _ _) (dvd_mul_right _ _)
        rcases hd1 with ⟨Q, hQ⟩
        rw [hQ]
        apply mul_dvd_mul_left
        apply EuclideanDomain.dvd_gcd
        · have := EuclideanDomain.gcd_dvd_left (natToPoly d * natToPoly a) (natToPoly d * natToPoly b)
          rw [hQ] at this
          exact (mul_dvd_mul_iff_left hd).mp this
        · have := EuclideanDomain.gcd_dvd_right (natToPoly d * natToPoly a) (natToPoly d * natToPoly b)
          rw [hQ] at this
          exact (mul_dvd_mul_iff_left hd).mp this
    · apply EuclideanDomain.dvd_gcd
      · exact mul_dvd_mul_left _ (EuclideanDomain.gcd_dvd_left _ _)
      · exact mul_dvd_mul_left _ (EuclideanDomain.gcd_dvd_right _ _)
  have heq := zmod2_associated_iff_eq.mp hassoc
  have hp : natToPoly (polyToNat (EuclideanDomain.gcd (natToPoly d * natToPoly a) (natToPoly d * natToPoly b))) =
      natToPoly (clmul d (polyToNat (EuclideanDomain.gcd (natToPoly a) (natToPoly b)))) := by
    rw [natToPoly_polyToNat, heq, natToPoly_clmul, natToPoly_polyToNat]
  have := congrArg polyToNat hp
  rwa [polyToNat_natToPoly, polyToNat_natToPoly] at this

private theorem lt_two_pow_iff_natDegree_lt (a d : ℕ) :
    a < 2 ^ d ↔ a = 0 ∨ (natToPoly a).natDegree < d := by
  constructor
  · intro ha
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · right
      rw [natToPoly_natDegree a (by omega)]
      exact (Nat.log_lt_iff_lt_pow (by omega) (by omega)).mpr ha
  · rintro (rfl | hdeg)
    · exact Nat.two_pow_pos d
    · by_cases ha0 : a = 0
      · subst ha0; exact Nat.two_pow_pos d
      · rw [natToPoly_natDegree a (by omega)] at hdeg
        exact (Nat.log_lt_iff_lt_pow (by omega) (by omega)).mp hdeg

private theorem clmul_one_right (a : ℕ) : clmul a 1 = a := by
  have h := natToPoly_clmul a 1
  rw [natToPoly_one, mul_one] at h
  have := congrArg polyToNat h
  rwa [polyToNat_natToPoly, polyToNat_natToPoly] at this

private theorem clmul_cancel_left {d a b : ℕ} (hd : 1 ≤ d) (h : clmul d a = clmul d b) :
    a = b := by
  have hp := congrArg natToPoly h
  rw [natToPoly_clmul, natToPoly_clmul] at hp
  have hd0 : natToPoly d ≠ 0 := fun hz => by have := (natToPoly_eq_zero_iff d).mp hz; omega
  have hab := mul_left_cancel₀ hd0 hp
  have := congrArg polyToNat hab
  rwa [polyToNat_natToPoly, polyToNat_natToPoly] at this

theorem sum_clTotient_divisors (m : ℕ) (hm : 1 ≤ m) :
    ∑ d ∈ clDivisors m, clTotient d = 2 ^ Nat.log 2 m := by
  classical
  let quotOf (d : ℕ) : ℕ := polyToNat (natToPoly m / natToPoly d)
  have hmul_quot : ∀ d ∈ clDivisors m, clmul d (quotOf d) = m := by
    intro d hd
    rw [mem_clDivisors_iff hm] at hd
    have hq : natToPoly d * (natToPoly m / natToPoly d) = natToPoly m :=
      EuclideanDomain.mul_div_cancel' (by
        intro h0; have ⟨h1, _⟩ := le_of_natToPoly_dvd hm hd
        have := (natToPoly_eq_zero_iff d).mp h0; omega) hd
    have h1 := congrArg polyToNat hq
    rw [← natToPoly_polyToNat (natToPoly m / natToPoly d), ← natToPoly_clmul,
      polyToNat_natToPoly, polyToNat_natToPoly] at h1
    exact h1
  have hquot_mem : ∀ d ∈ clDivisors m, quotOf d ∈ clDivisors m := by
    intro d hd
    rw [mem_clDivisors_iff hm]
    refine ⟨natToPoly d, ?_⟩
    rw [mul_comm, ← natToPoly_clmul, hmul_quot d hd]
  have hquot_invol : ∀ d ∈ clDivisors m, quotOf (quotOf d) = d := by
    intro d hd
    have hq_mem := hquot_mem d hd
    have hq_pos : 1 ≤ quotOf d := (le_of_natToPoly_dvd hm ((mem_clDivisors_iff hm).mp hq_mem)).1
    have h1 := hmul_quot (quotOf d) hq_mem
    have h2 : clmul (quotOf d) d = m := by
      have hp := congrArg natToPoly (hmul_quot d hd)
      rw [natToPoly_clmul, mul_comm, ← natToPoly_clmul] at hp
      have := congrArg polyToNat hp
      rwa [polyToNat_natToPoly, polyToNat_natToPoly] at this
    exact clmul_cancel_left hq_pos (h1.trans h2.symm)
  -- Partition `Finset.range (2 ^ Nat.log 2 m)` by `a ↦ clgcd a m ∈ clDivisors m`.
  have hpart : (Finset.range (2 ^ Nat.log 2 m)).card =
      ∑ d ∈ clDivisors m, ((Finset.range (2 ^ Nat.log 2 m)).filter (fun a => clgcd a m = d)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a => clgcd a m)]
    intro a _
    simp only [Finset.mem_coe]
    rw [mem_clDivisors_iff hm, clgcd, natToPoly_polyToNat]
    exact EuclideanDomain.gcd_dvd_right (natToPoly a) (natToPoly m)
  rw [Finset.card_range] at hpart
  have hfiber : ∀ d ∈ clDivisors m,
      ((Finset.range (2 ^ Nat.log 2 m)).filter (fun a => clgcd a m = d)).card =
        clTotient (quotOf d) := by
    intro d hd
    unfold clTotient
    have hd_pos : 1 ≤ d := (le_of_natToPoly_dvd hm ((mem_clDivisors_iff hm).mp hd)).1
    have he_pos : 1 ≤ quotOf d := (le_of_natToPoly_dvd hm ((mem_clDivisors_iff hm).mp (hquot_mem d hd))).1
    have hdeg_add : Nat.log 2 d + Nat.log 2 (quotOf d) = Nat.log 2 m := by
      have hp := congrArg (fun x => (natToPoly x).natDegree) (hmul_quot d hd)
      rw [natToPoly_clmul, Polynomial.natDegree_mul
        (fun h => by have := (natToPoly_eq_zero_iff d).mp h; omega)
        (fun h => by have := (natToPoly_eq_zero_iff (quotOf d)).mp h; omega),
        natToPoly_natDegree d hd_pos, natToPoly_natDegree (quotOf d) he_pos,
        natToPoly_natDegree m hm] at hp
      exact hp
    refine (Finset.card_bij (fun b _ => clmul d b) ?_ ?_ ?_).symm
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
      refine ⟨?_, ?_⟩
      · rw [lt_two_pow_iff_natDegree_lt] at hb ⊢
        rcases hb.1 with rfl | hdegb
        · left; exact clmul_zero_right d
        · by_cases hb0 : b = 0
          · left; rw [hb0]; exact clmul_zero_right d
          · right
            rw [natToPoly_clmul, Polynomial.natDegree_mul
              (fun h => by have := (natToPoly_eq_zero_iff d).mp h; omega)
              (fun h => by have := (natToPoly_eq_zero_iff b).mp h; omega),
              natToPoly_natDegree d hd_pos]
            omega
      · rw [← hmul_quot d hd, clgcd_clmul_left, hb.2, clmul_one_right]
    · intro b1 _ b2 _ h; exact clmul_cancel_left hd_pos h
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      have hd_dvd_a : natToPoly d ∣ natToPoly a := by
        have := (natToPoly_dvd_clgcd_iff d a m).mp (by rw [ha.2])
        exact this.1
      rcases hd_dvd_a with ⟨Q, hQ⟩
      let b := polyToNat Q
      have hmul_ab : clmul d b = a := by
        have h1 : natToPoly (clmul d b) = natToPoly a := by
          rw [natToPoly_clmul, natToPoly_polyToNat, ← hQ]
        have := congrArg polyToNat h1
        rwa [polyToNat_natToPoly, polyToNat_natToPoly] at this
      refine ⟨b, ?_, hmul_ab⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ?_⟩
      · rw [lt_two_pow_iff_natDegree_lt]
        by_cases hb0 : b = 0
        · exact Or.inl hb0
        · right
          have ha_lt := (lt_two_pow_iff_natDegree_lt a (Nat.log 2 m)).mp ha.1
          have ha0 : a ≠ 0 := by
            intro h0; rw [h0] at hmul_ab
            have hp := congrArg natToPoly hmul_ab
            rw [natToPoly_clmul, natToPoly_zero, mul_eq_zero] at hp
            rcases hp with hd0 | hb0'
            · exact absurd ((natToPoly_eq_zero_iff d).mp hd0) (by omega)
            · exact hb0 ((natToPoly_eq_zero_iff b).mp hb0')
          have hdega : (natToPoly a).natDegree < Nat.log 2 m := ha_lt.resolve_left ha0
          rw [← hmul_ab, natToPoly_clmul, Polynomial.natDegree_mul
            (fun h => by have := (natToPoly_eq_zero_iff d).mp h; omega)
            (fun h => by have := (natToPoly_eq_zero_iff b).mp h; omega),
            natToPoly_natDegree d hd_pos] at hdega
          omega
      · have h1 : clmul d (clgcd b (quotOf d)) = clmul d 1 := by
          rw [← clgcd_clmul_left, hmul_ab, hmul_quot d hd, ha.2, clmul_one_right]
        exact clmul_cancel_left hd_pos h1
  -- Reindex `∑ d ∈ clDivisors m, clTotient (quotOf d)` via involution `quotOf`.
  have hsum_invol : ∑ d ∈ clDivisors m, clTotient (quotOf d) = ∑ d ∈ clDivisors m, clTotient d := by
    refine Finset.sum_nbij quotOf ?_ ?_ ?_ (fun _ _ => rfl)
    · exact hquot_mem
    · intro d1 hd1 d2 hd2 h
      have := congrArg quotOf h
      rwa [hquot_invol d1 hd1, hquot_invol d2 hd2] at this
    · intro d hd
      exact ⟨quotOf d, hquot_mem d hd, hquot_invol d hd⟩
  rw [hpart, ← hsum_invol]
  exact (Finset.sum_congr rfl hfiber).symm
where
  clmul_zero_right (a : ℕ) : clmul a 0 = 0 := by
    have h := natToPoly_clmul a 0
    rw [natToPoly_zero, mul_zero] at h
    exact (natToPoly_eq_zero_iff _).mp h

private theorem clTotient_pos (m : ℕ) (hm : 1 ≤ m) : 1 ≤ clTotient m := by
  unfold clTotient
  apply Finset.card_pos.mpr
  by_cases hm1 : m = 1
  · subst hm1
    refine ⟨0, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range, Nat.log_one_right, pow_zero]
    refine ⟨by omega, ?_⟩
    unfold clgcd
    rw [natToPoly_zero, natToPoly_one]
    have h1 : EuclideanDomain.gcd (0 : Polynomial (ZMod 2)) 1 = 1 :=
      zmod2_associated_iff_eq.mp (by
        refine associated_of_dvd_dvd ?_ (one_dvd _)
        exact EuclideanDomain.gcd_dvd_right 0 1)
    rw [h1]
    simpa [natToPoly_one] using polyToNat_natToPoly 1
  · refine ⟨1, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    have hlog_pos : 1 ≤ Nat.log 2 m := by
      have h1 := Nat.log_mono_right (b := 2) (by omega : 2 ≤ m)
      have hlog2 : Nat.log 2 2 = 1 := by decide
      omega
    have hpow : 2 ≤ 2 ^ Nat.log 2 m := by
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hlog_pos; omega
    refine ⟨by omega, ?_⟩
    unfold clgcd
    rw [natToPoly_one]
    have h1 : EuclideanDomain.gcd (1 : Polynomial (ZMod 2)) (natToPoly m) = 1 :=
      zmod2_associated_iff_eq.mp (by
        refine associated_of_dvd_dvd ?_ (one_dvd _)
        exact EuclideanDomain.gcd_dvd_left 1 (natToPoly m))
    rw [h1]
    simpa [natToPoly_one] using polyToNat_natToPoly 1

theorem det_clgcd_pow2_deg (n : ℕ) :
    (clgcdMat (fun d => (2 : ℤ) ^ Nat.log 2 d) n).det =
      ∏ k ∈ Finset.range n, (clTotient (k + 1) : ℤ) ∧
    0 < (clgcdMat (fun d => (2 : ℤ) ^ Nat.log 2 d) n).det := by
  have hdet : (clgcdMat (fun d => (2 : ℤ) ^ Nat.log 2 d) n).det =
      ∏ k ∈ Finset.range n, (clTotient (k + 1) : ℤ) :=
    det_clgcdMat_of_divisorSum
      (fun d => (2 : ℤ) ^ Nat.log 2 d)
      (fun d => (clTotient d : ℤ))
      (fun m hm => by exact_mod_cast (sum_clTotient_divisors m hm).symm) n
  refine ⟨hdet, ?_⟩
  rw [hdet]
  apply Finset.prod_pos
  intro k _
  have hpos := clTotient_pos (k + 1) (by omega)
  omega

/-! ## Section 4: Finite Carry-Less Divisors `1..9` & The Three Collapse Paradoxes -/

private theorem clDvd_iff_exists_le {d m : ℕ} (hm : 1 ≤ m) :
    natToPoly d ∣ natToPoly m ↔ ∃ e ≤ m, clmul d e = m := by
  constructor
  · rintro ⟨Q, hQ⟩
    let e := polyToNat Q
    have hmul : clmul d e = m := by
      have hp : natToPoly (clmul d e) = natToPoly m := by
        rw [natToPoly_clmul, natToPoly_polyToNat, ← hQ]
      have := congrArg polyToNat hp
      rwa [polyToNat_natToPoly, polyToNat_natToPoly] at this
    have he_dvd : natToPoly e ∣ natToPoly m := ⟨natToPoly d, by rw [mul_comm, ← natToPoly_clmul, hmul]⟩
    have ⟨_, hle⟩ := le_of_natToPoly_dvd hm he_dvd
    exact ⟨e, hle, hmul⟩
  · rintro ⟨e, _, hmul⟩
    exact ⟨natToPoly e, by rw [← natToPoly_clmul, hmul]⟩

private def clmulAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, a, b =>
    if a = 0 then 0
    else (if a % 2 = 1 then b else 0) ^^^ (clmulAux fuel (a / 2) b <<< 1)

private theorem clmul_eq_aux (fuel a b : ℕ) (hf : a ≤ fuel) :
    clmul a b = clmulAux fuel a b := by
  induction fuel generalizing a with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; simp [clmul_zero, clmulAux]
  | succ fuel ih =>
    by_cases ha : a = 0
    · subst ha; simp [clmul_zero, clmulAux]
    · rw [clmul_eq_of_ne_zero ha, clmulAux]
      simp only [ha, ↓reduceIte]
      rw [ih (a / 2) (by omega)]

private def isClDivBool (d m : ℕ) : Bool :=
  (List.range (m + 1)).any (fun e => clmulAux d d e == m)

private theorem mem_clDivisors_iff_bool {d m : ℕ} (hm : 1 ≤ m) :
    d ∈ clDivisors m ↔ 1 ≤ d ∧ d ≤ m ∧ isClDivBool d m = true := by
  rw [mem_clDivisors_iff hm, clDvd_iff_exists_le hm]
  constructor
  · rintro ⟨e, hle, hmul⟩
    have hle_d := le_of_natToPoly_dvd (d := d) hm ⟨natToPoly e, by rw [← natToPoly_clmul, hmul]⟩
    refine ⟨hle_d.1, hle_d.2, ?_⟩
    unfold isClDivBool
    rw [List.any_eq_true]
    exact ⟨e, List.mem_range.mpr (by omega), by rw [← clmul_eq_aux d d e (le_refl _), hmul]; simp⟩
  · rintro ⟨_, _, hbool⟩
    unfold isClDivBool at hbool
    rw [List.any_eq_true] at hbool
    rcases hbool with ⟨e, he, heq⟩
    have hmul : clmul d e = m := by
      rw [clmul_eq_aux d d e (le_refl _)]
      exact eq_of_beq heq
    exact ⟨e, by have := List.mem_range.mp he; omega, hmul⟩

private theorem clDivisors_eq_of_list (m : ℕ) (hm : 1 ≤ m) (L : Finset ℕ)
    (hL : ∀ d, d ∈ L ↔ 1 ≤ d ∧ d ≤ m ∧ isClDivBool d m = true) :
    clDivisors m = L := by
  ext d
  rw [mem_clDivisors_iff_bool hm, hL d]

private theorem clDivisors_1 : clDivisors 1 = {1} := by
  apply clDivisors_eq_of_list 1 (by omega)
  intro d; by_cases hd : d ≤ 1
  · interval_cases d <;> decide
  · simp [show d ≠ 1 by omega, hd]

private theorem clDivisors_2 : clDivisors 2 = {1, 2} := by
  apply clDivisors_eq_of_list 2 (by omega)
  intro d; by_cases hd : d ≤ 2
  · interval_cases d <;> decide
  · simp [show d ≠ 1 by omega, show d ≠ 2 by omega, hd]

private theorem clDivisors_3 : clDivisors 3 = {1, 3} := by
  apply clDivisors_eq_of_list 3 (by omega)
  intro d; by_cases hd : d ≤ 3
  · interval_cases d <;> decide
  · simp [show d ≠ 1 by omega, show d ≠ 3 by omega, hd]

private theorem clDivisors_4 : clDivisors 4 = {1, 2, 4} := by
  apply clDivisors_eq_of_list 4 (by omega)
  intro d; by_cases hd : d ≤ 4
  · interval_cases d <;> decide
  · simp [show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 4 by omega, hd]

private theorem clDivisors_5 : clDivisors 5 = {1, 3, 5} := by
  apply clDivisors_eq_of_list 5 (by omega)
  intro d; by_cases hd : d ≤ 5
  · interval_cases d <;> decide
  · simp [show d ≠ 1 by omega, show d ≠ 3 by omega, show d ≠ 5 by omega, hd]

private theorem clDivisors_6 : clDivisors 6 = {1, 2, 3, 6} := by
  apply clDivisors_eq_of_list 6 (by omega)
  intro d; by_cases hd : d ≤ 6
  · interval_cases d <;> decide
  · simp [show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 3 by omega, show d ≠ 6 by omega, hd]

private theorem clDivisors_7 : clDivisors 7 = {1, 7} := by
  apply clDivisors_eq_of_list 7 (by omega)
  intro d; by_cases hd : d ≤ 7
  · interval_cases d <;> decide
  · simp [show d ≠ 1 by omega, show d ≠ 7 by omega, hd]

private theorem clDivisors_8 : clDivisors 8 = {1, 2, 4, 8} := by
  apply clDivisors_eq_of_list 8 (by omega)
  intro d; by_cases hd : d ≤ 8
  · interval_cases d <;> decide
  · simp [show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 4 by omega, show d ≠ 8 by omega, hd]

private theorem clDivisors_9 : clDivisors 9 = {1, 3, 7, 9} := by
  apply clDivisors_eq_of_list 9 (by omega)
  intro d; by_cases hd : d ≤ 9
  · interval_cases d <;> decide
  · simp [show d ≠ 1 by omega, show d ≠ 3 by omega, show d ≠ 7 by omega, show d ≠ 9 by omega, hd]

private theorem clMobiusInv_eq_sub {R : Type*} [CommRing R] (f : ℕ → R) (m : ℕ) (hm : 1 ≤ m) :
    clMobiusInv f m = f m - ∑ d ∈ (clDivisors m).erase m, clMobiusInv f d := by
  have hm0 : m ≠ 0 := by omega
  conv => lhs; unfold clMobiusInv
  simp only [hm0, ↓reduceIte]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hne : d ≠ m := (Finset.mem_erase.mp hd).1
  have hmem : d ∈ clDivisors m := (Finset.mem_erase.mp hd).2
  have hle : d ≤ m := (le_of_natToPoly_dvd hm ((mem_clDivisors_iff hm).mp hmem)).2
  simp [show d < m by omega]

private theorem clMobiusInv_id_vals {S : Type*} [CommRing S] :
    clMobiusInv (fun d => (d : S)) 1 = 1 ∧
    clMobiusInv (fun d => (d : S)) 2 = 1 ∧
    clMobiusInv (fun d => (d : S)) 3 = 2 ∧
    clMobiusInv (fun d => (d : S)) 4 = 2 ∧
    clMobiusInv (fun d => (d : S)) 5 = 2 ∧
    clMobiusInv (fun d => (d : S)) 6 = 2 ∧
    clMobiusInv (fun d => (d : S)) 7 = 6 ∧
    clMobiusInv (fun d => (d : S)) 8 = 4 ∧
    clMobiusInv (fun d => (d : S)) 9 = 0 := by
  have g1 : clMobiusInv (fun d => (d : S)) 1 = 1 := by
    rw [clMobiusInv_eq_sub _ 1 (by omega), clDivisors_1]; simp
  have g2 : clMobiusInv (fun d => (d : S)) 2 = 1 := by
    rw [clMobiusInv_eq_sub _ 2 (by omega), clDivisors_2]; simp [g1]; ring
  have g3 : clMobiusInv (fun d => (d : S)) 3 = 2 := by
    rw [clMobiusInv_eq_sub _ 3 (by omega), clDivisors_3]; simp [g1]; ring
  have g4 : clMobiusInv (fun d => (d : S)) 4 = 2 := by
    rw [clMobiusInv_eq_sub _ 4 (by omega), clDivisors_4]; simp [g1, g2]; ring
  have g5 : clMobiusInv (fun d => (d : S)) 5 = 2 := by
    rw [clMobiusInv_eq_sub _ 5 (by omega), clDivisors_5]; simp [g1, g3]; ring
  have g6 : clMobiusInv (fun d => (d : S)) 6 = 2 := by
    rw [clMobiusInv_eq_sub _ 6 (by omega), clDivisors_6]; simp [g1, g2, g3]; ring
  have g7 : clMobiusInv (fun d => (d : S)) 7 = 6 := by
    rw [clMobiusInv_eq_sub _ 7 (by omega), clDivisors_7]; simp [g1]; ring
  have g8 : clMobiusInv (fun d => (d : S)) 8 = 4 := by
    rw [clMobiusInv_eq_sub _ 8 (by omega), clDivisors_8]; simp [g1, g2, g4]; ring
  have g9 : clMobiusInv (fun d => (d : S)) 9 = 0 := by
    rw [clMobiusInv_eq_sub _ 9 (by omega), clDivisors_9]; simp [g1, g3, g7]; ring
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩

theorem det_clgcd_id_collapse_nine {R : Type*} [CommRing R] :
    (∀ n, 9 ≤ n → (clgcdMat (fun d => (d : R)) n).det = 0) ∧
    (clgcdMat (fun d => (d : ℤ)) 8).det = 384 := by
  constructor
  · intro n hn
    rw [det_clgcdMat]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : 8 < n))
      (clMobiusInv_id_vals (S := R)).2.2.2.2.2.2.2.2
  · rw [det_clgcdMat]
    rcases clMobiusInv_id_vals (S := ℤ) with ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, g1, g2, g3, g4, g5, g6, g7, g8]
    norm_num

private theorem clMobiusInv_coprime_vals {S : Type*} [CommRing S] :
    clMobiusInv (fun d => if d = 1 then (1 : S) else 0) 1 = 1 ∧
    clMobiusInv (fun d => if d = 1 then (1 : S) else 0) 2 = -1 ∧
    clMobiusInv (fun d => if d = 1 then (1 : S) else 0) 3 = -1 ∧
    clMobiusInv (fun d => if d = 1 then (1 : S) else 0) 4 = 0 := by
  have g1 : clMobiusInv (fun d => if d = 1 then (1 : S) else 0) 1 = 1 := by
    rw [clMobiusInv_eq_sub _ 1 (by omega), clDivisors_1]; simp
  have g2 : clMobiusInv (fun d => if d = 1 then (1 : S) else 0) 2 = -1 := by
    rw [clMobiusInv_eq_sub _ 2 (by omega), clDivisors_2]; simp [g1]
  have g3 : clMobiusInv (fun d => if d = 1 then (1 : S) else 0) 3 = -1 := by
    rw [clMobiusInv_eq_sub _ 3 (by omega), clDivisors_3]; simp [g1]
  have g4 : clMobiusInv (fun d => if d = 1 then (1 : S) else 0) 4 = 0 := by
    rw [clMobiusInv_eq_sub _ 4 (by omega), clDivisors_4]; simp [g1, g2]
  exact ⟨g1, g2, g3, g4⟩

theorem det_clgcd_coprime_collapse_four {R : Type*} [CommRing R] :
    (∀ n, 4 ≤ n → (clgcdMat (fun d => if d = 1 then (1 : R) else 0) n).det = 0) ∧
    (clgcdMat (fun d => if d = 1 then (1 : ℤ) else 0) 3).det = 1 := by
  constructor
  · intro n hn
    rw [det_clgcdMat]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : 3 < n))
      (clMobiusInv_coprime_vals (S := R)).2.2.2
  · rw [det_clgcdMat]
    rcases clMobiusInv_coprime_vals (S := ℤ) with ⟨g1, g2, g3, _⟩
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, g1, g2, g3]
    norm_num

private theorem clMobiusInv_popcount_vals {S : Type*} [CommRing S] :
    clMobiusInv (fun d => (popcount d : S)) 1 = 1 ∧
    clMobiusInv (fun d => (popcount d : S)) 2 = 0 := by
  have hp0 : popcount 0 = 0 := by unfold popcount; simp
  have hp1 : popcount 1 = 1 := by conv => lhs; unfold popcount; simp [hp0]
  have hp2 : popcount 2 = 1 := by conv => lhs; unfold popcount; simp [hp1]
  have g1 : clMobiusInv (fun d => (popcount d : S)) 1 = 1 := by
    rw [clMobiusInv_eq_sub _ 1 (by omega), clDivisors_1]; simp [hp1]
  have g2 : clMobiusInv (fun d => (popcount d : S)) 2 = 0 := by
    rw [clMobiusInv_eq_sub _ 2 (by omega), clDivisors_2]; simp [g1, hp2]
  exact ⟨g1, g2⟩

theorem det_clgcd_popcount_collapse_two {R : Type*} [CommRing R] :
    (∀ n, 2 ≤ n → (clgcdMat (fun d => (popcount d : R)) n).det = 0) ∧
    (clgcdMat (fun d => (popcount d : ℤ)) 1).det = 1 := by
  constructor
  · intro n hn
    rw [det_clgcdMat]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : 1 < n))
      (clMobiusInv_popcount_vals (S := R)).2
  · rw [det_clgcdMat]
    rcases clMobiusInv_popcount_vals (S := ℤ) with ⟨g1, _⟩
    simp [g1]

end CarrylessSmithDet
