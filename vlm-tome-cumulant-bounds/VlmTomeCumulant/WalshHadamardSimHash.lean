/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VlmTomeCumulant.RatOrder

/-!
# Pillar 2: Orthogonal Walsh-Hadamard Transform (`H_{2^k}`), Outlier Flattening, and 1-Bit SimHash Ties

Proves Theorem 4 (`bipartite_wht_int4_outlier_rescue_vs_binary_walsh_tie`) purely over `Init`.
-/

namespace VlmTomeCumulant

theorem pow2_succ_eq_add (k : Nat) : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  rw [Nat.pow_succ]; omega

theorem fin_pow2_left {k : Nat} (i : Fin (2 ^ k)) : i.val < 2 ^ (k + 1) := by
  have hp := pow2_succ_eq_add k
  have hi := i.isLt
  omega

theorem fin_pow2_right {k : Nat} (i : Fin (2 ^ k)) : i.val + 2 ^ k < 2 ^ (k + 1) := by
  have hp := pow2_succ_eq_add k
  have hi := i.isLt
  omega

theorem fin_pow2_sub {k : Nat} (i : Fin (2 ^ (k + 1))) (h : ¬ i.val < 2 ^ k) :
    i.val - 2 ^ k < 2 ^ k := by
  have hp := pow2_succ_eq_add k
  have hi := i.isLt
  omega

theorem wht_succ_left (k : Nat) (v : Fin (2 ^ (k + 1)) → Int) (i : Fin (2 ^ k)) :
    wht (k + 1) v ⟨i.val, fin_pow2_left i⟩ =
      wht k (fun t : Fin (2 ^ k) => v ⟨t.val, fin_pow2_left t⟩) i +
      wht k (fun t : Fin (2 ^ k) => v ⟨t.val + 2 ^ k, fin_pow2_right t⟩) i := by
  simp only [wht, i.isLt, dite_true]

theorem wht_succ_right (k : Nat) (v : Fin (2 ^ (k + 1)) → Int) (i : Fin (2 ^ k)) :
    wht (k + 1) v ⟨i.val + 2 ^ k, fin_pow2_right i⟩ =
      wht k (fun t : Fin (2 ^ k) => v ⟨t.val, fin_pow2_left t⟩) i -
      wht k (fun t : Fin (2 ^ k) => v ⟨t.val + 2 ^ k, fin_pow2_right t⟩) i := by
  have hnot : ¬ (i.val + 2 ^ k < 2 ^ k) := by omega
  have hsub : (⟨i.val + 2 ^ k - 2 ^ k, by omega⟩ : Fin (2 ^ k)) = i := by
    apply Fin.ext; simp
  change (if h : i.val + 2 ^ k < 2 ^ k then _ else
      wht k (fun t => v ⟨t.val, _⟩) ⟨i.val + 2 ^ k - 2 ^ k, _⟩ -
      wht k (fun t => v ⟨t.val + 2 ^ k, _⟩) ⟨i.val + 2 ^ k - 2 ^ k, _⟩) = _
  simp only [hnot, dite_false]
  rw [hsub]

theorem finSumInt_pow2_split {k : Nat} (f : Fin (2 ^ (k + 1)) → Int) :
    finSumInt f =
      finSumInt (fun i : Fin (2 ^ k) => f ⟨i.val, fin_pow2_left i⟩) +
      finSumInt (fun j : Fin (2 ^ k) => f ⟨j.val + 2 ^ k, fin_pow2_right j⟩) := by
  have hcast : ∀ (n m : Nat) (h : n = m) (g : Fin n → Int),
      finSumInt g = finSumInt (fun i : Fin m => g ⟨i.val, h ▸ i.isLt⟩) := by
    intro n m h g; subst h; rfl
  rw [hcast (2 ^ (k + 1)) (2 ^ k + 2 ^ k) (pow2_succ_eq_add k) f]
  rw [finSumInt_split]
  congr 1
  apply finSumInt_congr
  intro j
  have heq : (⟨2 ^ k + j.val, by have hp := pow2_succ_eq_add k; have hj := j.isLt; omega⟩ : Fin (2 ^ (k + 1))) =
      ⟨j.val + 2 ^ k, fin_pow2_right j⟩ := by
    apply Fin.ext; dsimp; omega
  exact congrArg f heq

theorem finSumNat_pow2_split {k : Nat} (f : Fin (2 ^ (k + 1)) → Nat) :
    finSumNat f =
      finSumNat (fun i : Fin (2 ^ k) => f ⟨i.val, fin_pow2_left i⟩) +
      finSumNat (fun j : Fin (2 ^ k) => f ⟨j.val + 2 ^ k, fin_pow2_right j⟩) := by
  have hcast : ∀ (n m : Nat) (h : n = m) (g : Fin n → Nat),
      finSumNat g = finSumNat (fun i : Fin m => g ⟨i.val, h ▸ i.isLt⟩) := by
    intro n m h g; subst h; rfl
  rw [hcast (2 ^ (k + 1)) (2 ^ k + 2 ^ k) (pow2_succ_eq_add k) f]
  rw [finSumNat_split]
  congr 1
  apply finSumNat_congr
  intro j
  have heq : (⟨2 ^ k + j.val, by have hp := pow2_succ_eq_add k; have hj := j.isLt; omega⟩ : Fin (2 ^ (k + 1))) =
      ⟨j.val + 2 ^ k, fin_pow2_right j⟩ := by
    apply Fin.ext; dsimp; omega
  exact congrArg f heq

theorem wht_dot_eq : ∀ (k : Nat) (u v : Fin (2 ^ k) → Int),
    dotInt (wht k u) (wht k v) = (2 ^ k : Int) * dotInt u v
  | 0, u, v => by simp [wht, dotInt]
  | k + 1, u, v => by
    unfold dotInt
    rw [finSumInt_pow2_split (fun i => wht (k + 1) u i * wht (k + 1) v i)]
    let uL : Fin (2 ^ k) → Int := fun i => u ⟨i.val, fin_pow2_left i⟩
    let uR : Fin (2 ^ k) → Int := fun i => u ⟨i.val + 2 ^ k, fin_pow2_right i⟩
    let vL : Fin (2 ^ k) → Int := fun i => v ⟨i.val, fin_pow2_left i⟩
    let vR : Fin (2 ^ k) → Int := fun i => v ⟨i.val + 2 ^ k, fin_pow2_right i⟩
    have hL : finSumInt (fun i : Fin (2 ^ k) =>
        wht (k + 1) u ⟨i.val, fin_pow2_left i⟩ * wht (k + 1) v ⟨i.val, fin_pow2_left i⟩) =
      finSumInt (fun i : Fin (2 ^ k) =>
        (wht k uL i + wht k uR i) * (wht k vL i + wht k vR i)) := by
      apply finSumInt_congr; intro i
      rw [wht_succ_left, wht_succ_left]
    have hR : finSumInt (fun j : Fin (2 ^ k) =>
        wht (k + 1) u ⟨j.val + 2 ^ k, fin_pow2_right j⟩ *
        wht (k + 1) v ⟨j.val + 2 ^ k, fin_pow2_right j⟩) =
      finSumInt (fun j : Fin (2 ^ k) =>
        (wht k uL j - wht k uR j) * (wht k vL j - wht k vR j)) := by
      apply finSumInt_congr; intro j
      rw [wht_succ_right, wht_succ_right]
    rw [hL, hR, ← finSumInt_add]
    have hcomb : finSumInt (fun i : Fin (2 ^ k) =>
        (wht k uL i + wht k uR i) * (wht k vL i + wht k vR i) +
        (wht k uL i - wht k uR i) * (wht k vL i - wht k vR i)) =
      2 * (dotInt (wht k uL) (wht k vL) + dotInt (wht k uR) (wht k vR)) := by
      unfold dotInt
      rw [← finSumInt_add, ← finSumInt_mul_left]
      apply finSumInt_congr; intro i; grind
    rw [hcomb, wht_dot_eq k uL vL, wht_dot_eq k uR vR]
    rw [finSumInt_pow2_split (fun i => u i * v i)]
    have hpow : (2 ^ (k + 1) : Int) = 2 * (2 ^ k : Int) := by
      rw [Int.pow_succ]; grind
    rw [hpow]
    unfold dotInt
    grind

theorem wht_normSq_eq (k : Nat) (v : Fin (2 ^ k) → Int) :
    normSqInt (wht k v) = (2 ^ k : Int) * normSqInt v :=
  wht_dot_eq k v v

theorem wht_succ_lt (k : Nat) (v : Fin (2 ^ (k + 1)) → Int) (i : Fin (2 ^ (k + 1))) (hi : i.val < 2 ^ k) :
    wht (k + 1) v i =
      wht k (fun t : Fin (2 ^ k) => v ⟨t.val, fin_pow2_left t⟩) ⟨i.val, hi⟩ +
      wht k (fun t : Fin (2 ^ k) => v ⟨t.val + 2 ^ k, fin_pow2_right t⟩) ⟨i.val, hi⟩ :=
  wht_succ_left k v ⟨i.val, hi⟩

theorem wht_succ_ge (k : Nat) (v : Fin (2 ^ (k + 1)) → Int) (i : Fin (2 ^ (k + 1))) (hi : ¬ i.val < 2 ^ k) :
    wht (k + 1) v i =
      wht k (fun t : Fin (2 ^ k) => v ⟨t.val, fin_pow2_left t⟩) ⟨i.val - 2 ^ k, fin_pow2_sub i hi⟩ -
      wht k (fun t : Fin (2 ^ k) => v ⟨t.val + 2 ^ k, fin_pow2_right t⟩) ⟨i.val - 2 ^ k, fin_pow2_sub i hi⟩ := by
  have heq : i = ⟨(⟨i.val - 2 ^ k, fin_pow2_sub i hi⟩ : Fin (2 ^ k)).val + 2 ^ k,
      fin_pow2_right ⟨i.val - 2 ^ k, fin_pow2_sub i hi⟩⟩ := by
    apply Fin.ext; dsimp; omega
  calc wht (k + 1) v i
      = wht (k + 1) v ⟨(⟨i.val - 2 ^ k, fin_pow2_sub i hi⟩ : Fin (2 ^ k)).val + 2 ^ k,
          fin_pow2_right ⟨i.val - 2 ^ k, fin_pow2_sub i hi⟩⟩ := congrArg (wht (k + 1) v) heq
    _ = _ := wht_succ_right k v ⟨i.val - 2 ^ k, fin_pow2_sub i hi⟩

theorem wht_add : ∀ (k : Nat) (a b : Fin (2 ^ k) → Int) (i : Fin (2 ^ k)),
    wht k (fun t => a t + b t) i = wht k a i + wht k b i
  | 0, a, b, i => by simp [wht]
  | k + 1, a, b, i => by
    by_cases hi : i.val < 2 ^ k
    · rw [wht_succ_lt k _ i hi, wht_succ_lt k a i hi, wht_succ_lt k b i hi]
      rw [wht_add k, wht_add k]; omega
    · rw [wht_succ_ge k _ i hi, wht_succ_ge k a i hi, wht_succ_ge k b i hi]
      rw [wht_add k, wht_add k]; omega

theorem wht_sub : ∀ (k : Nat) (a b : Fin (2 ^ k) → Int) (i : Fin (2 ^ k)),
    wht k (fun t => a t - b t) i = wht k a i - wht k b i
  | 0, a, b, i => by simp [wht]
  | k + 1, a, b, i => by
    by_cases hi : i.val < 2 ^ k
    · rw [wht_succ_lt k _ i hi, wht_succ_lt k a i hi, wht_succ_lt k b i hi]
      rw [wht_sub k, wht_sub k]; omega
    · rw [wht_succ_ge k _ i hi, wht_succ_ge k a i hi, wht_succ_ge k b i hi]
      rw [wht_sub k, wht_sub k]; omega

theorem wht_involutive : ∀ (k : Nat) (v : Fin (2 ^ k) → Int) (i : Fin (2 ^ k)),
    wht k (wht k v) i = (2 ^ k : Int) * v i
  | 0, v, i => by simp [wht]
  | k + 1, v, i => by
    let vL : Fin (2 ^ k) → Int := fun j => v ⟨j.val, fin_pow2_left j⟩
    let vR : Fin (2 ^ k) → Int := fun j => v ⟨j.val + 2 ^ k, fin_pow2_right j⟩
    have hEqL : (fun j : Fin (2 ^ k) => wht (k + 1) v ⟨j.val, fin_pow2_left j⟩) =
        fun j => wht k vL j + wht k vR j := by
      funext j; exact wht_succ_left k v j
    have hEqR : (fun j : Fin (2 ^ k) => wht (k + 1) v ⟨j.val + 2 ^ k, fin_pow2_right j⟩) =
        fun j => wht k vL j - wht k vR j := by
      funext j; exact wht_succ_right k v j
    have hpow : (2 ^ (k + 1) : Int) = 2 * (2 ^ k : Int) := by rw [Int.pow_succ]; grind
    by_cases hi : i.val < 2 ^ k
    · rw [wht_succ_lt k _ i hi, hEqL, hEqR, wht_add, wht_sub,
          wht_involutive k vL, wht_involutive k vR, hpow]
      dsimp [vL]; grind
    · rw [wht_succ_ge k _ i hi, hEqL, hEqR, wht_add, wht_sub,
          wht_involutive k vL, wht_involutive k vR, hpow]
      have hvi : vR ⟨i.val - 2 ^ k, fin_pow2_sub i hi⟩ = v i := by
        show v ⟨i.val - 2 ^ k + 2 ^ k, _⟩ = v i
        congr 1; apply Fin.ext; dsimp; omega
      rw [hvi]; grind

theorem wht_zero : ∀ (k : Nat) (i : Fin (2 ^ k)),
    wht k (fun _ => (0 : Int)) i = 0
  | 0, _ => rfl
  | k + 1, i => by
    by_cases hi : i.val < 2 ^ k
    · rw [wht_succ_lt k _ i hi, wht_zero k]; omega
    · rw [wht_succ_ge k _ i hi, wht_zero k]; omega

theorem wht_outlierVec_flat : ∀ (k : Nat) (M : Int) (i : Fin (2 ^ k)),
    wht k (outlierVec k M) i = M
  | 0, M, i => by
    simp [wht, outlierVec]
  | k + 1, M, i => by
    have hL : (fun j : Fin (2 ^ k) => outlierVec (k + 1) M ⟨j.val, fin_pow2_left j⟩) =
        outlierVec k M := by funext j; rfl
    have hR : (fun j : Fin (2 ^ k) => outlierVec (k + 1) M ⟨j.val + 2 ^ k, fin_pow2_right j⟩) =
        (fun _ => (0 : Int)) := by
      funext j
      simp [outlierVec]
    by_cases hi : i.val < 2 ^ k
    · rw [wht_succ_lt k _ i hi, hL, hR, wht_outlierVec_flat k M, wht_zero k]; omega
    · rw [wht_succ_ge k _ i hi, hL, hR, wht_outlierVec_flat k M, wht_zero k]; omega

theorem wht_outlierSignal_eq : ∀ (k : Nat) (_hk : 1 ≤ k) (M a : Int) (i : Fin (2 ^ k)),
    wht k (outlierSignalVec k M a) i = if i.val % 2 = 0 then M + a else M - a
  | 0, hk, _, _, _ => by omega
  | 1, _, M, a, i => by
    have hi : i.val = 0 ∨ i.val = 1 := by have := i.isLt; omega
    cases hi with
    | inl h0 =>
      have : i = ⟨0, by decide⟩ := Fin.ext h0
      subst this; simp [wht, outlierSignalVec]
    | inr h1 =>
      have : i = ⟨1, by decide⟩ := Fin.ext h1
      subst this; simp [wht, outlierSignalVec]
  | k + 2, _, M, a, i => by
    have h2ge2 : 2 ≤ 2 ^ (k + 1) := by
      have h1 : 1 ≤ 2 ^ k := Nat.two_pow_pos k
      rw [pow2_succ_eq_add]; omega
    have hL : (fun j : Fin (2 ^ (k + 1)) =>
        outlierSignalVec (k + 2) M a ⟨j.val, fin_pow2_left j⟩) =
        outlierSignalVec (k + 1) M a := by funext j; rfl
    have hR : (fun j : Fin (2 ^ (k + 1)) =>
        outlierSignalVec (k + 2) M a ⟨j.val + 2 ^ (k + 1), fin_pow2_right j⟩) =
        (fun _ => (0 : Int)) := by
      funext j
      have hne1 : j.val + 2 ^ (k + 1) ≠ 1 := by omega
      simp [outlierSignalVec, hne1]
    by_cases hi : i.val < 2 ^ (k + 1)
    · rw [wht_succ_lt (k + 1) _ i hi, hL, hR, wht_outlierSignal_eq (k + 1) (by omega) M a, wht_zero (k + 1)]
      simp
    · rw [wht_succ_ge (k + 1) _ i hi, hL, hR, wht_outlierSignal_eq (k + 1) (by omega) M a, wht_zero (k + 1)]
      have heven : 2 ^ (k + 1) % 2 = 0 := by rw [pow2_succ_eq_add]; omega
      have hmod : (i.val - 2 ^ (k + 1)) % 2 = i.val % 2 := by omega
      simp [hmod]

theorem wht_basisVec_pm1 : ∀ (k : Nat) (j i : Fin (2 ^ k)),
    wht k (basisVec k j) i = 1 ∨ wht k (basisVec k j) i = -1
  | 0, j, i => by
    left; simp [wht, basisVec]
  | k + 1, j, i => by
    by_cases hj : j.val < 2 ^ k
    · have hL : (fun t : Fin (2 ^ k) => basisVec (k + 1) j ⟨t.val, fin_pow2_left t⟩) =
          basisVec k ⟨j.val, hj⟩ := by funext t; rfl
      have hR : (fun t : Fin (2 ^ k) => basisVec (k + 1) j ⟨t.val + 2 ^ k, fin_pow2_right t⟩) =
          (fun _ => (0 : Int)) := by
        funext t
        have hne : t.val + 2 ^ k ≠ j.val := by omega
        simp [basisVec, hne]
      by_cases hi : i.val < 2 ^ k
      · rw [wht_succ_lt k _ i hi, hL, hR, wht_zero k]
        cases wht_basisVec_pm1 k ⟨j.val, hj⟩ ⟨i.val, hi⟩ with
        | inl h => left; omega
        | inr h => right; omega
      · rw [wht_succ_ge k _ i hi, hL, hR, wht_zero k]
        cases wht_basisVec_pm1 k ⟨j.val, hj⟩ ⟨i.val - 2 ^ k, fin_pow2_sub i hi⟩ with
        | inl h => left; omega
        | inr h => right; omega
    · have hj' := fin_pow2_sub j hj
      have hL : (fun t : Fin (2 ^ k) => basisVec (k + 1) j ⟨t.val, fin_pow2_left t⟩) =
          (fun _ => (0 : Int)) := by
        funext t
        have hne : t.val ≠ j.val := by have := t.isLt; omega
        simp [basisVec, hne]
      have hR : (fun t : Fin (2 ^ k) => basisVec (k + 1) j ⟨t.val + 2 ^ k, fin_pow2_right t⟩) =
          basisVec k ⟨j.val - 2 ^ k, hj'⟩ := by
        funext t
        simp only [basisVec]
        by_cases ht : t.val = j.val - 2 ^ k
        · simp [ht]; omega
        · have ht' : t.val + 2 ^ k ≠ j.val := by omega
          simp [ht, ht']
      by_cases hi : i.val < 2 ^ k
      · rw [wht_succ_lt k _ i hi, hL, hR, wht_zero k]
        cases wht_basisVec_pm1 k ⟨j.val - 2 ^ k, hj'⟩ ⟨i.val, hi⟩ with
        | inl h => left; omega
        | inr h => right; omega
      · rw [wht_succ_ge k _ i hi, hL, hR, wht_zero k]
        cases wht_basisVec_pm1 k ⟨j.val - 2 ^ k, hj'⟩ ⟨i.val - 2 ^ k, fin_pow2_sub i hi⟩ with
        | inl h => right; omega
        | inr h => left; omega

theorem wht_basisVec_hamming_equidistant :
    ∀ (k : Nat) (_hk : 1 ≤ k) (j : Fin (2 ^ k)),
      j.val ≠ 0 →
      hammingDist (simHash (wht k (basisVec k ⟨0, Nat.two_pow_pos k⟩)))
        (simHash (wht k (basisVec k j))) = 2 ^ (k - 1)
  | 0, hk, _, _ => by omega
  | 1, _, j, hj0 => by
    have hj1 : j.val = 1 := by have := j.isLt; omega
    have hj : j = ⟨1, by decide⟩ := Fin.ext hj1
    subst hj
    decide
  | k + 2, _, j, hj0 => by
    have h0flat : ∀ i : Fin (2 ^ (k + 2)),
        simHash (wht (k + 2) (basisVec (k + 2) ⟨0, Nat.two_pow_pos (k + 2)⟩)) i = true := by
      intro i
      unfold simHash
      have heq : basisVec (k + 2) ⟨0, Nat.two_pow_pos (k + 2)⟩ = outlierVec (k + 2) 1 := rfl
      rw [heq, wht_outlierVec_flat]; rfl
    unfold hammingDist
    rw [finSumNat_congr (g := fun i => if simHash (wht (k + 2) (basisVec (k + 2) j)) i = true then 0 else 1)]
    · rw [finSumNat_pow2_split]
      by_cases hj : j.val < 2 ^ (k + 1)
      · have hL : (fun t : Fin (2 ^ (k + 1)) => basisVec (k + 2) j ⟨t.val, fin_pow2_left t⟩) =
            basisVec (k + 1) ⟨j.val, hj⟩ := by funext t; rfl
        have hR : (fun t : Fin (2 ^ (k + 1)) => basisVec (k + 2) j ⟨t.val + 2 ^ (k + 1), fin_pow2_right t⟩) =
            (fun _ => (0 : Int)) := by
          funext t
          have hne : t.val + 2 ^ (k + 1) ≠ j.val := by omega
          simp [basisVec, hne]
        have hpart1 : finSumNat (fun i : Fin (2 ^ (k + 1)) =>
            if simHash (wht (k + 2) (basisVec (k + 2) j)) ⟨i.val, fin_pow2_left i⟩ = true then 0 else 1) =
            2 ^ k := by
          have hih := wht_basisVec_hamming_equidistant (k + 1) (by omega) ⟨j.val, hj⟩ hj0
          simp only [Nat.add_sub_cancel] at hih
          rw [← hih]
          unfold hammingDist
          apply finSumNat_congr; intro i
          have h0i : simHash (wht (k + 1) (basisVec (k + 1) ⟨0, Nat.two_pow_pos (k + 1)⟩)) i = true := by
            unfold simHash
            have heq : basisVec (k + 1) ⟨0, Nat.two_pow_pos (k + 1)⟩ = outlierVec (k + 1) 1 := rfl
            rw [heq, wht_outlierVec_flat]; rfl
          rw [h0i]
          have hwi : wht (k + 2) (basisVec (k + 2) j) ⟨i.val, fin_pow2_left i⟩ =
              wht (k + 1) (basisVec (k + 1) ⟨j.val, hj⟩) i := by
            rw [wht_succ_left, hL, hR, wht_zero (k + 1)]; omega
          simp only [simHash, hwi]
          by_cases hb : signBit (wht (k + 1) (basisVec (k + 1) ⟨j.val, hj⟩) i) = true
          · simp [hb]
          · simp [hb]
        have hpart2 : finSumNat (fun i : Fin (2 ^ (k + 1)) =>
            if simHash (wht (k + 2) (basisVec (k + 2) j)) ⟨i.val + 2 ^ (k + 1), fin_pow2_right i⟩ = true then 0 else 1) =
            2 ^ k := by
          have hih := wht_basisVec_hamming_equidistant (k + 1) (by omega) ⟨j.val, hj⟩ hj0
          simp only [Nat.add_sub_cancel] at hih
          rw [← hih]
          unfold hammingDist
          apply finSumNat_congr; intro i
          have h0i : simHash (wht (k + 1) (basisVec (k + 1) ⟨0, Nat.two_pow_pos (k + 1)⟩)) i = true := by
            unfold simHash
            have heq : basisVec (k + 1) ⟨0, Nat.two_pow_pos (k + 1)⟩ = outlierVec (k + 1) 1 := rfl
            rw [heq, wht_outlierVec_flat]; rfl
          rw [h0i]
          have hwi : wht (k + 2) (basisVec (k + 2) j) ⟨i.val + 2 ^ (k + 1), fin_pow2_right i⟩ =
              wht (k + 1) (basisVec (k + 1) ⟨j.val, hj⟩) i := by
            rw [wht_succ_right, hL, hR, wht_zero (k + 1)]; omega
          simp only [simHash, hwi]
          by_cases hb : signBit (wht (k + 1) (basisVec (k + 1) ⟨j.val, hj⟩) i) = true
          · simp [hb]
          · simp [hb]
        rw [hpart1, hpart2]
        have hsub : k + 2 - 1 = k + 1 := by omega
        rw [hsub, pow2_succ_eq_add]
      · have hj' := fin_pow2_sub j hj
        have hL : (fun t : Fin (2 ^ (k + 1)) => basisVec (k + 2) j ⟨t.val, fin_pow2_left t⟩) =
            (fun _ => (0 : Int)) := by
          funext t
          have hne : t.val ≠ j.val := by have := t.isLt; omega
          simp [basisVec, hne]
        have hR : (fun t : Fin (2 ^ (k + 1)) => basisVec (k + 2) j ⟨t.val + 2 ^ (k + 1), fin_pow2_right t⟩) =
            basisVec (k + 1) ⟨j.val - 2 ^ (k + 1), hj'⟩ := by
          funext t
          simp only [basisVec]
          by_cases ht : t.val = j.val - 2 ^ (k + 1)
          · simp [ht]; omega
          · have ht' : t.val + 2 ^ (k + 1) ≠ j.val := by omega
            simp [ht, ht']
        rw [← finSumNat_add]
        have hsum1 : finSumNat (fun i : Fin (2 ^ (k + 1)) =>
            (if simHash (wht (k + 2) (basisVec (k + 2) j)) ⟨i.val, fin_pow2_left i⟩ = true then 0 else 1) +
            (if simHash (wht (k + 2) (basisVec (k + 2) j)) ⟨i.val + 2 ^ (k + 1), fin_pow2_right i⟩ = true then 0 else 1)) =
            finSumNat (fun _ : Fin (2 ^ (k + 1)) => 1) := by
          apply finSumNat_congr; intro i
          have hw1 : wht (k + 2) (basisVec (k + 2) j) ⟨i.val, fin_pow2_left i⟩ =
              wht (k + 1) (basisVec (k + 1) ⟨j.val - 2 ^ (k + 1), hj'⟩) i := by
            rw [wht_succ_left, hL, hR, wht_zero (k + 1)]; omega
          have hw2 : wht (k + 2) (basisVec (k + 2) j) ⟨i.val + 2 ^ (k + 1), fin_pow2_right i⟩ =
              -(wht (k + 1) (basisVec (k + 1) ⟨j.val - 2 ^ (k + 1), hj'⟩) i) := by
            rw [wht_succ_right, hL, hR, wht_zero (k + 1)]; omega
          simp only [simHash, hw1, hw2]
          cases wht_basisVec_pm1 (k + 1) ⟨j.val - 2 ^ (k + 1), hj'⟩ i with
          | inl h => rw [h]; decide
          | inr h => rw [h]; decide
        rw [hsum1, finSumNat_const]
        simp
    · intro i
      rw [h0flat i]
      by_cases hb : simHash (wht (k + 2) (basisVec (k + 2) j)) i = true
      · simp [hb]
      · simp [hb]

/-- Headline Theorem 4 (`bipartite_wht_int4_outlier_rescue_vs_binary_walsh_tie`). -/
theorem bipartite_wht_int4_outlier_rescue_vs_binary_walsh_tie :
    (∀ (k : Nat) (u v : Fin (2 ^ k) → Int),
      dotInt (wht k u) (wht k v) = (2 ^ k : Int) * dotInt u v ∧
      normSqInt (wht k u) = (2 ^ k : Int) * normSqInt u ∧
      (∀ i : Fin (2 ^ k), wht k (wht k u) i = (2 ^ k : Int) * u i)) ∧
    (∀ (k : Nat) (M : Int) (i : Fin (2 ^ k)),
      wht k (outlierVec k M) i = M ∧
      ((wht k (outlierVec k M) i : Rat) * (wht k (outlierVec k M) i : Rat)) / ((2 ^ k : Nat) : Rat) =
        ((M : Rat) * (M : Rat)) / ((2 ^ k : Nat) : Rat)) ∧
    (∀ (m : Nat) (M : Int) (i : Fin (2 ^ (2 * m))),
      (wht (2 * m) (outlierVec (2 * m) M) i : Rat) / ((2 ^ m : Nat) : Rat) =
        (M : Rat) / ((2 ^ m : Nat) : Rat)) ∧
    (∀ (k : Nat), 1 ≤ k → ∀ (M a b1 b2 : Int),
      0 < a → 0 < b1 → 0 < b2 → a < M → b1 < M → b2 < M →
      let q := outlierSignalVec k M a
      let k1 := outlierSignalVec k M b1
      let k2 := outlierSignalVec k M (-b2)
      hammingDist (simHash q) (simHash k1) = 0 ∧
      hammingDist (simHash q) (simHash k2) = 1 ∧
      hammingDist (simHash (wht k q)) (simHash (wht k k1)) = 0 ∧
      hammingDist (simHash (wht k q)) (simHash (wht k k2)) = 0) ∧
    (∀ (k : Nat), 1 ≤ k → ∀ (j : Fin (2 ^ k)),
      j.val ≠ 0 →
      hammingDist (simHash (wht k (basisVec k ⟨0, Nat.two_pow_pos k⟩)))
        (simHash (wht k (basisVec k j))) = 2 ^ (k - 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k u v
    exact ⟨wht_dot_eq k u v, wht_normSq_eq k u, wht_involutive k u⟩
  · intro k M i
    have hflat := wht_outlierVec_flat k M i
    exact ⟨hflat, by rw [hflat]⟩
  · intro m M i
    rw [wht_outlierVec_flat (2 * m) M i]
  · intro k hk M a b1 b2 ha hb1 hb2 haM hb1M hb2M
    intro q k1 k2
    have hraw1 : hammingDist (simHash q) (simHash k1) = 0 := by
      unfold hammingDist
      rw [finSumNat_congr (g := fun _ => 0)]
      · exact finSumNat_zero (2 ^ k)
      · intro i
        have hEq : simHash q i = simHash k1 i := by
          simp only [simHash, signBit, q, k1, outlierSignalVec]
          split
          · rfl
          · split
            · have ha0 : 0 ≤ a := by omega
              have hb0 : 0 ≤ b1 := by omega
              simp [ha0, hb0]
            · rfl
        simp [hEq]
    have hraw2 : hammingDist (simHash q) (simHash k2) = 1 := by
      have h1lt : 1 < 2 ^ k := by
        have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
        omega
      let idx1 : Fin (2 ^ k) := ⟨1, h1lt⟩
      unfold hammingDist
      rw [finSumNat_congr (g := fun i => if i = idx1 then 1 else 0)]
      · exact finSumNat_single idx1 1
      · intro i
        by_cases hi1 : i = idx1
        · subst hi1
          simp only [simHash, signBit, q, k2, outlierSignalVec, idx1]
          have ha0 : 0 ≤ a := by omega
          simp [ha0]
          exact hb2
        · have hne1 : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
          have hEq : simHash q i = simHash k2 i := by
            simp only [simHash, signBit, q, k2, outlierSignalVec, hne1, ite_false]
          simp [hEq, hi1]
    have hallPos : ∀ (x : Int), -M < x → x < M →
        ∀ i : Fin (2 ^ k), simHash (wht k (outlierSignalVec k M x)) i = true := by
      intro x hxlo hxhi i
      rw [simHash, wht_outlierSignal_eq k hk M x i]
      unfold signBit
      split
      · simp; omega
      · simp; omega
    have hwht1 : hammingDist (simHash (wht k q)) (simHash (wht k k1)) = 0 := by
      unfold hammingDist
      rw [finSumNat_congr (g := fun _ => 0)]
      · exact finSumNat_zero (2 ^ k)
      · intro i
        rw [hallPos a (by omega) haM i, hallPos b1 (by omega) hb1M i]
        rfl
    have hwht2 : hammingDist (simHash (wht k q)) (simHash (wht k k2)) = 0 := by
      unfold hammingDist
      rw [finSumNat_congr (g := fun _ => 0)]
      · exact finSumNat_zero (2 ^ k)
      · intro i
        rw [hallPos a (by omega) haM i, hallPos (-b2) (by omega) (by omega) i]
        rfl
    exact ⟨hraw1, hraw2, hwht1, hwht2⟩
  · exact wht_basisVec_hamming_equidistant

end VlmTomeCumulant
