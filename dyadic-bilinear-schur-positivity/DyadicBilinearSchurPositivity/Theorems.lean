import DyadicBilinearSchurPositivity.Defs

namespace DyadicPDEngine
namespace Dyadic
end Dyadic
namespace ZHalf
end ZHalf
open ZHalf

/-- Mode 1 UNIVERSAL INFINITE SOUNDNESS THEOREM:
    If the finite Z[1/2] certificate passes `checkStrictPD`, then for EVERY `k : Nat`
    and EVERY nonzero `x : Fin (2^k) → ZHalf`, the target quadratic form is strictly positive! -/
theorem soundness_strict_pd {m : Nat} (sys : BQS m) (Wtarget : Fin m → Fin m → ZHalf)
    (cert : PDCert m) (hcheck : checkStrictPD sys Wtarget cert = true) :
    ∀ (k : Nat) (x : Fin (2 ^ k) → ZHalf), (∃ i, x i ≠ 0) →
      0 < sys.Q k x + quadForm Wtarget (sys.L k x) := by
  unfold checkStrictPD checkCoreCert at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hCsym, hWsym⟩, _⟩, hHpos⟩, hdet⟩, hh00⟩, hh01⟩, hh11⟩, hDpos⟩, hDeq⟩, hSpos⟩, hSeq⟩, hf0⟩
  have hC : ∀ i j, sys.C i j = sys.C j i := isSymmMat_sound hCsym
  have hW : ∀ i j, cert.W i j = cert.W j i := isSymmMat_sound hWsym
  have hDm := matEq_sound hDeq
  have hSm := matEq_sound hSeq
  unfold allPosWeights at hHpos
  simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hHpos
  rcases hHpos with ⟨hw1, hw2, hwExtra⟩
  have hF_ind : ∀ k : Nat,
      (∀ x : Fin (2 ^ k) → ZHalf, 0 ≤ sys.F cert.W k x) ∧
      (∀ x : Fin (2 ^ k) → ZHalf, (∃ i, x i ≠ 0) → 0 < sys.F cert.W k x) := by
    intro k
    induction k with
    | zero =>
      constructor
      · intro x; rw [sys.F_zero_eq]; exact mul_nonneg (le_of_lt hf0) (sq_nonneg _)
      · intro x ⟨⟨v, hv⟩, hne⟩
        have hv0 : (⟨v, hv⟩ : Fin (2 ^ 0)) = ⟨0, by decide⟩ := Fin.ext (by omega)
        rw [hv0] at hne
        rw [sys.F_zero_eq]
        exact mul_pos hf0 (sq_pos_of_ne_zero hne)
    | succ k ih =>
      rcases ih with ⟨ih_ge, ih_gt⟩
      have hStep : ∀ x : Fin (2 ^ (k + 1)) → ZHalf,
          sys.F cert.W (k + 1) x =
            (cert.h1.1 * sys.F cert.W k (vecAdd (vecSmul cert.h1.2.1 (evenHalf x)) (vecSmul cert.h1.2.2 (oddHalf x))) +
             cert.h2.1 * sys.F cert.W k (vecAdd (vecSmul cert.h2.2.1 (evenHalf x)) (vecSmul cert.h2.2.2 (oddHalf x))) +
             hTermsEval sys cert.W k cert.hExtra (evenHalf x) (oddHalf x)) +
            sosEval cert.deltaTerms (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) := by
        intro x
        rw [sys.F_step_identity cert.W k x]
        have hHT := hTermsEval_eq sys cert.W hC hW k (cert.h1 :: cert.h2 :: cert.hExtra) (evenHalf x) (oddHalf x)
        rw [hh00, hh01, hh11] at hHT
        rw [← hHT]
        have hDval : quadForm (deltaMat sys cert.W) (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) =
                     sosEval cert.deltaTerms (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) := by
          rw [← quadForm_sosMatrix cert.deltaTerms]
          unfold quadForm quadBilin
          apply sumFin_congr; intro i
          apply sumFin_congr; intro j
          rw [hDm i j]
        rw [hDval]
        change (cert.h1.1 * sys.F cert.W k (vecAdd (vecSmul cert.h1.2.1 (evenHalf x)) (vecSmul cert.h1.2.2 (oddHalf x))) +
                (cert.h2.1 * sys.F cert.W k (vecAdd (vecSmul cert.h2.2.1 (evenHalf x)) (vecSmul cert.h2.2.2 (oddHalf x))) +
                 hTermsEval sys cert.W k cert.hExtra (evenHalf x) (oddHalf x))) +
               sosEval cert.deltaTerms (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) = _
        rw [← add_assoc (cert.h1.1 * _)]
      constructor
      · intro x
        rw [hStep x]
        refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
        · exact mul_nonneg (le_of_lt hw1) (ih_ge _)
        · exact mul_nonneg (le_of_lt hw2) (ih_ge _)
        · exact hTermsEval_nonneg sys cert.W k ih_ge hwExtra _ _
        · exact sosEval_nonneg hDpos _
      · intro x hx
        rw [hStep x]
        have hsp := spanning_pair_nonzero hdet (ne_zero_split hx)
        have hExtra_ge : 0 ≤ hTermsEval sys cert.W k cert.hExtra (evenHalf x) (oddHalf x) :=
          hTermsEval_nonneg sys cert.W k ih_ge hwExtra _ _
        have hD_ge : 0 ≤ sosEval cert.deltaTerms (pairVec (sys.L k (evenHalf x)) (sys.L k (oddHalf x))) :=
          sosEval_nonneg hDpos _
        rcases hsp with h1ne | h2ne
        · have h1pos := mul_pos hw1 (ih_gt _ h1ne)
          have h2ge  := mul_nonneg (le_of_lt hw2) (ih_ge (vecAdd (vecSmul cert.h2.2.1 (evenHalf x)) (vecSmul cert.h2.2.2 (oddHalf x))))
          exact add_pos_of_pos_of_nonneg
            (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg h1pos h2ge) hExtra_ge) hD_ge
        · have h1ge  := mul_nonneg (le_of_lt hw1) (ih_ge (vecAdd (vecSmul cert.h1.2.1 (evenHalf x)) (vecSmul cert.h1.2.2 (oddHalf x))))
          have h2pos := mul_pos hw2 (ih_gt _ h2ne)
          exact add_pos_of_pos_of_nonneg
            (add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos h1ge h2pos) hExtra_ge) hD_ge
  intro k x hx
  have hFpos : 0 < sys.F cert.W k x := (hF_ind k).2 x hx
  have hSurplus : 0 ≤ quadForm (fun i j => Wtarget i j - cert.W i j) (sys.L k x) := by
    have heq : quadForm (fun i j => Wtarget i j - cert.W i j) (sys.L k x) =
               sosEval cert.surplusTerms (sys.L k x) := by
      rw [← quadForm_sosMatrix cert.surplusTerms]
      unfold quadForm quadBilin
      apply sumFin_congr; intro i
      apply sumFin_congr; intro j
      dsimp only
      rw [hSm i j]
    rw [heq]
    exact sosEval_nonneg hSpos _
  have hDecomp : sys.Q k x + quadForm Wtarget (sys.L k x) =
      sys.F cert.W k x + quadForm (fun i j => Wtarget i j - cert.W i j) (sys.L k x) := by
    unfold BQS.F BQS.BF BQS.Q quadForm
    rw [quadBilin_mat_sub, add_assoc, sub_eq_add_neg]
    calc sys.B k x x + quadBilin Wtarget (sys.L k x) (sys.L k x)
        = sys.B k x x + (quadBilin Wtarget (sys.L k x) (sys.L k x) + 0) := by rw [add_zero]
      _ = sys.B k x x + (quadBilin Wtarget (sys.L k x) (sys.L k x) +
            (quadBilin cert.W (sys.L k x) (sys.L k x) + -(quadBilin cert.W (sys.L k x) (sys.L k x)))) := by
            rw [add_neg_cancel]
      _ = sys.B k x x + (quadBilin cert.W (sys.L k x) (sys.L k x) +
            (quadBilin Wtarget (sys.L k x) (sys.L k x) + -(quadBilin cert.W (sys.L k x) (sys.L k x)))) := by
            congr 1
            rw [← add_assoc, add_comm (quadBilin Wtarget _ _) (quadBilin cert.W _ _), add_assoc]
  rw [hDecomp]
  exact add_pos_of_pos_of_nonneg hFpos hSurplus

/-! ### Mode 2: Degenerate-Base Boundary-Kernel-Collapse Lifter (`checkBoundaryStrictPD`) -/

/-- Pure-silicon 2-adic identity: `v_2(|i - j|) = ctz(i ^^^ j)` for ALL `i, j : Nat`! -/
theorem v2Nat_xor_eq_absDiff (i j : Nat) : v2Nat (i ^^^ j) = v2Nat (absDiff i j) := by
  have gen : ∀ m i j : Nat, i + j ≤ m → v2Nat (i ^^^ j) = v2Nat (absDiff i j) := by
    intro m
    induction m with
    | zero =>
      intro i j hij
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      subst hi; subst hj; rfl
    | succ m ih =>
      intro i j hij
      by_cases heq : i = j
      · subst heq; simp [absDiff_self]
      · by_cases hp : i % 2 = j % 2
        · have hxor_even : (i ^^^ j) % 2 = 0 := by
            have hb := Nat.testBit_xor i j 0
            simp only [Nat.testBit_zero] at hb
            rw [hp] at hb
            have hfalse : decide ((i ^^^ j) % 2 = 1) = false := by
              rw [hb]; cases decide (j % 2 = 1) <;> rfl
            have hne1 : ¬ ((i ^^^ j) % 2 = 1) := of_decide_eq_false hfalse
            omega
          have hxor_ne : (i ^^^ j) ≠ 0 := by
            intro hz
            apply heq
            exact Nat.eq_of_testBit_eq fun b => by
              have htb := congrArg (fun x => x.testBit b) hz
              rw [Nat.testBit_xor, Nat.zero_testBit] at htb
              cases hi : i.testBit b <;> cases hj : j.testBit b <;> simp_all
          have hxor_div : (i ^^^ j) / 2 = (i / 2) ^^^ (j / 2) := by
            rw [← Nat.shiftRight_eq_div_pow _ 1, ← Nat.shiftRight_eq_div_pow _ 1, ← Nat.shiftRight_eq_div_pow _ 1]
            exact Nat.shiftRight_xor_distrib
          have hdiff_ne : absDiff (i / 2) (j / 2) ≠ 0 := by
            unfold absDiff; split <;> omega
          have hdiff_eq : absDiff i j = 2 * absDiff (i / 2) (j / 2) := by
            unfold absDiff; split <;> split <;> omega
          have hL : v2Nat (i ^^^ j) = 1 + v2Nat ((i / 2) ^^^ (j / 2)) := by
            have h2 : i ^^^ j = 2 * ((i ^^^ j) / 2) := by omega
            have hdivne : (i ^^^ j) / 2 ≠ 0 := by omega
            conv => lhs; rw [h2]
            rw [v2Nat_two_mul hdivne, hxor_div]
          have hR : v2Nat (absDiff i j) = 1 + v2Nat (absDiff (i / 2) (j / 2)) := by
            rw [hdiff_eq, v2Nat_two_mul hdiff_ne]
          rw [hL, hR]
          congr 1
          exact ih (i / 2) (j / 2) (by omega)
        · have hxor_odd : (i ^^^ j) % 2 = 1 := by
            have hb := Nat.testBit_xor i j 0
            simp only [Nat.testBit_zero] at hb
            by_cases h1 : i % 2 = 1
            · have h2 : ¬ (j % 2 = 1) := by omega
              simp only [h1, h2, decide_true, decide_false] at hb
              exact of_decide_eq_true hb
            · have h2 : j % 2 = 1 := by omega
              simp only [h1, h2, decide_true, decide_false] at hb
              exact of_decide_eq_true hb
          have hdiff_odd : absDiff i j % 2 = 1 := by
            unfold absDiff; split <;> omega
          rw [v2Nat_odd _ hxor_odd, v2Nat_odd _ hdiff_odd]
  exact gen (i + j) i j (Nat.le_refl _)

theorem riesz2AdicForm_succ (s k : Nat) (x : Fin (2 ^ (k + 1)) → ZHalf) :
    riesz2AdicForm s (k + 1) x =
      pow2Neg (s + 2) * riesz2AdicForm s k (evenHalf x) +
      pow2Neg (s + 2) * riesz2AdicForm s k (oddHalf x) +
      dyad 1 1 * muForm k (evenHalf x) * muForm k (oddHalf x) := by
  unfold riesz2AdicForm
  rw [sumFin_pow2_succ]
  have hinner : ∀ (f : Fin (2 ^ (k + 1)) → ZHalf),
      sumFin f = sumFin (fun j : Fin (2 ^ k) => f ⟨2 * j.val, by have := j.isLt; rw [Nat.pow_succ]; omega⟩) +
                 sumFin (fun j : Fin (2 ^ k) => f ⟨2 * j.val + 1, by have := j.isLt; rw [Nat.pow_succ]; omega⟩) :=
    fun f => sumFin_pow2_succ f
  rw [sumFin_congr (fun i => hinner _), sumFin_congr (fun i => hinner _), sumFin_add, sumFin_add]
  have hEE : ∀ a b : Nat, riesz2AdicKernel s (2 * a) (2 * b) = pow2Neg s * riesz2AdicKernel s a b := fun a b => by
    unfold riesz2AdicKernel
    by_cases hab : a = b
    · subst hab; simp [mul_zero]
    · have h2 : 2 * a ≠ 2 * b := by omega
      simp only [hab, h2, ↓reduceIte]
      rw [v2Nat_xor_eq_absDiff, v2Nat_xor_eq_absDiff, absDiff_two_mul]
      have hd : absDiff a b ≠ 0 := by unfold absDiff; split <;> omega
      rw [v2Nat_two_mul hd, Nat.mul_add, Nat.mul_one, pow2Neg_add]
  have hOO : ∀ a b : Nat, riesz2AdicKernel s (2 * a + 1) (2 * b + 1) = pow2Neg s * riesz2AdicKernel s a b := fun a b => by
    unfold riesz2AdicKernel
    by_cases hab : a = b
    · subst hab; simp [mul_zero]
    · have h2 : 2 * a + 1 ≠ 2 * b + 1 := by omega
      simp only [hab, h2, ↓reduceIte]
      rw [v2Nat_xor_eq_absDiff, v2Nat_xor_eq_absDiff, absDiff_two_mul_add_one]
      have hd : absDiff a b ≠ 0 := by unfold absDiff; split <;> omega
      rw [v2Nat_two_mul hd, Nat.mul_add, Nat.mul_one, pow2Neg_add]
  have hEO : ∀ a b : Nat, riesz2AdicKernel s (2 * a) (2 * b + 1) = 1 := fun a b => by
    unfold riesz2AdicKernel
    have hne : 2 * a ≠ 2 * b + 1 := by omega
    simp only [hne, ↓reduceIte]
    rw [v2Nat_xor_eq_absDiff, v2Nat_odd _ (absDiff_even_odd_mod2 a b), Nat.mul_zero]; rfl
  have hOE : ∀ a b : Nat, riesz2AdicKernel s (2 * a + 1) (2 * b) = 1 := fun a b => by
    unfold riesz2AdicKernel
    have hne : 2 * a + 1 ≠ 2 * b := by omega
    simp only [hne, ↓reduceIte]
    rw [v2Nat_xor_eq_absDiff, v2Nat_odd _ (absDiff_odd_even_mod2 a b), Nat.mul_zero]; rfl
  have sEE : sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               riesz2AdicKernel s (2 * i.val) (2 * j.val) * evenHalf x i * evenHalf x j)) =
             pow2Neg s * sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               riesz2AdicKernel s i.val j.val * evenHalf x i * evenHalf x j)) := by
    rw [← sumFin_mul_left]; apply sumFin_congr; intro i
    rw [← sumFin_mul_left]; apply sumFin_congr; intro j
    rw [hEE i.val j.val, mul_assoc (pow2Neg s), mul_assoc (pow2Neg s)]
  have sOO : sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               riesz2AdicKernel s (2 * i.val + 1) (2 * j.val + 1) * oddHalf x i * oddHalf x j)) =
             pow2Neg s * sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               riesz2AdicKernel s i.val j.val * oddHalf x i * oddHalf x j)) := by
    rw [← sumFin_mul_left]; apply sumFin_congr; intro i
    rw [← sumFin_mul_left]; apply sumFin_congr; intro j
    rw [hOO i.val j.val, mul_assoc (pow2Neg s), mul_assoc (pow2Neg s)]
  have sEO : sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               riesz2AdicKernel s (2 * i.val) (2 * j.val + 1) * evenHalf x i * oddHalf x j)) =
             sumFin (evenHalf x) * sumFin (oddHalf x) := by
    rw [← sumFin_mul_right]; apply sumFin_congr; intro i
    rw [← sumFin_mul_left]; apply sumFin_congr; intro j
    rw [hEO i.val j.val, one_mul]
  have sOE : sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
               riesz2AdicKernel s (2 * i.val + 1) (2 * j.val) * oddHalf x i * evenHalf x j)) =
             sumFin (evenHalf x) * sumFin (oddHalf x) := by
    rw [mul_comm (sumFin (evenHalf x)), ← sumFin_mul_right]; apply sumFin_congr; intro i
    rw [← sumFin_mul_left]; apply sumFin_congr; intro j
    rw [hOE i.val j.val, one_mul]
  change pow2Neg (2 * (k + 1)) *
    ((sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
        riesz2AdicKernel s (2 * i.val) (2 * j.val) * evenHalf x i * evenHalf x j)) +
      sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
        riesz2AdicKernel s (2 * i.val) (2 * j.val + 1) * evenHalf x i * oddHalf x j))) +
     (sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
        riesz2AdicKernel s (2 * i.val + 1) (2 * j.val) * oddHalf x i * evenHalf x j)) +
      sumFin (fun i : Fin (2 ^ k) => sumFin (fun j : Fin (2 ^ k) =>
        riesz2AdicKernel s (2 * i.val + 1) (2 * j.val + 1) * oddHalf x i * oddHalf x j)))) = _
  rw [sEE, sOO, sEO, sOE]
  have hp2 : pow2Neg (2 * (k + 1)) = dyad 1 2 * pow2Neg (2 * k) := by
    rw [show 2 * (k + 1) = 2 + 2 * k by omega]; exact pow2Neg_add 2 (2 * k)
  have hps : dyad 1 2 * pow2Neg s = pow2Neg (s + 2) := by
    rw [show s + 2 = 2 + s by omega]; exact (pow2Neg_add 2 s).symm
  have hhalf : dyad 1 2 + dyad 1 2 = dyad 1 1 := by decide
  have hpk : pow2Neg (2 * k) = pow2Neg k * pow2Neg k := by
    rw [show 2 * k = k + k by omega]; exact pow2Neg_add k k
  unfold muForm
  rw [hp2]
  have hrearr : ∀ a b c : ZHalf, (a + c) + (c + b) = (a + b) + (c + c) := fun a b c => by
    rw [add_comm c b]; exact add_four_swap a c b c
  rw [hrearr, mul_add, mul_add]
  have hscale : ∀ A : ZHalf, (dyad 1 2 * pow2Neg (2 * k)) * (pow2Neg s * A) =
                pow2Neg (s + 2) * (pow2Neg (2 * k) * A) := fun A => by
    calc (dyad 1 2 * pow2Neg (2 * k)) * (pow2Neg s * A)
        = (dyad 1 2 * (pow2Neg (2 * k) * pow2Neg s)) * A := by simp [mul_assoc]
      _ = (dyad 1 2 * (pow2Neg s * pow2Neg (2 * k))) * A := by rw [mul_comm (pow2Neg (2 * k))]
      _ = (dyad 1 2 * pow2Neg s) * (pow2Neg (2 * k) * A) := by simp [mul_assoc]
      _ = pow2Neg (s + 2) * (pow2Neg (2 * k) * A) := by rw [hps]
  have hcross : (dyad 1 2 * pow2Neg (2 * k)) * (sumFin (evenHalf x) * sumFin (oddHalf x) +
                                               sumFin (evenHalf x) * sumFin (oddHalf x)) =
                dyad 1 1 * (pow2Neg k * sumFin (evenHalf x)) * (pow2Neg k * sumFin (oddHalf x)) := by
    calc (dyad 1 2 * pow2Neg (2 * k)) * (sumFin (evenHalf x) * sumFin (oddHalf x) +
                                         sumFin (evenHalf x) * sumFin (oddHalf x))
        = (dyad 1 2 + dyad 1 2) * (pow2Neg (2 * k) * (sumFin (evenHalf x) * sumFin (oddHalf x))) := by
            rw [mul_add, add_mul, mul_assoc (dyad 1 2)]
      _ = dyad 1 1 * ((pow2Neg k * pow2Neg k) * (sumFin (evenHalf x) * sumFin (oddHalf x))) := by
            rw [hhalf, hpk]
      _ = dyad 1 1 * (pow2Neg k * (pow2Neg k * sumFin (evenHalf x)) * sumFin (oddHalf x)) := by
            simp [mul_assoc]
      _ = dyad 1 1 * (pow2Neg k * (sumFin (evenHalf x) * pow2Neg k) * sumFin (oddHalf x)) := by
            rw [mul_comm (pow2Neg k) (sumFin (evenHalf x))]
      _ = dyad 1 1 * (pow2Neg k * sumFin (evenHalf x)) * (pow2Neg k * sumFin (oddHalf x)) := by
            simp [mul_assoc]
  rw [hscale, hscale, hcross]

theorem sysRiesz_Q_eq (s k : Nat) (x : Fin (2 ^ k) → ZHalf) :
    (sysRiesz s).Q k x = -(ofInt (Dyadic.pow2Int (s + 1) - 1)) * riesz2AdicForm s k x := by
  induction k with
  | zero =>
    unfold BQS.Q BQS.B sysRiesz
    rw [riesz2AdicForm_zero, zero_mul, zero_mul, mul_zero]
  | succ k ih =>
    unfold BQS.Q BQS.B
    change (sysRiesz s).h00 * (sysRiesz s).Q k (evenHalf x) +
           (sysRiesz s).h01 * ((sysRiesz s).B k (evenHalf x) (oddHalf x) + (sysRiesz s).B k (oddHalf x) (evenHalf x)) +
           (sysRiesz s).h11 * (sysRiesz s).Q k (oddHalf x) +
           quadForm (sysRiesz s).C (pairVec ((sysRiesz s).L k (evenHalf x)) ((sysRiesz s).L k (oddHalf x))) = _
    rw [ih (evenHalf x), ih (oddHalf x), riesz2AdicForm_succ]
    have hh01 : (sysRiesz s).h01 = 0 := rfl
    rw [hh01, zero_mul, add_zero]
    have hCquad : quadForm (sysRiesz s).C (pairVec ((sysRiesz s).L k (evenHalf x)) ((sysRiesz s).L k (oddHalf x))) =
                  (-(ofInt (Dyadic.pow2Int (s + 1) - 1))) * (dyad 1 1 * muForm k (evenHalf x) * muForm k (oddHalf x)) := by
      rw [quadForm_fin2]
      have p0 : pairVec ((sysRiesz s).L k (evenHalf x)) ((sysRiesz s).L k (oddHalf x)) ⟨0, by decide⟩ = muForm k (evenHalf x) := by
        unfold pairVec; simp; exact sysRiesz_L_eq s k (evenHalf x)
      have p1 : pairVec ((sysRiesz s).L k (evenHalf x)) ((sysRiesz s).L k (oddHalf x)) ⟨1, by decide⟩ = muForm k (oddHalf x) := by
        unfold pairVec; simp; exact sysRiesz_L_eq s k (oddHalf x)
      rw [p0, p1]
      have c00 : (sysRiesz s).C ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := rfl
      have c11 : (sysRiesz s).C ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := rfl
      have c01 : (sysRiesz s).C ⟨0, by decide⟩ ⟨1, by decide⟩ = dyad (-(Dyadic.pow2Int (s + 1) - 1)) 2 := rfl
      have c10 : (sysRiesz s).C ⟨1, by decide⟩ ⟨0, by decide⟩ = dyad (-(Dyadic.pow2Int (s + 1) - 1)) 2 := rfl
      rw [c00, c11, c01, c10]
      simp only [zero_mul, zero_add, add_zero]
      have hcomm : dyad (-(Dyadic.pow2Int (s + 1) - 1)) 2 * muForm k (oddHalf x) * muForm k (evenHalf x) =
                   dyad (-(Dyadic.pow2Int (s + 1) - 1)) 2 * muForm k (evenHalf x) * muForm k (oddHalf x) := by
        rw [mul_assoc, mul_comm (muForm k (oddHalf x)), ← mul_assoc]
      rw [hcomm, ← add_mul, ← add_mul, ← mul_assoc, ← mul_assoc]
      congr 1; congr 1
      change Quotient.mk Dyadic.instSetoid ⟨-(Dyadic.pow2Int (s + 1) - 1), 2⟩ +
             Quotient.mk Dyadic.instSetoid ⟨-(Dyadic.pow2Int (s + 1) - 1), 2⟩ =
             Quotient.mk Dyadic.instSetoid ⟨-(Dyadic.pow2Int (s + 1) - 1), 0⟩ *
             Quotient.mk Dyadic.instSetoid ⟨1, 1⟩
      rw [ZHalf.mk_add_eq]
      apply Quotient.sound
      show ((-(Dyadic.pow2Int (s + 1) - 1)) * Dyadic.pow2Int 2 +
            (-(Dyadic.pow2Int (s + 1) - 1)) * Dyadic.pow2Int 2) * Dyadic.pow2Int (0 + 1) =
           ((-(Dyadic.pow2Int (s + 1) - 1)) * 1) * Dyadic.pow2Int (2 + 2)
      have h2 : Dyadic.pow2Int 2 = 4 := rfl
      have h1 : Dyadic.pow2Int (0 + 1) = 2 := rfl
      have h4 : Dyadic.pow2Int (2 + 2) = 16 := rfl
      rw [h2, h1, h4]; omega
    rw [hCquad]
    change pow2Neg (s + 2) * (-(ofInt (Dyadic.pow2Int (s + 1) - 1)) * riesz2AdicForm s k (evenHalf x)) +
           pow2Neg (s + 2) * (-(ofInt (Dyadic.pow2Int (s + 1) - 1)) * riesz2AdicForm s k (oddHalf x)) +
           (-(ofInt (Dyadic.pow2Int (s + 1) - 1))) * (dyad 1 1 * muForm k (evenHalf x) * muForm k (oddHalf x)) = _
    rw [mul_add, mul_add]
    congr 1; congr 1
    · rw [← mul_assoc, mul_comm (pow2Neg (s + 2)), mul_assoc]
    · rw [← mul_assoc, mul_comm (pow2Neg (s + 2)), mul_assoc]

/-- THEOREM 1 (Infinite 2-Parameter Sharp 2-Adic Riesz Strict Positivity):
    For ALL integer exponents `s ≥ 1`, ALL resolutions `k : Nat`, and ALL nonzero
    `x : Fin (2^k) → ZHalf`:
      `2^s * μ_k(x)^2 - (2^(s+1) - 1) * R_k^{(s)}(x) > 0`. -/
theorem thm_riesz2Adic_strict_pd (s : Nat) (hs : 1 ≤ s) (k : Nat)
    (x : Fin (2 ^ k) → ZHalf) (hx : ∃ i, x i ≠ 0) :
    0 < pow2Nat s * (muForm k x * muForm k x) -
        ofInt (Dyadic.pow2Int (s + 1) - 1) * riesz2AdicForm s k x := by
  have h := soundness_strict_pd (sysRiesz s) (WRiesz s) (certRiesz s) (checkStrictPD_riesz_all s hs) k x hx
  rw [sysRiesz_Q_eq] at h
  have hW : quadForm (WRiesz s) ((sysRiesz s).L k x) = pow2Nat s * (muForm k x * muForm k x) := by
    unfold quadForm quadBilin WRiesz mat1
    rw [sumFin_fin1, sumFin_fin1, sysRiesz_L_eq, mul_assoc]
  rw [hW, add_comm, neg_mul, ← sub_eq_add_neg] at h
  exact h

theorem riesz2Adic_ones_eval (s k : Nat) :
    pow2Nat s * (muForm k (vecOnes (2 ^ k)) * muForm k (vecOnes (2 ^ k))) -
    ofInt (Dyadic.pow2Int (s + 1) - 1) * riesz2AdicForm s k (vecOnes (2 ^ k)) =
    pow2Nat s * pow2Neg (k * (s + 1)) := by
  induction k with
  | zero =>
    rw [muForm_ones, riesz2AdicForm_zero, mul_zero, one_mul, Nat.zero_mul]
    have h0 : pow2Neg 0 = 1 := rfl
    rw [h0, mul_one, sub_eq_add_neg, neg_zero, add_zero]
  | succ k ih =>
    have hE : evenHalf (vecOnes (2 ^ (k + 1))) = vecOnes (2 ^ k) := rfl
    have hO : oddHalf (vecOnes (2 ^ (k + 1))) = vecOnes (2 ^ k) := rfl
    rw [muForm_ones, one_mul, mul_one, riesz2AdicForm_succ, hE, hO, muForm_ones, mul_one, mul_one]
    have hR : ofInt (Dyadic.pow2Int (s + 1) - 1) * riesz2AdicForm s k (vecOnes (2 ^ k)) =
              pow2Nat s - pow2Nat s * pow2Neg (k * (s + 1)) := by
      rw [muForm_ones, one_mul, mul_one] at ih
      have hsub : ∀ a b c : ZHalf, a - b = c → b = a - c := fun a b c h => by
        rw [← h, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, ← add_assoc, add_neg_cancel, zero_add]
      exact hsub _ _ _ ih
    rw [mul_add, mul_add]
    have hcomm : ∀ A : ZHalf, ofInt (Dyadic.pow2Int (s + 1) - 1) * (pow2Neg (s + 2) * A) =
                 pow2Neg (s + 2) * (ofInt (Dyadic.pow2Int (s + 1) - 1) * A) := fun A => by
      rw [← mul_assoc, mul_comm (ofInt _), mul_assoc]
    rw [hcomm, hR]
    have h2 : pow2Neg (s + 2) + pow2Neg (s + 2) = pow2Neg (s + 1) := by
      change Quotient.mk Dyadic.instSetoid ⟨1, s + 2⟩ + Quotient.mk Dyadic.instSetoid ⟨1, s + 2⟩ =
             Quotient.mk Dyadic.instSetoid ⟨1, s + 1⟩
      rw [ZHalf.mk_add_eq]
      apply Quotient.sound
      show (1 * Dyadic.pow2Int (s + 2) + 1 * Dyadic.pow2Int (s + 2)) * Dyadic.pow2Int (s + 1) =
           1 * Dyadic.pow2Int ((s + 2) + (s + 2))
      simp only [Int.one_mul]
      rw [Dyadic.pow2Int_add (s + 2) (s + 2), show s + 2 = (s + 1) + 1 by omega, Dyadic.pow2Int_succ]
      generalize Dyadic.pow2Int (s + 1) = P
      have h4 : P * 2 + P * 2 = 2 * (P * 2) := by omega
      rw [h4, Int.mul_assoc 2 (P * 2) P, Int.mul_comm (P * 2) P, ← Int.mul_assoc 2 P (P * 2), Int.mul_comm 2 P]
    have hcomb : pow2Neg (s + 2) * (pow2Nat s - pow2Nat s * pow2Neg (k * (s + 1))) +
                 pow2Neg (s + 2) * (pow2Nat s - pow2Nat s * pow2Neg (k * (s + 1))) =
                 pow2Neg (s + 1) * pow2Nat s - pow2Nat s * pow2Neg ((k + 1) * (s + 1)) := by
      rw [← add_mul, h2, mul_sub]
      congr 1
      rw [← mul_assoc, mul_comm (pow2Neg (s + 1)) (pow2Nat s), mul_assoc, ← pow2Neg_add]
      congr 1; congr 1; rw [Nat.succ_mul, Nat.add_comm]
    rw [hcomb]
    have hcancel : pow2Neg (s + 1) * pow2Nat s + ofInt (Dyadic.pow2Int (s + 1) - 1) * dyad 1 1 = pow2Nat s := by
      have h1 : pow2Neg (s + 1) * pow2Nat s = dyad 1 1 := by
        apply Quotient.sound
        show (1 * Dyadic.pow2Int s) * Dyadic.pow2Int 1 = 1 * Dyadic.pow2Int (s + 1 + 0)
        rw [Int.one_mul, Int.one_mul, Nat.add_zero, Dyadic.pow2Int_succ]; rfl
      rw [h1]
      change Quotient.mk Dyadic.instSetoid ⟨1, 1⟩ +
             Quotient.mk Dyadic.instSetoid ⟨(Dyadic.pow2Int (s + 1) - 1) * 1, 0 + 1⟩ =
             Quotient.mk Dyadic.instSetoid ⟨Dyadic.pow2Int s, 0⟩
      rw [ZHalf.mk_add_eq]
      apply Quotient.sound
      show (1 * Dyadic.pow2Int (0 + 1) + (Dyadic.pow2Int (s + 1) - 1) * 1 * Dyadic.pow2Int 1) * Dyadic.pow2Int 0 =
           Dyadic.pow2Int s * Dyadic.pow2Int (1 + (0 + 1))
      have h0 : Dyadic.pow2Int 0 = 1 := rfl
      have h01 : Dyadic.pow2Int (0 + 1) = 2 := rfl
      have h2' : Dyadic.pow2Int (1 + (0 + 1)) = 4 := rfl
      rw [h2', h01, h0, Dyadic.pow2Int_succ]
      omega
    have hfin : ∀ a b c d : ZHalf, a + c = d → d - (a - b + c) = b := fun a b c d h => by
      rw [← h, sub_eq_add_neg, sub_eq_add_neg, add_assoc a (-b) c, add_comm (-b) c,
          ← add_assoc a c (-b), neg_add, neg_neg, ← add_assoc, add_neg_cancel, zero_add]
    exact hfin _ _ _ _ hcancel

/-- INFINITE SHARPNESS THEOREM FOR THEOREM 1:
    For EVERY `s ≥ 1` and EVERY dyadic reduction `c = 2^s - 2^{-r} < 2^s`,
    there exists `k` and nonzero `x` (`vecOnes`) making the form STRICTLY NEGATIVE! -/
theorem thm_riesz2Adic_sharp (s r : Nat) (hs : 1 ≤ s) :
    ∃ (k : Nat) (x : Fin (2 ^ k) → ZHalf), (∃ i, x i ≠ 0) ∧
      (pow2Nat s - pow2Neg r) * (muForm k x * muForm k x) -
      ofInt (Dyadic.pow2Int (s + 1) - 1) * riesz2AdicForm s k x < 0 := by
  refine ⟨s + r + 1, vecOnes (2 ^ (s + r + 1)), ⟨⟨0, Nat.two_pow_pos _⟩, by show (1 : ZHalf) ≠ 0; decide⟩, ?_⟩
  rw [sub_mul, sub_eq_add_neg, sub_eq_add_neg]
  have hre : ∀ a b c : ZHalf, (a + -b) + -c = (a - c) - b := fun a b c => by
    rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, add_comm (-b) (-c), ← add_assoc]
  rw [hre, riesz2Adic_ones_eval, muForm_ones, one_mul, mul_one]
  rw [← neg_pos_iff]
  have hnegsub : -(pow2Nat s * pow2Neg ((s + r + 1) * (s + 1)) - pow2Neg r) =
                 pow2Neg r - pow2Nat s * pow2Neg ((s + r + 1) * (s + 1)) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]
  rw [hnegsub, sub_pos_iff]
  change Dyadic.lt ⟨Dyadic.pow2Int s * 1, 0 + (s + r + 1) * (s + 1)⟩ ⟨1, r⟩
  unfold Dyadic.lt
  simp only [Int.mul_one, Int.one_mul, Nat.zero_add, ← Dyadic.pow2Int_add]
  have hexp : s + r < (s + r + 1) * (s + 1) := by
    have : (s + r + 1) * 1 ≤ (s + r + 1) * (s + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hmono : ∀ a b : Nat, a < b → Dyadic.pow2Int a < Dyadic.pow2Int b := by
    intro a b hab
    obtain ⟨d, hd⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
    subst hd
    rw [show a + d + 1 = a + (d + 1) by omega, Dyadic.pow2Int_add, Dyadic.pow2Int_succ]
    have ha := Dyadic.pow2Int_pos a
    have hd' := Dyadic.pow2Int_pos d
    have hmul := Int.mul_lt_mul_of_pos_left (show (1 : Int) < Dyadic.pow2Int d * 2 by omega) ha
    rw [Int.mul_one] at hmul
    exact hmul
  exact hmono _ _ hexp

/-! ### THEOREM 2: Sharp Discrete Archimedean-Monna Distance Form via Mode-2 Boundary-Kernel Lifting -/

/-- Direct-induction obstruction: naive `W = [[1/2, 0], [0, 0]]` produces an INDEFINITE `Δ`
    (principal 2×2 minor on indices `{0, 3}` has determinant `-1/64 < 0`)! -/
theorem monnaArch_direct_induction_fails :
    deltaMat sysArch WArchTarget ⟨0, by decide⟩ ⟨0, by decide⟩ *
    deltaMat sysArch WArchTarget ⟨3, by decide⟩ ⟨3, by decide⟩ -
    deltaMat sysArch WArchTarget ⟨0, by decide⟩ ⟨3, by decide⟩ *
    deltaMat sysArch WArchTarget ⟨3, by decide⟩ ⟨0, by decide⟩ < 0 := by decide

/-- THEOREM 2 (Sharp Discrete Archimedean-Monna Distance Form Strict Positivity):
    For ALL `k : Nat` and ALL nonzero `x : Fin (2^k) → ZHalf`:
      `(1/2) * μ_k(x)^2 - A_k(x) > 0`. -/
theorem thm_monnaArch_strict_pd (k : Nat) (x : Fin (2 ^ k) → ZHalf) (hx : ∃ i, x i ≠ 0) :
    0 < dyad 1 1 * (muForm k x * muForm k x) - monnaArchForm k x := by
  have h := soundness_boundary_strict_pd sysArch WArchTarget certArch (dyad 1 1) checkBoundaryStrictPD_arch k x hx
  rw [sysArch_Q_eq] at h
  have hL := monna_L_eq sysArch rfl rfl rfl k x
  have hW : quadForm WArchTarget (sysArch.L k x) = dyad 1 1 * (muForm k x * muForm k x) := by
    rw [quadForm_fin2, hL.1, hL.2]
    change (dyad 1 1 * muForm k x * muForm k x + 0 * muForm k x * nuForm k x) +
           (0 * nuForm k x * muForm k x + 0 * nuForm k x * nuForm k x) = _
    simp only [zero_mul, add_zero, mul_assoc]
  rw [hW, add_comm, ← sub_eq_add_neg] at h
  exact h

/-- Exact bridge: `Q sysAdelic k x = -3 * R_k^{(1)}(x) - 2 * A_k(x)`. -/
theorem sysAdelic_Q_eq (k : Nat) (x : Fin (2 ^ k) → ZHalf) :
    sysAdelic.Q k x = -(3 : ZHalf) * riesz2AdicForm 1 k x - 2 * monnaArchForm k x := by
  induction k with
  | zero =>
    unfold BQS.Q BQS.B sysAdelic
    rw [riesz2AdicForm_zero, monnaArchForm_zero, zero_mul, zero_mul, mul_zero, mul_zero, sub_self]
  | succ k ih =>
    unfold BQS.Q BQS.B
    change dyad 1 3 * sysAdelic.Q k (evenHalf x) +
           0 * (sysAdelic.B k (evenHalf x) (oddHalf x) + sysAdelic.B k (oddHalf x) (evenHalf x)) +
           dyad 1 3 * sysAdelic.Q k (oddHalf x) +
           quadForm sysAdelic.C (pairVec (sysAdelic.L k (evenHalf x)) (sysAdelic.L k (oddHalf x))) = _
    rw [ih (evenHalf x), ih (oddHalf x), zero_mul, add_zero, riesz2AdicForm_succ, monnaArchForm_succ]
    have hLe := monna_L_eq sysAdelic rfl rfl rfl k (evenHalf x)
    have hLo := monna_L_eq sysAdelic rfl rfl rfl k (oddHalf x)
    rw [quadForm_fin4]
    have pv0 : pairVec (sysAdelic.L k (evenHalf x)) (sysAdelic.L k (oddHalf x)) ⟨0, by decide⟩ = muForm k (evenHalf x) := by
      unfold pairVec; simp; exact hLe.1
    have pv1 : pairVec (sysAdelic.L k (evenHalf x)) (sysAdelic.L k (oddHalf x)) ⟨1, by decide⟩ = nuForm k (evenHalf x) := by
      unfold pairVec; simp; exact hLe.2
    have pv2 : pairVec (sysAdelic.L k (evenHalf x)) (sysAdelic.L k (oddHalf x)) ⟨2, by decide⟩ = muForm k (oddHalf x) := by
      unfold pairVec; simp; exact hLo.1
    have pv3 : pairVec (sysAdelic.L k (evenHalf x)) (sysAdelic.L k (oddHalf x)) ⟨3, by decide⟩ = nuForm k (oddHalf x) := by
      unfold pairVec; simp; exact hLo.2
    rw [pv0, pv1, pv2, pv3]
    change dyad 1 3 * (-(3 : ZHalf) * riesz2AdicForm 1 k (evenHalf x) - 2 * monnaArchForm k (evenHalf x)) +
           dyad 1 3 * (-(3 : ZHalf) * riesz2AdicForm 1 k (oddHalf x) - 2 * monnaArchForm k (oddHalf x)) +
      ((0 * muForm k (evenHalf x) * muForm k (evenHalf x) + 0 * muForm k (evenHalf x) * nuForm k (evenHalf x) +
        dyad (-1) 0 * muForm k (evenHalf x) * muForm k (oddHalf x) + dyad (-1) 2 * muForm k (evenHalf x) * nuForm k (oddHalf x)) +
       (0 * nuForm k (evenHalf x) * muForm k (evenHalf x) + 0 * nuForm k (evenHalf x) * nuForm k (evenHalf x) +
        dyad 1 2 * nuForm k (evenHalf x) * muForm k (oddHalf x) + 0 * nuForm k (evenHalf x) * nuForm k (oddHalf x)) +
       (dyad (-1) 0 * muForm k (oddHalf x) * muForm k (evenHalf x) + dyad 1 2 * muForm k (oddHalf x) * nuForm k (evenHalf x) +
        0 * muForm k (oddHalf x) * muForm k (oddHalf x) + 0 * muForm k (oddHalf x) * nuForm k (oddHalf x)) +
       (dyad (-1) 2 * nuForm k (oddHalf x) * muForm k (evenHalf x) + 0 * nuForm k (oddHalf x) * nuForm k (evenHalf x) +
        0 * nuForm k (oddHalf x) * muForm k (oddHalf x) + 0 * nuForm k (oddHalf x) * nuForm k (oddHalf x))) = _
    simp only [zero_mul, zero_add, add_zero]
    have hp13 : pow2Neg (1 + 2) = dyad 1 3 := rfl
    rw [hp13]
    generalize riesz2AdicForm 1 k (evenHalf x) = r0
    generalize riesz2AdicForm 1 k (oddHalf x) = r1
    generalize monnaArchForm k (evenHalf x) = a0
    generalize monnaArchForm k (oddHalf x) = a1
    generalize muForm k (evenHalf x) = m0
    generalize nuForm k (evenHalf x) = n0
    generalize muForm k (oddHalf x) = m1
    generalize nuForm k (oddHalf x) = n1
    have hcoeff1 : dyad (-1) 0 + dyad (-1) 0 = -(3 : ZHalf) * dyad 1 1 + -(2 * dyad 1 2) := by decide
    have hcoeff2 : dyad (-1) 2 + dyad (-1) 2 = -(2 * dyad 1 2) := by decide
    have hcoeff3 : dyad 1 2 + dyad 1 2 = 2 * dyad 1 2 := by decide
    -- Simplify quadratic part on LHS
    have hc1 : dyad (-1) 0 * m1 * m0 = dyad (-1) 0 * m0 * m1 := by rw [mul_assoc, mul_comm m1 m0, ← mul_assoc]
    have hc2 : dyad 1 2 * m1 * n0 = dyad 1 2 * n0 * m1 := by rw [mul_assoc, mul_comm m1 n0, ← mul_assoc]
    have hc3 : dyad (-1) 2 * n1 * m0 = dyad (-1) 2 * m0 * n1 := by rw [mul_assoc, mul_comm n1 m0, ← mul_assoc]
    rw [hc1, hc2, hc3]
    have hq_lhs :
        ((dyad (-1) 0 * m0 * m1 + dyad (-1) 2 * m0 * n1) + dyad 1 2 * n0 * m1 +
         (dyad (-1) 0 * m0 * m1 + dyad 1 2 * n0 * m1) + dyad (-1) 2 * m0 * n1) =
        (-(3 : ZHalf) * (dyad 1 1 * m0 * m1)) +
        (-(2 * (dyad 1 2 * m0 * m1)) + -(2 * (dyad 1 2 * m0 * n1)) + 2 * (dyad 1 2 * n0 * m1)) := by
      have ha : dyad (-1) 0 * m0 * m1 + dyad (-1) 0 * m0 * m1 =
                -(3 : ZHalf) * (dyad 1 1 * m0 * m1) + -(2 * (dyad 1 2 * m0 * m1)) := by
        rw [← add_mul, ← add_mul, hcoeff1, add_mul, add_mul]
        simp only [neg_mul, mul_assoc]
      have hb : dyad (-1) 2 * m0 * n1 + dyad (-1) 2 * m0 * n1 = -(2 * (dyad 1 2 * m0 * n1)) := by
        rw [← add_mul, ← add_mul, hcoeff2]
        simp only [neg_mul, mul_assoc]
      have hc : dyad 1 2 * n0 * m1 + dyad 1 2 * n0 * m1 = 2 * (dyad 1 2 * n0 * m1) := by
        rw [← add_mul, ← add_mul, hcoeff3]
        simp only [mul_assoc]
      rw [← hb, ← hc]
      have hstep :
          ((dyad (-1) 0 * m0 * m1 + dyad (-1) 2 * m0 * n1) + dyad 1 2 * n0 * m1 +
           (dyad (-1) 0 * m0 * m1 + dyad 1 2 * n0 * m1) + dyad (-1) 2 * m0 * n1) =
          (dyad (-1) 0 * m0 * m1 + dyad (-1) 0 * m0 * m1) +
          ((dyad (-1) 2 * m0 * n1 + dyad (-1) 2 * m0 * n1) +
           (dyad 1 2 * n0 * m1 + dyad 1 2 * n0 * m1)) := by
        generalize dyad (-1) 0 * m0 * m1 = X
        generalize dyad (-1) 2 * m0 * n1 = Y
        generalize dyad 1 2 * n0 * m1 = Z
        calc (X + Y) + Z + (X + Z) + Y
            = ((X + Y) + (X + Z)) + (Z + Y) := by
                rw [add_assoc (X + Y) Z (X + Z), add_comm Z (X + Z), ← add_assoc (X + Y), add_assoc]
          _ = ((X + X) + (Y + Z)) + (Z + Y) := by rw [add_four_swap X Y X Z]
          _ = (X + X) + ((Y + Z) + (Y + Z)) := by rw [add_assoc, add_comm Z Y]
          _ = (X + X) + ((Y + Y) + (Z + Z)) := by rw [add_four_swap Y Z Y Z]
      rw [hstep, ha, add_assoc, ← add_assoc (-(2 * (dyad 1 2 * m0 * m1)))]
    rw [hq_lhs]
    -- Now combine LHS and RHS linear combinations of r0, r1, a0, a1, m0*m1, m0*n1, n0*m1!
    have hmul_comm1 : ∀ c u : ZHalf, dyad 1 3 * (c * u) = c * (dyad 1 3 * u) := fun c u => by
      rw [← mul_assoc, mul_comm (dyad 1 3) c, mul_assoc]
    rw [mul_sub, mul_sub, hmul_comm1, hmul_comm1, hmul_comm1, hmul_comm1]
    simp only [mul_add, sub_eq_add_neg, neg_add, mul_neg, neg_neg]
    generalize -(3 : ZHalf) * (dyad 1 3 * r0) = R0
    generalize -(3 : ZHalf) * (dyad 1 3 * r1) = R1
    generalize -(2 * (dyad 1 3 * a0)) = A0
    generalize -(2 * (dyad 1 3 * a1)) = A1
    generalize -(3 : ZHalf) * (dyad 1 1 * m0 * m1) = M_R
    generalize -(2 * (dyad 1 2 * m0 * m1)) = M_A
    generalize -(2 * (dyad 1 2 * m0 * n1)) = MN_A
    generalize 2 * (dyad 1 2 * n0 * m1) = NM_A
    calc (R0 + A0) + (R1 + A1) + (M_R + (M_A + MN_A + NM_A))
        = ((R0 + R1) + (A0 + A1)) + (M_R + (M_A + MN_A + NM_A)) := by rw [add_four_swap R0 A0 R1 A1]
      _ = ((R0 + R1) + M_R) + ((A0 + A1) + (M_A + MN_A + NM_A)) := add_four_swap (R0 + R1) (A0 + A1) M_R _
      _ = (R0 + R1 + M_R) + (A0 + A1 + M_A + MN_A + NM_A) := by
            congr 1
            rw [← add_assoc (A0 + A1), ← add_assoc (A0 + A1)]

/-- THEOREM 3 (Coupled Non-Commuting Adelic-Monna-Dipole Strict Positivity):
    For ALL `k : Nat` and ALL nonzero `x : Fin (2^k) → ZHalf`:
      `3 * μ_k(x)^2 - (μ_k(x) - 2*ν_k(x))^2 - 3 * R_k^{(1)}(x) - 2 * A_k(x) > 0`. -/
theorem thm_adelic_dipole_strict_pd (k : Nat) (x : Fin (2 ^ k) → ZHalf) (hx : ∃ i, x i ≠ 0) :
    0 < 3 * (muForm k x * muForm k x) -
        (muForm k x - 2 * nuForm k x) * (muForm k x - 2 * nuForm k x) -
        3 * riesz2AdicForm 1 k x - 2 * monnaArchForm k x := by
  have h := soundness_strict_pd sysAdelic WAdelic certAdelic checkStrictPD_adelic k x hx
  rw [sysAdelic_Q_eq] at h
  have hL := monna_L_eq sysAdelic rfl rfl rfl k x
  have hW : quadForm WAdelic (sysAdelic.L k x) =
            3 * (muForm k x * muForm k x) -
            (muForm k x - 2 * nuForm k x) * (muForm k x - 2 * nuForm k x) := by
    rw [quadForm_fin2, hL.1, hL.2]
    change (2 * muForm k x * muForm k x + 2 * muForm k x * nuForm k x) +
           (2 * nuForm k x * muForm k x + (-4) * nuForm k x * nuForm k x) = _
    generalize muForm k x = m
    generalize nuForm k x = n
    have h22 : (2 : ZHalf) + 2 = 4 := by decide
    have h31 : (3 : ZHalf) - 1 = 2 := by decide
    have h2m2 : (2 : ZHalf) * 2 = 4 := by decide
    have hsq : (m - 2 * n) * (m - 2 * n) = m * m + (-(4 * (m * n)) + 4 * (n * n)) := by
      rw [sub_mul, mul_sub, mul_sub]
      have t1 : m * (2 * n) = 2 * (m * n) := by rw [← mul_assoc, mul_comm m 2, mul_assoc]
      have t2 : (2 * n) * m = 2 * (m * n) := by rw [mul_assoc, mul_comm n m]
      have t3 : (2 * n) * (2 * n) = 4 * (n * n) := by
        calc (2 * n) * (2 * n) = (2 * (n * 2)) * n := by simp [mul_assoc]
          _ = (2 * (2 * n)) * n := by rw [mul_comm n 2]
          _ = (2 * 2) * (n * n) := by simp [mul_assoc]
          _ = 4 * (n * n) := by rw [h2m2]
      rw [t1, t2, t3, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg]
      have h4 : -(2 * (m * n)) + -(2 * (m * n)) = -(4 * (m * n)) := by
        rw [← neg_add, ← add_mul, h22]
      calc (m * m + -(2 * (m * n))) + (-(2 * (m * n)) + 4 * (n * n))
          = m * m + ((-(2 * (m * n)) + -(2 * (m * n))) + 4 * (n * n)) := by
              rw [add_assoc (m * m), ← add_assoc (-(2 * (m * n)))]
        _ = m * m + (-(4 * (m * n)) + 4 * (n * n)) := by rw [h4]
    rw [hsq, sub_eq_add_neg, neg_add, neg_add, neg_neg]
    have h3m1 : 3 * (m * m) + -(m * m) = 2 * (m * m) := by
      have h1 : -(m * m) = (-1 : ZHalf) * (m * m) := by rw [neg_mul, one_mul]
      rw [h1, ← add_mul]
      have hc : (3 : ZHalf) + (-1) = 2 := by decide
      rw [hc]
    have hmid : 2 * m * n + 2 * n * m = 4 * (m * n) := by
      rw [mul_assoc 2 n m, mul_comm n m, mul_assoc 2 m n, ← add_mul, h22]
    have hlast : (-4 : ZHalf) * n * n = -(4 * (n * n)) := by rw [neg_mul, neg_mul, mul_assoc]
    calc (2 * m * m + 2 * m * n) + (2 * n * m + (-4) * n * n)
        = (2 * (m * m) + (2 * m * n + 2 * n * m)) + (-4) * n * n := by
            rw [mul_assoc 2 m m, add_mid_group]
      _ = 2 * (m * m) + (4 * (m * n) + -(4 * (n * n))) := by
            rw [hmid, hlast, add_assoc]
      _ = (3 * (m * m) + -(m * m)) + (4 * (m * n) + -(4 * (n * n))) := by rw [h3m1]
      _ = 3 * (m * m) + (-(m * m) + (4 * (m * n) + -(4 * (n * n)))) := add_assoc _ _ _
  rw [hW, add_comm] at h
  have hre : ∀ A B C : ZHalf, A + (-(B) - C) = A - B - C := fun A B C => by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, ← add_assoc]
  rw [neg_mul, hre] at h
  exact h

/-- Non-commutativity witness at `k = 2` (4×4 matrices): `[R_2^{(1)}, A_2] ≠ 0`! -/
theorem adelic_kernels_noncommuting :
    sumFin (fun t : Fin 4 => riesz2AdicKernel 1 0 t.val * monnaArchKernel 2 t.val 2) ≠
    sumFin (fun t : Fin 4 => monnaArchKernel 2 0 t.val * riesz2AdicKernel 1 t.val 2) := by
  decide

/-! ### THEOREM 4: Asymmetric Non-Diagonal Bilinear Bitwise-AND/XOR + Full Adelic Form -/

/-- THEOREM 4A (Asymmetric Non-Diagonal Bilinear + Indefinite Adelic + Indefinite Boundary Form):
    For ALL `k : Nat` and ALL nonzero `x : Fin (2^k) → ZHalf`:
      `Q_k^{asym}(x) + μ_k(x)^2 + 4*μ_k(x)*ν_k(x) - 2*ν_k(x)^2 > 0`. -/
theorem thm_asym_nondiag_indef_strict_pd (k : Nat) (x : Fin (2 ^ k) → ZHalf) (hx : ∃ i, x i ≠ 0) :
    0 < sysAsym.Q k x + quadForm WAsymIndef (sysAsym.L k x) :=
  soundness_strict_pd sysAsym WAsymIndef certAsymIndef checkStrictPD_asym_indef k x hx

/-- THEOREM 4B (Pure Mean-Shifted Corollary for Asymmetric Non-Diagonal Bilinear Adelic Form):
    For ALL `k : Nat` and ALL nonzero `x : Fin (2^k) → ZHalf`:
      `Q_k^{asym}(x) + 3 * μ_k(x)^2 > 0`. -/
theorem thm_asym_nondiag_pure_mean_strict_pd (k : Nat) (x : Fin (2 ^ k) → ZHalf) (hx : ∃ i, x i ≠ 0) :
    0 < sysAsym.Q k x + 3 * (muForm k x * muForm k x) := by
  have h := soundness_strict_pd sysAsym WAsymMean certAsymMean checkStrictPD_asym_mean k x hx
  have hL := monna_L_eq sysAsym rfl rfl rfl k x
  have hW : quadForm WAsymMean (sysAsym.L k x) = 3 * (muForm k x * muForm k x) := by
    rw [quadForm_fin2, hL.1, hL.2]
    change (3 * muForm k x * muForm k x + 0 * muForm k x * nuForm k x) +
           (0 * nuForm k x * muForm k x + 0 * nuForm k x * nuForm k x) = _
    simp only [zero_mul, add_zero, mul_assoc]
  rw [hW] at h
  exact h

theorem asym_nondiag_asymmetric_diag :
    sysAsym.F WAsymIndef 2 (basisFin4 ⟨0, by decide⟩) ≠
    sysAsym.F WAsymIndef 2 (basisFin4 ⟨3, by decide⟩) := by decide

theorem asym_nondiag_not_diag_dom :
    sysAsym.BF WAsymIndef 2 (basisFin4 ⟨0, by decide⟩) (basisFin4 ⟨0, by decide⟩) <
    sysAsym.BF WAsymIndef 2 (basisFin4 ⟨0, by decide⟩) (basisFin4 ⟨1, by decide⟩) +
    sysAsym.BF WAsymIndef 2 (basisFin4 ⟨0, by decide⟩) (basisFin4 ⟨2, by decide⟩) +
    sysAsym.BF WAsymIndef 2 (basisFin4 ⟨0, by decide⟩) (basisFin4 ⟨3, by decide⟩) := by decide

theorem thm_asym_nondiag_sharp_W00 :
    sysAsym.F (mat2 0 2 2 (-2)) 1 (vec2 4 1) < 0 := by decide

/-! ## Section 6: Kernel-Checked Non-Vacuity Witnesses, Hostile Mutation Tests & Axiom Receipts -/

-- Non-vacuity witnesses: concrete nonzero evaluations for all 4 infinite theorems
example : 0 < pow2Nat 2 * (muForm 2 (vec4 1 (-2) 3 (-1)) * muForm 2 (vec4 1 (-2) 3 (-1))) -
              ofInt (Dyadic.pow2Int 3 - 1) * riesz2AdicForm 2 2 (vec4 1 (-2) 3 (-1)) := by decide
example : 0 < dyad 1 1 * (muForm 2 (vec4 1 (-2) 3 (-1)) * muForm 2 (vec4 1 (-2) 3 (-1))) -
              monnaArchForm 2 (vec4 1 (-2) 3 (-1)) := by decide
example : 0 < sysAdelic.Q 2 (vec4 1 (-2) 3 (-1)) + quadForm WAdelic (sysAdelic.L 2 (vec4 1 (-2) 3 (-1))) := by decide
example : 0 < sysAsym.Q 2 (vec4 1 (-2) 3 (-1)) + quadForm WAsymIndef (sysAsym.L 2 (vec4 1 (-2) 3 (-1))) := by decide

-- Concrete `decide` certificates for s = 1, 2, 3 in Theorem 1
example : checkStrictPD (sysRiesz 1) (WRiesz 1) (certRiesz 1) = true := by decide
example : checkStrictPD (sysRiesz 2) (WRiesz 2) (certRiesz 2) = true := by decide
example : checkStrictPD (sysRiesz 3) (WRiesz 3) (certRiesz 3) = true := by decide

-- Theorem 3 sharpness counterexamples (c = 5/2 fails at k = 2; dipole weight 4 fails at k = 1)
theorem thm_adelic_sharp_mean_k2 :
    dyad 5 1 * (muForm 2 (vec4 1 1 1 1) * muForm 2 (vec4 1 1 1 1)) -
    (muForm 2 (vec4 1 1 1 1) - 2 * nuForm 2 (vec4 1 1 1 1)) *
    (muForm 2 (vec4 1 1 1 1) - 2 * nuForm 2 (vec4 1 1 1 1)) -
    3 * riesz2AdicForm 1 2 (vec4 1 1 1 1) - 2 * monnaArchForm 2 (vec4 1 1 1 1) < 0 := by decide

theorem thm_adelic_sharp_dipole_k1 :
    3 * (muForm 1 (vec2 1 0) * muForm 1 (vec2 1 0)) -
    4 * ((muForm 1 (vec2 1 0) - 2 * nuForm 1 (vec2 1 0)) *
         (muForm 1 (vec2 1 0) - 2 * nuForm 1 (vec2 1 0))) -
    3 * riesz2AdicForm 1 1 (vec2 1 0) - 2 * monnaArchForm 1 (vec2 1 0) < 0 := by decide

-- Hostile mutation tests: verify `checkStrictPD` and `checkBoundaryStrictPD` reject corrupted certificates!
example : checkStrictPD sysAsym WAsymIndef { certAsymIndef with h2 := (dyad 5 5, 1, dyad 1 1) } = false := by decide
example : checkStrictPD sysAsym WAsymIndef { certAsymIndef with h1 := (dyad (-1) 3, 1, dyad 1 1) } = false := by decide
example : checkStrictPD sysAsym WAsymIndef { certAsymIndef with deltaTerms := [] } = false := by decide
example : checkStrictPD sysAsym (mat2 2 0 0 0) certAsymMean = false := by decide
example : checkStrictPD sysArch WArchTarget certArch = false := by decide
example : checkBoundaryStrictPD sysArch WArchTarget certArch 0 = false := by decide
example : checkBoundaryStrictPD sysArch WArchTarget { certArch with deltaTerms := [] } (dyad 1 1) = false := by decide

end DyadicPDEngine
