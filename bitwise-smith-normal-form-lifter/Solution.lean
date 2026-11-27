/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitwiseSmithNormalFormLifter

/-!
# Verified Solutions (`bitwise-smith-normal-form-lifter`)
-/

namespace BitwiseSmithNormalFormLifterChallenge

open SiliconSNF in
/-- Theorem 1 (Torsion obstruction): if M has Smith normal form d and some invariant d i exceeds 1, there is a right-hand side b not hit by M while d i times b is hit. -/
theorem hasSNF_torsion_obstruction {n : Nat} {M : Mat n} {d : Fin n → Nat}
    (h : HasSNF M d) (i : Fin n) (hi : d i > 1) :
    ∃ b : Fin n → Int, (∀ x, matVec M x ≠ b) ∧ (∃ x, matVec M x = fun j => (d i : Int) * b j) :=
  SiliconSNF.HasSNF.torsion_obstruction h i hi

open SiliconSNF in
/-- Theorem 2 (Kummer carry identity): for x, y < 2^k and carry-in c <= 1, carries + popcount(x + y + c) = popcount x + popcount y + c. -/
theorem carriesK_kummer (k : Nat) :
    ∀ x y c : Nat, x < 2 ^ k → y < 2 ^ k → c ≤ 1 →
      carriesK k x y c + popcount (x + y + c) = popcount x + popcount y + c :=
  SiliconSNF.carriesK_kummer k

open SiliconSNF in
/-- Theorem 3 (Affine carry-parity SNF): for every k >= 1 and integers a, b, the affine carry-parity matrix has the explicit Smith normal form affineCarrySNFDiag. -/
theorem snf_affine_carry_parity (k : Nat) (hk : 1 ≤ k) (a b : Int) :
    HasSNF (affineCarryParMat k a b) (affineCarrySNFDiag k a b) :=
  SiliconSNF.snf_affine_carry_parity k hk a b

open SiliconSNF in
/-- Theorem 4 (Flat carry-sign SNF): for k >= 1 the (-1)^carries matrix has Smith normal form (1, 2, 2, ..., 2) on 2^k indices. -/
theorem snf_carry_sign_flat (k : Nat) (hk : 1 ≤ k) :
    HasSNF (carrySignMat k) (fun i : Fin (2 ^ k) => if i.1 = 0 then 1 else 2) :=
  SiliconSNF.snf_carry_sign_flat k hk

open SiliconSNF in
/-- Theorem 5 (Odd/even dichotomy): the carry-parity matrix at parameter 1 is unimodular for odd k and has a single zero invariant for even k. -/
theorem snf_carry_parity_one_dichotomy (k : Nat) :
    HasSNF (carryParMat k 1)
      (fun i : Fin (2 ^ k) => if k % 2 = 1 then 1 else if i.1 + 1 = 2 ^ k then 0 else 1) :=
  SiliconSNF.snf_carry_parity_one_dichotomy k

open SiliconSNF in
/-- Theorem 6 (Add-XOR collapse): the add-XOR matrix DMat k has Smith normal form given by addXorSNFDiag for every k. -/
theorem snf_DMat (k : Nat) : HasSNF (DMat k) (fun i : Fin (2 ^ k) => addXorSNFDiag i.1) :=
  SiliconSNF.snf_DMat k

open SiliconSNF in
/-- Theorem 7 (Bitwise-AND SNF): the 2^k x 2^k matrix x AND y has Smith normal form with invariants 2^i for i < k and 0 otherwise. -/
theorem snf_bitwise_and (k : Nat) :
    HasSNF (fun x y : Fin (2 ^ k) => ((x.1 &&& y.1 : Nat) : Int))
           (fun i : Fin (2 ^ k) => if i.1 < k then 2 ^ i.1 else 0) :=
  SiliconSNF.snf_bitwise_and k

open SiliconSNF in
/-- Theorem 8 (Unimodular popcount-AND): the matrix 2^popcount(x AND y) is unimodular (all invariants 1) for every k. -/
theorem snf_two_pow_popcount_and_unimod (k : Nat) :
    HasSNF (qPopAndMat k 2) (fun _ : Fin (2 ^ k) => 1) :=
  SiliconSNF.snf_two_pow_popcount_and_unimod k

end BitwiseSmithNormalFormLifterChallenge
