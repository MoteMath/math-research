/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WalshMobiusRunsDihedralSpectra

/-!
# Verified Solutions (`walsh-mobius-runs-dihedral-spectra`)
-/

namespace WalshMobiusRunsDihedralSpectraChallenge

open SpecMat2 in
/-- Theorem 1 (XOR-convolution determinant): the determinant of the 2^k x 2^k XOR-convolution matrix of f equals the product of its Walsh-Hadamard transform values. -/
theorem det_xorConv (k : Nat) (f : Nat → Int) :
    det (xorConvMat k f) = prodFin (2 ^ k) (fun u => wht k f u.val) :=
  SpecMat2.det_xorConv k f

open SpecMat2 in
/-- Theorem 2 (XOR-convolution characteristic polynomial): det(lam I - C_f) equals the product over u of (lam - wht f u). -/
theorem charPoly_xorConv (k : Nat) (f : Nat → Int) (lam : Int) :
    det (matSub (matScale lam (matId (2 ^ k))) (xorConvMat k f)) =
    prodFin (2 ^ k) (fun u => lam - wht k f u.val) :=
  SpecMat2.charPoly_xorConv k f lam

open SpecMat2 in
/-- Theorem 3 (AND-lattice determinant): the determinant of the AND-lattice matrix of g equals the product of its Mobius down-transform values. -/
theorem det_andLattice (k : Nat) (g : Nat → Int) :
    det (andLatticeMat k g) = prodFin (2 ^ k) (fun z => mobiusDown k g z.val) :=
  SpecMat2.det_andLattice k g

open SpecMat2 in
/-- Theorem 4 (Walsh transfer compiler): the Walsh-Hadamard transform of any bit-automaton sequence is again a bit-automaton sequence of the same size, for every width k. -/
theorem wht_transfer_compiler {d : Nat} (A : BitAutomaton d) (k : Nat) :
    ∀ u : Nat, wht k (evalAuto A k) u = evalAuto (whtAuto A) k u :=
  SpecMat2.wht_transfer_compiler A k

open SpecMat2 in
/-- Theorem 5 (Runs-kernel XOR determinant): closed-form product formula with Pell-type factors for the determinant of the XOR-convolution matrix of the runs kernel at every k and parameter q. -/
theorem det_runs_xorConv (q : Int) (k : Nat) :
    det (xorConvMat k (runsKernel q)) =
    prodFin (2 ^ k) (fun u =>
      let v := popcount (invGray u.val)
      let r := Nat.min v (k + 1 - v)
      (1 - q) ^ r * pellQ q (k + 1 - 2 * r)) :=
  SpecMat2.det_runs_xorConv q k

open SpecMat2 in
/-- Theorem 6 (Odd-dimension singularity): the runs-kernel XOR-convolution matrix at q = -1 is singular for every odd exponent 2m + 1. -/
theorem runs_xorConv_neg_one_singular_odd (m : Nat) :
    det (xorConvMat (2 * m + 1) (runsKernel (-1))) = 0 :=
  SpecMat2.runs_xorConv_neg_one_singular_odd m

open SpecMat2 in
/-- Theorem 7 (Unimodular two-runs AND-lattice): the AND-lattice matrix of the runs kernel at q = 2 has determinant exactly -1 for every k >= 2. -/
theorem det_two_runs_andLattice_unimodular (k : Nat) (hk : k ≥ 2) :
    det (andLatticeMat k (runsKernel 2)) = -1 :=
  SpecMat2.det_two_runs_andLattice_unimodular k hk

open SpecMat2 in
/-- Theorem 8 (Never positive definite): for every q and k >= 2, the runs-kernel AND-lattice quadratic form has a nonzero integer vector with nonpositive value. -/
theorem runs_andLattice_never_posdef (q : Int) (k : Nat) (hk : k ≥ 2) :
    ∃ v : Fin (2 ^ k) → Int, (∃ i, v i ≠ 0) ∧ quadForm (andLatticeMat k (runsKernel q)) v ≤ 0 :=
  SpecMat2.runs_andLattice_never_posdef q k hk

end WalshMobiusRunsDihedralSpectraChallenge
