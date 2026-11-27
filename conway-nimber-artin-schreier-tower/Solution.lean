import ConwayNimberArtinSchreierTower

namespace ConwayNimberArtinSchreierTowerChallenge

open ConwaySilicon ConwaySilicon.Nim

theorem mul_inv : ∀ {k : Nat} (x : Nim k), x ≠ zero → mul x (inv x) = one :=
  _root_.ConwaySilicon.Nim.mul_inv

theorem wp_bitLen_contraction : ∀ {k : Nat} (x : Nim k), x ≠ zero → bitLen (wp x) = bitLen x - 1 :=
  _root_.ConwaySilicon.Nim.wp_bitLen_contraction

theorem cosetHarmonic_eq_inv_wpIter (k m : Nat) (hm : m ≤ 2 ^ k) :
    ∀ X : Nim k, 2 ^ m ≤ X.toNat → cosetHarmonic k m X = inv (wpIter m X) :=
  _root_.ConwaySilicon.Nim.cosetHarmonic_eq_inv_wpIter k m hm

theorem powerSum_binary_collapse (k m : Nat) (hm : m ≤ 2 ^ k) :
    ∀ d : Nat, powerSum k m d = zero ∨ powerSum k m d = one :=
  _root_.ConwaySilicon.Nim.powerSum_binary_collapse k m hm

theorem finite_table_evaluates_all_m (k m r n : Nat) (hr : r < 2 ^ k) (hbound : m + r < 2 ^ n) :
    (dyadicProd n m (pow2 n (m + r))).toNat =
      (wpIter (m % 2 ^ k) (pow2 (k + 1) (m % 2 ^ k + r))).toNat :=
  _root_.ConwaySilicon.Nim.finite_table_evaluates_all_m k m r n hr hbound

theorem dyadicProd_fourth_shell_period4 (n m : Nat) (h : m + 3 < 2 ^ n) :
    (dyadicProd n m (pow2 n (m + 3))).toNat =
      match m % 4 with
      | 0 => 8
      | 1 => 8
      | 2 => 10
      | _ => 11 :=
  _root_.ConwaySilicon.Nim.dyadicProd_fourth_shell_period4 n m h

theorem sharpness_period_fails_at_k1_r2 :
    wpIter (0 + 2 ^ 1) (pow2 3 (0 + 2 ^ 1 + 2)) ≠ wpIter 0 (pow2 3 (0 + 2)) :=
  _root_.ConwaySilicon.Nim.sharpness_period_fails_at_k1_r2

theorem sharpness_popcount_boundary_nonzero (k m : Nat) (hm : m ≤ 2 ^ k) :
    popcount (2 ^ m - 1) = m ∧ powerSum k m (2 ^ m - 1) ≠ zero :=
  _root_.ConwaySilicon.Nim.sharpness_popcount_boundary_nonzero k m hm

end ConwayNimberArtinSchreierTowerChallenge
