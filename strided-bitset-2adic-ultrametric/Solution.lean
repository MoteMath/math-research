import StridedBitset2adicUltrametric

namespace StridedBitset2adicUltrametricChallenge

open StridedBitsetEngine

theorem maskRepCount_slice (m : Nat) (hm : m ≥ 1) :
    ∀ (masks : List Nat) (q r : Nat), r < 2 ^ m →
      maskRepCount m masks (2 ^ m * q + r) =
      sumRange (fun c =>
        digitWeight m masks (c * 2 ^ m + r) * maskRepCount m masks (q - c)) (q + 1) :=
  _root_.StridedBitsetEngine.maskRepCount_slice m hm

theorem ultrametric_odd_parity_lift
    (B : Nat) (hB : B ≥ 2)
    (w : Nat → Nat → Nat)
    (f V : Nat → Nat)
    (hf0 : f 0 = 1) (hV0 : V 0 = 0)
    (hrec : ∀ q r : Nat, r < B →
      f (B * q + r) = sumRange (fun c => w c r * f (q - c)) (q + 1))
    (hge : ∀ q r : Nat, r < B → B * q + r > 0 →
      ∀ c ≤ q, w c r > 0 → V (B * q + r) ≤ v2 (w c r) + V (q - c))
    (hodd : ∀ q r : Nat, r < B → B * q + r > 0 →
      (sumRange (fun c =>
        if w c r > 0 ∧ v2 (w c r) + V (q - c) = V (B * q + r) then 1 else 0) (q + 1)) % 2 = 1) :
    ∀ n : Nat, f n > 0 ∧ v2 (f n) = V n :=
  _root_.StridedBitsetEngine.ultrametric_odd_parity_lift B hB w f V hf0 hV0 hrec hge hodd

theorem nonbinomial_3S2_add_N_v2 :
    ∀ n : Nat,
      maskRepCount 2 [1, 1, 1, 3] n > 0 ∧
      v2 (maskRepCount 2 [1, 1, 1, 3] n) =
        certVal 4 (fun r => digitWeight 2 [1, 1, 1, 3] r)
                  (fun r => digitWeight 2 [1, 1, 1, 3] (4 + r)) n :=
  _root_.StridedBitsetEngine.nonbinomial_3S2_add_N_v2

theorem even_window_strided_v2 {m t : Nat} (hm : m ≥ 1) (ht : 2 * t < 2 ^ m) :
    ∀ n : Nat,
      stridedRepCount m (2 ^ m + 2 * t) n > 0 ∧
      v2 (stridedRepCount m (2 ^ m + 2 * t) n) = evenWindowVal m t n :=
  _root_.StridedBitsetEngine.even_window_strided_v2 hm ht

theorem upper_endpoint_v2_collapse {m : Nat} (hm : m ≥ 1) :
    ∀ n : Nat, v2 (stridedRepCount m (2 ^ (m + 1) - 2) n) = v2 (n + 1) :=
  _root_.StridedBitsetEngine.upper_endpoint_v2_collapse hm

theorem pow2_strided_r_invariance {m r1 r2 : Nat} (hm : m ≥ 1) (hr1 : r1 ≥ m) (hr2 : r2 ≥ m) (a : Nat) :
    v2 (stridedRepCount m (2 ^ r1) (2 ^ r1 * a)) = v2 (stridedRepCount m (2 ^ r2) (2 ^ r2 * a)) :=
  _root_.StridedBitsetEngine.pow2_strided_r_invariance hm hr1 hr2 a

theorem witness_three_way_tie_survives :
    choose 8 0 * stridedRepCount 2 8 3 = 56 ∧
    choose 8 4 * stridedRepCount 2 8 2 = 1960 ∧
    choose 8 8 * stridedRepCount 2 8 1 = 8 ∧
    v2Exec 56 = 3 ∧ v2Exec 1960 = 3 ∧ v2Exec 8 = 3 ∧
    stridedRepCount 2 8 12 = 2024 ∧ v2Exec 2024 = 3 :=
  _root_.StridedBitsetEngine.witness_three_way_tie_survives

theorem sharpness_above_window_cancellation :
    choose 10 0 * stridedRepCount 2 10 1 = 10 ∧
    choose 10 4 * stridedRepCount 2 10 0 = 210 ∧
    v2Exec 10 = 1 ∧ v2Exec 210 = 1 ∧
    stridedRepCount 2 10 4 = 220 ∧ v2Exec 220 = 2 :=
  _root_.StridedBitsetEngine.sharpness_above_window_cancellation

end StridedBitset2adicUltrametricChallenge
