import LucasMaskWalshBinomFractals

namespace LucasMaskWalshBinomFractalsChallenge

open LucasMaskEngine

theorem delta_two_state_div (N : Nat) :
    (∀ j c : Nat, Submask j N → 2 * c ≤ N →
      (2 : Int) ^ (popcount j - c) ∣ Delta (N - 2 * c) j (c : Int)) ∧
    (∀ j c : Nat, Submask j N → 1 ≤ c → 2 * c ≤ N + 1 →
      (2 : Int) ^ (popcount j - c) ∣ Delta (N + 1 - 2 * c) j (c : Int)) :=
  _root_.LucasMaskEngine.delta_two_state_div N

theorem bitUnit_sq_lift {n s : Nat} {g : Nat → Int} (hs : 1 ≤ s)
    (hg : BitUnit n s g) :
    BitUnit n (s + 1) (fun k => g k * g k) :=
  _root_.LucasMaskEngine.bitUnit_sq_lift hs hg

theorem bitSmooth_pow_odd {n E r : Nat} {f : Nat → Int}
    (hf0 : f 0 = 1) (hf : BitSmooth n E f) (hr : r % 2 = 1) :
    BitSmooth n E (fun k => (f k) ^ r) :=
  _root_.LucasMaskEngine.bitSmooth_pow_odd hf0 hf hr

theorem walsh_bitSmooth_spike {n E m : Nat} {f : Nat → Int}
    (hm : Submask m n) (hf : BitSmooth n E f) :
    (2 : Int) ^ (popcount n + 1) ∣
      (walsh n m f - (2 : Int) ^ (popcount n) * boolToInt (m == E)) :=
  _root_.LucasMaskEngine.walsh_bitSmooth_spike hm hf

theorem walsh_lucas_binom_odd_pow (n r m : Nat) (hr : r % 2 = 1) (hm : Submask m n) :
    (2 : Int) ^ (popcount n + 1) ∣
      (walsh n m (fun k => (binomZ n (k : Int)) ^ r) -
        (2 : Int) ^ (popcount n) * boolToInt (m == endpointMask n)) :=
  _root_.LucasMaskEngine.walsh_lucas_binom_odd_pow n r m hr hm

theorem walsh_lucas_binom_even_pow (n r m : Nat) (hrpos : r ≠ 0) (hreven : r % 2 = 0)
    (hm : Submask m n) :
    (2 : Int) ^ (popcount n + (v2Nat r + 1)) ∣
      (walsh n m (fun k => (binomZ n (k : Int)) ^ r) -
        (2 : Int) ^ (popcount n) * boolToInt (m == 0)) :=
  _root_.LucasMaskEngine.walsh_lucas_binom_even_pow n r m hrpos hreven hm

theorem walsh_lucas_mixed_product (n n1 n2 r1 r2 m : Nat)
    (h1 : Submask n n1) (h2 : Submask n n2)
    (hr1 : r1 % 2 = 1) (hr2 : r2 % 2 = 1) (hm : Submask m n) :
    (2 : Int) ^ (popcount n + 1) ∣
      (walsh n m (fun k => (binomZ n1 (k : Int)) ^ r1 * (binomZ n2 (k : Int)) ^ r2) -
        (2 : Int) ^ (popcount n) * boolToInt (m == ((endpointMask n1 ^^^ endpointMask n2) &&& n))) :=
  _root_.LucasMaskEngine.walsh_lucas_mixed_product n n1 n2 r1 r2 m h1 h2 hr1 hr2 hm

theorem sharpness_squaring_jump_needs_spike_mask :
    f_ce 0 = 1 ∧
    BitExcess 3 0 f_ce ∧
    mobius (fun k => f_ce k * f_ce k) 3 = 40 ∧
    ¬ ((2 : Int) ^ (popcount 3 + 2) ∣ mobius (fun k => f_ce k * f_ce k) 3) :=
  _root_.LucasMaskEngine.sharpness_squaring_jump_needs_spike_mask

end LucasMaskWalshBinomFractalsChallenge
