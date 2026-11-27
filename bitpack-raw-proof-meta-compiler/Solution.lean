import BitpackRawProofMetaCompiler

namespace BitpackRawProofMetaCompilerChallenge

open BitPackMC

theorem checkCert_sound (c : DecodedCert) (h : checkCert c = true) : c.goal.denote :=
  _root_.BitPackMC.checkCert_sound c h

theorem soundness_verifyRawCert (raw : ByteArray) (h : verifyRawCert raw = true) :
    ∃ c, decodeRawCert raw = some c ∧ c.goal.denote :=
  _root_.BitPackMC.soundness_verifyRawCert raw h

theorem gray_3x_uncertainty (x : Nat) :
    2 * popcount x ≤ 2 * popcount (3 * x) + popcount (x ^^^ (x >>> 1)) :=
  _root_.BitPackMC.gray_3x_uncertainty x

theorem pop_5x_9x_lower (x : Nat) :
    2 * popcount x ≤ 3 * (popcount (5 * x) + popcount (9 * x)) :=
  _root_.BitPackMC.pop_5x_9x_lower x

theorem pop_3x_or_11x_sharp (x : Nat) :
    2 * popcount x ≤ 3 * popcount ((3 * x) ||| (11 * x)) :=
  _root_.BitPackMC.pop_3x_or_11x_sharp x

theorem pop_2var_3x_plus_y_xor (x y : Nat) :
    popcount x + popcount y ≤ 3 * (popcount (3 * x + y) + popcount (x ^^^ y)) :=
  _root_.BitPackMC.pop_2var_3x_plus_y_xor x y

theorem pop_eq_3x_plus_y_cascade (x y : Nat) :
    popcount (3 * x + y) +
    popcount ((3 * x + y) ^^^ ((3 * x) ^^^ y)) +
    popcount ((3 * x) ^^^ (x ^^^ (2 * x))) =
    2 * popcount x + popcount y :=
  _root_.BitPackMC.pop_eq_3x_plus_y_cascade x y

theorem bit_eq_3x_plus_y_collapse (x y : Nat) :
    (3 * x + y) + ((3 * x) ^^^ y) = 2 * ((3 * x) ||| y) :=
  _root_.BitPackMC.bit_eq_3x_plus_y_collapse x y

end BitpackRawProofMetaCompilerChallenge
