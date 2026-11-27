/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SiliconCircuitBisimCompiler

/-!
# Verified Solutions (`silicon-circuit-bisim-compiler`)
-/

namespace SiliconCircuitBisimCompilerChallenge

open SiliconBisim

theorem slice_bisim_sound (G1 G2 : SliceGen)
    (hIn : G1.inW = G2.inW) (hOut : G1.outW = G2.outW) (hFin : G1.finW = G2.finW)
    (cert : SliceBisimCert G1.stW G2.stW)
    (hCert : checkSliceBisim G1 G2 hIn hOut hFin cert = true) :
    ∀ (xs : List (BitVec G1.inW)),
      let (ys1, f1) := evalSliceGen G1 xs
      let (ys2, f2) := evalSliceGen G2 (xs.map (fun x => hIn ▸ x))
      ys1 = ys2.map (fun y => hOut ▸ y) ∧ f1 = (hFin ▸ f2) :=
  SiliconBisim.slice_bisim_sound G1 G2 hIn hOut hFin cert hCert

theorem prefix_all_topologies_sound (P : PrefixSpec) (G : SliceGen)
    (hIn : P.inW = G.inW) (hSt : P.stW = G.stW) (hOut : P.outW = G.outW)
    (cert : PrefixToSliceCert P.tokW)
    (hCert : checkPrefixToSliceCert P G hIn hSt hOut cert = true) :
    ∀ (k : Nat) (c0 : BitVec P.stW) (xs : Fin (2 ^ k) → BitVec P.inW),
      -- 1. All 4 hardware topologies produce identical outputs and carry-out!
      evalPrefixCircuit P sklanskyPrefix k c0 xs = evalPrefixCircuit P serialPrefix k c0 xs ∧
      evalPrefixCircuit P brentKungPrefix k c0 xs = evalPrefixCircuit P serialPrefix k c0 xs ∧
      evalPrefixCircuit P koggeStonePrefix k c0 xs = evalPrefixCircuit P serialPrefix k c0 xs ∧
      -- 2. And they ALL match the serial bit-slice generator `G` bit-for-bit!
      (let (outFn, cOut) := evalPrefixCircuit P serialPrefix k c0 xs
       let (ysG, fG) := evalSliceFrom G (hSt ▸ c0) (finToList (fun i => hIn ▸ xs i))
       finToList (fun i => hOut ▸ outFn i) = ysG ∧ G.final (hSt ▸ cOut) = fG) :=
  SiliconBisim.prefix_all_topologies_sound P G hIn hSt hOut cert hCert

theorem four_way_prefix_adder_equiv :
    ∀ (k : Nat) (c0 : BitVec 1) (xs : Fin (2 ^ k) → BitVec 2),
      evalPrefixCircuit prefixAdderGlitchedXorSpec sklanskyPrefix k c0 xs =
      evalPrefixCircuit prefixAdderOrPropSpec brentKungPrefix k c0 xs ∧
      evalPrefixCircuit prefixAdderOrPropSpec brentKungPrefix k c0 xs =
      evalPrefixCircuit prefixAdderActiveLowSpec koggeStonePrefix k c0 xs ∧
      evalPrefixCircuit prefixAdderActiveLowSpec koggeStonePrefix k c0 xs =
      evalPrefixCircuit prefixAdderXorBlackSpec sklanskyPrefix k c0 xs :=
  SiliconBisim.four_way_prefix_adder_equiv

theorem parallel_gray_decoder_equiv :
    ∀ (k : Nat) (c0 : BitVec 1) (xs : Fin (2 ^ k) → BitVec 1),
      evalPrefixCircuit grayDecodePrefixSpec sklanskyPrefix k c0 xs =
      evalPrefixCircuit grayDecodePrefixSpec serialPrefix k c0 xs ∧
      evalPrefixCircuit grayDecodePrefixSpec brentKungPrefix k c0 xs =
      evalPrefixCircuit grayDecodePrefixSpec serialPrefix k c0 xs ∧
      evalPrefixCircuit grayDecodePrefixSpec koggeStonePrefix k c0 xs =
      evalPrefixCircuit grayDecodePrefixSpec serialPrefix k c0 xs :=
  SiliconBisim.parallel_gray_decoder_equiv

theorem three_way_shifter_equiv :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      recTreeRot nandOnlyMuxCell k ctrls xs = barrelRot xorAndMuxCell (finToList ctrls) xs ∧
      recTreeRot nandOnlyMuxCell k ctrls xs = iterRot (listToNat (finToList ctrls)) xs :=
  SiliconBisim.three_way_shifter_equiv

theorem reed_muller_anf_butterfly_all_k :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      omegaNet anfCell k ctrls xs = fwdButterfly anfCell k ctrls xs ∧
      fwdButterfly anfCell k ctrls xs = bwdButterfly anfCell k ctrls xs ∧
      fwdButterfly anfCell k ctrls (fwdButterfly anfCell k ctrls xs) = xs :=
  SiliconBisim.reed_muller_anf_butterfly_all_k

theorem gf4_butterfly_inverse_all_k :
    ∀ (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool),
      fwdButterfly gf4InvCell k ctrls (fwdButterfly gf4FwdCell k ctrls xs) = xs ∧
      omegaNet gf4FwdCell k ctrls xs = bwdButterfly gf4FwdCell k ctrls xs :=
  SiliconBisim.gf4_butterfly_inverse_all_k

theorem bitonic_andOr_eq_oddEven_nand_all_k :
    ∀ (k : Nat) (xs : Fin (2 ^ k) → Bool),
      bitonicSort andOrCmpCell k xs = oddEvenSort nandOnlyCmpCell k xs ∧
      bitonicSort andOrCmpCell k xs = thresholdSort xs :=
  SiliconBisim.bitonic_andOr_eq_oddEven_nand_all_k

end SiliconCircuitBisimCompilerChallenge
